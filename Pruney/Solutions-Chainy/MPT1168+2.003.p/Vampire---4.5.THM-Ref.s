%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:13 EST 2020

% Result     : Theorem 1.85s
% Output     : Refutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 498 expanded)
%              Number of leaves         :   36 ( 253 expanded)
%              Depth                    :    9
%              Number of atoms          :  806 (3417 expanded)
%              Number of equality atoms :   21 ( 263 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1307,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f157,f177,f208,f209,f211,f224,f226,f258,f271,f311,f315,f343,f357,f365,f452,f457,f461,f566,f657,f1078,f1103,f1168,f1205,f1207,f1283,f1296,f1306])).

fof(f1306,plain,
    ( spl7_103
    | ~ spl7_25
    | ~ spl7_49 ),
    inference(avatar_split_clause,[],[f1211,f454,f268,f1051])).

fof(f1051,plain,
    ( spl7_103
  <=> r2_hidden(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_103])])).

fof(f268,plain,
    ( spl7_25
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f454,plain,
    ( spl7_49
  <=> r2_hidden(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).

fof(f1211,plain,
    ( r2_hidden(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),sK3)
    | ~ spl7_25
    | ~ spl7_49 ),
    inference(resolution,[],[f456,f359])).

fof(f359,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | r2_hidden(X0,sK3) )
    | ~ spl7_25 ),
    inference(resolution,[],[f270,f65])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f41,f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
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

fof(f270,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f268])).

fof(f456,plain,
    ( r2_hidden(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),sK2)
    | ~ spl7_49 ),
    inference(avatar_component_clause,[],[f454])).

fof(f1296,plain,
    ( spl7_14
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_46
    | ~ spl7_47
    | ~ spl7_24
    | ~ spl7_48
    | ~ spl7_103
    | spl7_13 ),
    inference(avatar_split_clause,[],[f463,f205,f1051,f449,f264,f445,f441,f97,f93,f89,f85,f213])).

fof(f213,plain,
    ( spl7_14
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f85,plain,
    ( spl7_1
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f89,plain,
    ( spl7_2
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f93,plain,
    ( spl7_3
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f97,plain,
    ( spl7_4
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f441,plain,
    ( spl7_46
  <=> m1_subset_1(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f445,plain,
    ( spl7_47
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f264,plain,
    ( spl7_24
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f449,plain,
    ( spl7_48
  <=> r2_orders_2(sK0,sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f205,plain,
    ( spl7_13
  <=> r2_hidden(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),k3_orders_2(sK0,sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f463,plain,
    ( ~ r2_hidden(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),sK3)
    | ~ r2_orders_2(sK0,sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl7_13 ),
    inference(resolution,[],[f206,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
      | ~ r2_hidden(X1,X3)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).

fof(f206,plain,
    ( ~ r2_hidden(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),k3_orders_2(sK0,sK3,sK1))
    | spl7_13 ),
    inference(avatar_component_clause,[],[f205])).

fof(f1283,plain,
    ( spl7_46
    | ~ spl7_13
    | ~ spl7_43 ),
    inference(avatar_split_clause,[],[f1277,f341,f205,f441])).

fof(f341,plain,
    ( spl7_43
  <=> ! [X14] :
        ( m1_subset_1(k3_orders_2(sK0,sK3,X14),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X14,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).

fof(f1277,plain,
    ( m1_subset_1(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),u1_struct_0(sK0))
    | ~ spl7_13
    | ~ spl7_43 ),
    inference(resolution,[],[f1097,f408])).

fof(f408,plain,
    ( m1_subset_1(k3_orders_2(sK0,sK3,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_43 ),
    inference(resolution,[],[f342,f50])).

fof(f50,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( k3_orders_2(sK0,sK2,sK1) != k3_orders_2(sK0,sK3,sK1)
    & m1_orders_2(sK2,sK0,sK3)
    & r2_hidden(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f33,f32,f31,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( k3_orders_2(X0,X2,X1) != k3_orders_2(X0,X3,X1)
                    & m1_orders_2(X2,X0,X3)
                    & r2_hidden(X1,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k3_orders_2(sK0,X2,X1) != k3_orders_2(sK0,X3,X1)
                  & m1_orders_2(X2,sK0,X3)
                  & r2_hidden(X1,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( k3_orders_2(sK0,X2,X1) != k3_orders_2(sK0,X3,X1)
                & m1_orders_2(X2,sK0,X3)
                & r2_hidden(X1,X2)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( k3_orders_2(sK0,X2,sK1) != k3_orders_2(sK0,X3,sK1)
              & m1_orders_2(X2,sK0,X3)
              & r2_hidden(sK1,X2)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( k3_orders_2(sK0,X2,sK1) != k3_orders_2(sK0,X3,sK1)
            & m1_orders_2(X2,sK0,X3)
            & r2_hidden(sK1,X2)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X3] :
          ( k3_orders_2(sK0,X3,sK1) != k3_orders_2(sK0,sK2,sK1)
          & m1_orders_2(sK2,sK0,X3)
          & r2_hidden(sK1,sK2)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X3] :
        ( k3_orders_2(sK0,X3,sK1) != k3_orders_2(sK0,sK2,sK1)
        & m1_orders_2(sK2,sK0,X3)
        & r2_hidden(sK1,sK2)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( k3_orders_2(sK0,sK2,sK1) != k3_orders_2(sK0,sK3,sK1)
      & m1_orders_2(sK2,sK0,sK3)
      & r2_hidden(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k3_orders_2(X0,X2,X1) != k3_orders_2(X0,X3,X1)
                  & m1_orders_2(X2,X0,X3)
                  & r2_hidden(X1,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k3_orders_2(X0,X2,X1) != k3_orders_2(X0,X3,X1)
                  & m1_orders_2(X2,X0,X3)
                  & r2_hidden(X1,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
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
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( ( m1_orders_2(X2,X0,X3)
                        & r2_hidden(X1,X2) )
                     => k3_orders_2(X0,X2,X1) = k3_orders_2(X0,X3,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( m1_orders_2(X2,X0,X3)
                      & r2_hidden(X1,X2) )
                   => k3_orders_2(X0,X2,X1) = k3_orders_2(X0,X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_orders_2)).

fof(f342,plain,
    ( ! [X14] :
        ( ~ m1_subset_1(X14,u1_struct_0(sK0))
        | m1_subset_1(k3_orders_2(sK0,sK3,X14),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_43 ),
    inference(avatar_component_clause,[],[f341])).

fof(f1097,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k3_orders_2(sK0,sK3,sK1),k1_zfmisc_1(X0))
        | m1_subset_1(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),X0) )
    | ~ spl7_13 ),
    inference(resolution,[],[f207,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f207,plain,
    ( r2_hidden(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),k3_orders_2(sK0,sK3,sK1))
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f205])).

fof(f1207,plain,
    ( ~ spl7_13
    | ~ spl7_47
    | ~ spl7_46
    | ~ spl7_36
    | spl7_48 ),
    inference(avatar_split_clause,[],[f889,f449,f313,f441,f445,f205])).

fof(f313,plain,
    ( spl7_36
  <=> ! [X1,X0] :
        ( r2_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k3_orders_2(sK0,sK3,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f889,plain,
    ( ~ m1_subset_1(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r2_hidden(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),k3_orders_2(sK0,sK3,sK1))
    | ~ spl7_36
    | spl7_48 ),
    inference(resolution,[],[f450,f314])).

fof(f314,plain,
    ( ! [X0,X1] :
        ( r2_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k3_orders_2(sK0,sK3,X1)) )
    | ~ spl7_36 ),
    inference(avatar_component_clause,[],[f313])).

fof(f450,plain,
    ( ~ r2_orders_2(sK0,sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),sK1)
    | spl7_48 ),
    inference(avatar_component_clause,[],[f449])).

fof(f1205,plain,
    ( spl7_14
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_46
    | ~ spl7_47
    | ~ spl7_26
    | ~ spl7_48
    | ~ spl7_49
    | spl7_12 ),
    inference(avatar_split_clause,[],[f1090,f201,f454,f449,f273,f445,f441,f97,f93,f89,f85,f213])).

fof(f273,plain,
    ( spl7_26
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f201,plain,
    ( spl7_12
  <=> r2_hidden(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),k3_orders_2(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f1090,plain,
    ( ~ r2_hidden(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),sK2)
    | ~ r2_orders_2(sK0,sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl7_12 ),
    inference(resolution,[],[f202,f58])).

fof(f202,plain,
    ( ~ r2_hidden(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),k3_orders_2(sK0,sK2,sK1))
    | spl7_12 ),
    inference(avatar_component_clause,[],[f201])).

fof(f1168,plain,
    ( ~ spl7_48
    | ~ spl7_103
    | spl7_49
    | ~ spl7_46
    | ~ spl7_69 ),
    inference(avatar_split_clause,[],[f1128,f655,f441,f454,f1051,f449])).

fof(f655,plain,
    ( spl7_69
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK3)
        | ~ r2_orders_2(sK0,X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_69])])).

fof(f1128,plain,
    ( r2_hidden(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),sK2)
    | ~ r2_hidden(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),sK3)
    | ~ r2_orders_2(sK0,sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),sK1)
    | ~ spl7_46
    | ~ spl7_69 ),
    inference(resolution,[],[f442,f656])).

fof(f656,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK3)
        | ~ r2_orders_2(sK0,X0,sK1) )
    | ~ spl7_69 ),
    inference(avatar_component_clause,[],[f655])).

fof(f442,plain,
    ( m1_subset_1(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),u1_struct_0(sK0))
    | ~ spl7_46 ),
    inference(avatar_component_clause,[],[f441])).

fof(f1103,plain,
    ( spl7_14
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_46
    | ~ spl7_47
    | ~ spl7_24
    | spl7_103
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f1096,f205,f1051,f264,f445,f441,f97,f93,f89,f85,f213])).

fof(f1096,plain,
    ( r2_hidden(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_13 ),
    inference(resolution,[],[f207,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1078,plain,
    ( spl7_46
    | ~ spl7_12
    | ~ spl7_35 ),
    inference(avatar_split_clause,[],[f1072,f309,f201,f441])).

fof(f309,plain,
    ( spl7_35
  <=> ! [X14] :
        ( m1_subset_1(k3_orders_2(sK0,sK2,X14),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X14,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f1072,plain,
    ( m1_subset_1(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),u1_struct_0(sK0))
    | ~ spl7_12
    | ~ spl7_35 ),
    inference(resolution,[],[f434,f405])).

fof(f405,plain,
    ( m1_subset_1(k3_orders_2(sK0,sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_35 ),
    inference(resolution,[],[f310,f50])).

fof(f310,plain,
    ( ! [X14] :
        ( ~ m1_subset_1(X14,u1_struct_0(sK0))
        | m1_subset_1(k3_orders_2(sK0,sK2,X14),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f309])).

fof(f434,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k3_orders_2(sK0,sK2,sK1),k1_zfmisc_1(X0))
        | m1_subset_1(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),X0) )
    | ~ spl7_12 ),
    inference(resolution,[],[f203,f71])).

fof(f203,plain,
    ( r2_hidden(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),k3_orders_2(sK0,sK2,sK1))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f201])).

fof(f657,plain,
    ( ~ spl7_58
    | ~ spl7_26
    | ~ spl7_24
    | spl7_69
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f653,f256,f655,f264,f273,f555])).

fof(f555,plain,
    ( spl7_58
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_58])])).

fof(f256,plain,
    ( spl7_22
  <=> ! [X16,X15,X17] :
        ( r2_hidden(X15,X16)
        | ~ m1_subset_1(X15,u1_struct_0(sK0))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_orders_2(sK0,X15,sK1)
        | ~ r2_hidden(X15,X17)
        | ~ r2_hidden(sK1,X16)
        | ~ m1_orders_2(X16,sK0,X17) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f653,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_orders_2(sK0,X0,sK1)
        | ~ r2_hidden(X0,sK3)
        | ~ r2_hidden(sK1,sK2)
        | r2_hidden(X0,sK2) )
    | ~ spl7_22 ),
    inference(resolution,[],[f257,f54])).

fof(f54,plain,(
    m1_orders_2(sK2,sK0,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f257,plain,
    ( ! [X17,X15,X16] :
        ( ~ m1_orders_2(X16,sK0,X17)
        | ~ m1_subset_1(X15,u1_struct_0(sK0))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_orders_2(sK0,X15,sK1)
        | ~ r2_hidden(X15,X17)
        | ~ r2_hidden(sK1,X16)
        | r2_hidden(X15,X16) )
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f256])).

fof(f566,plain,(
    spl7_58 ),
    inference(avatar_contradiction_clause,[],[f562])).

fof(f562,plain,
    ( $false
    | spl7_58 ),
    inference(resolution,[],[f557,f53])).

fof(f53,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f557,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl7_58 ),
    inference(avatar_component_clause,[],[f555])).

fof(f461,plain,(
    spl7_47 ),
    inference(avatar_contradiction_clause,[],[f458])).

fof(f458,plain,
    ( $false
    | spl7_47 ),
    inference(resolution,[],[f447,f50])).

fof(f447,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl7_47 ),
    inference(avatar_component_clause,[],[f445])).

fof(f457,plain,
    ( spl7_14
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_46
    | ~ spl7_47
    | ~ spl7_26
    | spl7_49
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f433,f201,f454,f273,f445,f441,f97,f93,f89,f85,f213])).

fof(f433,plain,
    ( r2_hidden(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_12 ),
    inference(resolution,[],[f203,f57])).

fof(f452,plain,
    ( spl7_14
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_46
    | ~ spl7_47
    | ~ spl7_26
    | spl7_48
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f432,f201,f449,f273,f445,f441,f97,f93,f89,f85,f213])).

fof(f432,plain,
    ( r2_orders_2(sK0,sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_12 ),
    inference(resolution,[],[f203,f56])).

fof(f56,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f365,plain,(
    spl7_26 ),
    inference(avatar_contradiction_clause,[],[f360])).

fof(f360,plain,
    ( $false
    | spl7_26 ),
    inference(resolution,[],[f275,f51])).

fof(f51,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f275,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_26 ),
    inference(avatar_component_clause,[],[f273])).

fof(f357,plain,(
    spl7_24 ),
    inference(avatar_contradiction_clause,[],[f352])).

fof(f352,plain,
    ( $false
    | spl7_24 ),
    inference(resolution,[],[f266,f52])).

fof(f52,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f266,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_24 ),
    inference(avatar_component_clause,[],[f264])).

fof(f343,plain,
    ( spl7_14
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_43 ),
    inference(avatar_split_clause,[],[f195,f341,f97,f93,f89,f85,f213])).

fof(f195,plain,(
    ! [X14] :
      ( m1_subset_1(k3_orders_2(sK0,sK3,X14),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X14,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f52,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_orders_2)).

fof(f315,plain,
    ( spl7_14
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_36 ),
    inference(avatar_split_clause,[],[f188,f313,f97,f93,f89,f85,f213])).

fof(f188,plain,(
    ! [X0,X1] :
      ( r2_orders_2(sK0,X0,X1)
      | ~ r2_hidden(X0,k3_orders_2(sK0,sK3,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f52,f56])).

fof(f311,plain,
    ( spl7_14
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_35 ),
    inference(avatar_split_clause,[],[f185,f309,f97,f93,f89,f85,f213])).

fof(f185,plain,(
    ! [X14] :
      ( m1_subset_1(k3_orders_2(sK0,sK2,X14),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X14,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f51,f70])).

fof(f271,plain,
    ( spl7_14
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_24
    | spl7_25 ),
    inference(avatar_split_clause,[],[f174,f268,f264,f97,f93,f89,f85,f213])).

fof(f174,plain,
    ( r1_tarski(sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f54,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X1)
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X2,X1)
              | ~ m1_orders_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X2,X1)
              | ~ m1_orders_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_orders_2(X2,X0,X1)
             => r1_tarski(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_orders_2)).

fof(f258,plain,
    ( spl7_14
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_22 ),
    inference(avatar_split_clause,[],[f171,f256,f97,f93,f89,f85,f213])).

fof(f171,plain,(
    ! [X17,X15,X16] :
      ( r2_hidden(X15,X16)
      | ~ m1_orders_2(X16,sK0,X17)
      | ~ r2_hidden(sK1,X16)
      | ~ r2_hidden(X15,X17)
      | ~ r2_orders_2(sK0,X15,sK1)
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X15,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f50,f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(X1,X4)
      | ~ m1_orders_2(X4,X0,X3)
      | ~ r2_hidden(X2,X4)
      | ~ r2_hidden(X1,X3)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_hidden(X1,X4)
                      | ~ m1_orders_2(X4,X0,X3)
                      | ~ r2_hidden(X2,X4)
                      | ~ r2_hidden(X1,X3)
                      | ~ r2_orders_2(X0,X1,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_hidden(X1,X4)
                      | ~ m1_orders_2(X4,X0,X3)
                      | ~ r2_hidden(X2,X4)
                      | ~ r2_hidden(X1,X3)
                      | ~ r2_orders_2(X0,X1,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( ( m1_orders_2(X4,X0,X3)
                          & r2_hidden(X2,X4)
                          & r2_hidden(X1,X3)
                          & r2_orders_2(X0,X1,X2) )
                       => r2_hidden(X1,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_orders_2)).

fof(f226,plain,(
    ~ spl7_14 ),
    inference(avatar_contradiction_clause,[],[f225])).

fof(f225,plain,
    ( $false
    | ~ spl7_14 ),
    inference(resolution,[],[f215,f45])).

fof(f45,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f215,plain,
    ( v2_struct_0(sK0)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f213])).

fof(f224,plain,(
    spl7_4 ),
    inference(avatar_contradiction_clause,[],[f223])).

fof(f223,plain,
    ( $false
    | spl7_4 ),
    inference(resolution,[],[f99,f49])).

fof(f49,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f99,plain,
    ( ~ l1_orders_2(sK0)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f97])).

fof(f211,plain,(
    spl7_3 ),
    inference(avatar_contradiction_clause,[],[f210])).

fof(f210,plain,
    ( $false
    | spl7_3 ),
    inference(resolution,[],[f95,f48])).

fof(f48,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f95,plain,
    ( ~ v5_orders_2(sK0)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f93])).

fof(f209,plain,
    ( ~ spl7_12
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f199,f205,f201])).

fof(f199,plain,
    ( ~ r2_hidden(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),k3_orders_2(sK0,sK3,sK1))
    | ~ r2_hidden(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),k3_orders_2(sK0,sK2,sK1)) ),
    inference(resolution,[],[f73,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( sQ6_eqProxy(X0,X1)
      | ~ r2_hidden(sK4(X0,X1),X1)
      | ~ r2_hidden(sK4(X0,X1),X0) ) ),
    inference(equality_proxy_replacement,[],[f64,f72])).

fof(f72,plain,(
    ! [X1,X0] :
      ( sQ6_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ6_eqProxy])])).

fof(f64,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK4(X0,X1),X1)
      | ~ r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK4(X0,X1),X1)
          | ~ r2_hidden(sK4(X0,X1),X0) )
        & ( r2_hidden(sK4(X0,X1),X1)
          | r2_hidden(sK4(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1),X1)
          | ~ r2_hidden(sK4(X0,X1),X0) )
        & ( r2_hidden(sK4(X0,X1),X1)
          | r2_hidden(sK4(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f73,plain,(
    ~ sQ6_eqProxy(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)) ),
    inference(equality_proxy_replacement,[],[f55,f72])).

fof(f55,plain,(
    k3_orders_2(sK0,sK2,sK1) != k3_orders_2(sK0,sK3,sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f208,plain,
    ( spl7_12
    | spl7_13 ),
    inference(avatar_split_clause,[],[f198,f205,f201])).

fof(f198,plain,
    ( r2_hidden(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),k3_orders_2(sK0,sK3,sK1))
    | r2_hidden(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),k3_orders_2(sK0,sK2,sK1)) ),
    inference(resolution,[],[f73,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( sQ6_eqProxy(X0,X1)
      | r2_hidden(sK4(X0,X1),X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(equality_proxy_replacement,[],[f63,f72])).

fof(f63,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK4(X0,X1),X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f177,plain,(
    spl7_2 ),
    inference(avatar_contradiction_clause,[],[f176])).

fof(f176,plain,
    ( $false
    | spl7_2 ),
    inference(resolution,[],[f91,f47])).

fof(f47,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f91,plain,
    ( ~ v4_orders_2(sK0)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f157,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f156])).

fof(f156,plain,
    ( $false
    | spl7_1 ),
    inference(resolution,[],[f87,f46])).

fof(f46,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f87,plain,
    ( ~ v3_orders_2(sK0)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f85])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:08:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.49  % (29070)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.50  % (29069)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % (29097)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.51  % (29098)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.51  % (29078)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.51  % (29090)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.52  % (29071)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (29073)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (29092)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (29077)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (29084)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (29072)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (29076)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (29075)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (29086)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.54  % (29093)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (29087)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  % (29095)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (29074)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (29071)Refutation not found, incomplete strategy% (29071)------------------------------
% 0.22/0.54  % (29071)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (29071)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (29071)Memory used [KB]: 10874
% 0.22/0.54  % (29071)Time elapsed: 0.127 s
% 0.22/0.54  % (29071)------------------------------
% 0.22/0.54  % (29071)------------------------------
% 0.22/0.54  % (29091)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (29080)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (29085)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (29088)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (29081)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (29086)Refutation not found, incomplete strategy% (29086)------------------------------
% 0.22/0.55  % (29086)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (29079)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (29082)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.55  % (29089)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (29083)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.56  % (29096)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.56  % (29094)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.57  % (29086)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (29086)Memory used [KB]: 10618
% 0.22/0.57  % (29086)Time elapsed: 0.143 s
% 0.22/0.57  % (29086)------------------------------
% 0.22/0.57  % (29086)------------------------------
% 1.85/0.63  % (29084)Refutation found. Thanks to Tanya!
% 1.85/0.63  % SZS status Theorem for theBenchmark
% 2.19/0.65  % SZS output start Proof for theBenchmark
% 2.19/0.65  fof(f1307,plain,(
% 2.19/0.65    $false),
% 2.19/0.65    inference(avatar_sat_refutation,[],[f157,f177,f208,f209,f211,f224,f226,f258,f271,f311,f315,f343,f357,f365,f452,f457,f461,f566,f657,f1078,f1103,f1168,f1205,f1207,f1283,f1296,f1306])).
% 2.19/0.65  fof(f1306,plain,(
% 2.19/0.65    spl7_103 | ~spl7_25 | ~spl7_49),
% 2.19/0.65    inference(avatar_split_clause,[],[f1211,f454,f268,f1051])).
% 2.19/0.65  fof(f1051,plain,(
% 2.19/0.65    spl7_103 <=> r2_hidden(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),sK3)),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_103])])).
% 2.19/0.65  fof(f268,plain,(
% 2.19/0.65    spl7_25 <=> r1_tarski(sK2,sK3)),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 2.19/0.65  fof(f454,plain,(
% 2.19/0.65    spl7_49 <=> r2_hidden(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),sK2)),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).
% 2.19/0.65  fof(f1211,plain,(
% 2.19/0.65    r2_hidden(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),sK3) | (~spl7_25 | ~spl7_49)),
% 2.19/0.65    inference(resolution,[],[f456,f359])).
% 2.19/0.65  fof(f359,plain,(
% 2.19/0.65    ( ! [X0] : (~r2_hidden(X0,sK2) | r2_hidden(X0,sK3)) ) | ~spl7_25),
% 2.19/0.65    inference(resolution,[],[f270,f65])).
% 2.19/0.65  fof(f65,plain,(
% 2.19/0.65    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.19/0.65    inference(cnf_transformation,[],[f43])).
% 2.19/0.65  fof(f43,plain,(
% 2.19/0.65    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.19/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f41,f42])).
% 2.19/0.65  fof(f42,plain,(
% 2.19/0.65    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 2.19/0.65    introduced(choice_axiom,[])).
% 2.19/0.65  fof(f41,plain,(
% 2.19/0.65    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.19/0.65    inference(rectify,[],[f40])).
% 2.19/0.65  fof(f40,plain,(
% 2.19/0.65    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.19/0.65    inference(nnf_transformation,[],[f25])).
% 2.19/0.65  fof(f25,plain,(
% 2.19/0.65    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.19/0.65    inference(ennf_transformation,[],[f1])).
% 2.19/0.65  fof(f1,axiom,(
% 2.19/0.65    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.19/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.19/0.65  fof(f270,plain,(
% 2.19/0.65    r1_tarski(sK2,sK3) | ~spl7_25),
% 2.19/0.65    inference(avatar_component_clause,[],[f268])).
% 2.19/0.65  fof(f456,plain,(
% 2.19/0.65    r2_hidden(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),sK2) | ~spl7_49),
% 2.19/0.65    inference(avatar_component_clause,[],[f454])).
% 2.19/0.65  fof(f1296,plain,(
% 2.19/0.65    spl7_14 | ~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_46 | ~spl7_47 | ~spl7_24 | ~spl7_48 | ~spl7_103 | spl7_13),
% 2.19/0.65    inference(avatar_split_clause,[],[f463,f205,f1051,f449,f264,f445,f441,f97,f93,f89,f85,f213])).
% 2.19/0.65  fof(f213,plain,(
% 2.19/0.65    spl7_14 <=> v2_struct_0(sK0)),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 2.19/0.65  fof(f85,plain,(
% 2.19/0.65    spl7_1 <=> v3_orders_2(sK0)),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 2.19/0.65  fof(f89,plain,(
% 2.19/0.65    spl7_2 <=> v4_orders_2(sK0)),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 2.19/0.65  fof(f93,plain,(
% 2.19/0.65    spl7_3 <=> v5_orders_2(sK0)),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 2.19/0.65  fof(f97,plain,(
% 2.19/0.65    spl7_4 <=> l1_orders_2(sK0)),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 2.19/0.65  fof(f441,plain,(
% 2.19/0.65    spl7_46 <=> m1_subset_1(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),u1_struct_0(sK0))),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).
% 2.19/0.65  fof(f445,plain,(
% 2.19/0.65    spl7_47 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).
% 2.19/0.65  fof(f264,plain,(
% 2.19/0.65    spl7_24 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 2.19/0.65  fof(f449,plain,(
% 2.19/0.65    spl7_48 <=> r2_orders_2(sK0,sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),sK1)),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).
% 2.19/0.65  fof(f205,plain,(
% 2.19/0.65    spl7_13 <=> r2_hidden(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),k3_orders_2(sK0,sK3,sK1))),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 2.19/0.65  fof(f463,plain,(
% 2.19/0.65    ~r2_hidden(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),sK3) | ~r2_orders_2(sK0,sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | spl7_13),
% 2.19/0.65    inference(resolution,[],[f206,f58])).
% 2.19/0.65  fof(f58,plain,(
% 2.19/0.65    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.19/0.65    inference(cnf_transformation,[],[f36])).
% 2.19/0.65  fof(f36,plain,(
% 2.19/0.65    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2)) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.19/0.65    inference(flattening,[],[f35])).
% 2.19/0.65  fof(f35,plain,(
% 2.19/0.65    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | (~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2))) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.19/0.65    inference(nnf_transformation,[],[f16])).
% 2.19/0.65  fof(f16,plain,(
% 2.19/0.65    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.19/0.65    inference(flattening,[],[f15])).
% 2.19/0.65  fof(f15,plain,(
% 2.19/0.65    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.19/0.65    inference(ennf_transformation,[],[f8])).
% 2.19/0.65  fof(f8,axiom,(
% 2.19/0.65    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 2.19/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).
% 2.19/0.65  fof(f206,plain,(
% 2.19/0.65    ~r2_hidden(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),k3_orders_2(sK0,sK3,sK1)) | spl7_13),
% 2.19/0.65    inference(avatar_component_clause,[],[f205])).
% 2.19/0.65  fof(f1283,plain,(
% 2.19/0.65    spl7_46 | ~spl7_13 | ~spl7_43),
% 2.19/0.65    inference(avatar_split_clause,[],[f1277,f341,f205,f441])).
% 2.19/0.65  fof(f341,plain,(
% 2.19/0.65    spl7_43 <=> ! [X14] : (m1_subset_1(k3_orders_2(sK0,sK3,X14),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X14,u1_struct_0(sK0)))),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).
% 2.19/0.65  fof(f1277,plain,(
% 2.19/0.65    m1_subset_1(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),u1_struct_0(sK0)) | (~spl7_13 | ~spl7_43)),
% 2.19/0.65    inference(resolution,[],[f1097,f408])).
% 2.19/0.65  fof(f408,plain,(
% 2.19/0.65    m1_subset_1(k3_orders_2(sK0,sK3,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_43),
% 2.19/0.65    inference(resolution,[],[f342,f50])).
% 2.19/0.65  fof(f50,plain,(
% 2.19/0.65    m1_subset_1(sK1,u1_struct_0(sK0))),
% 2.19/0.65    inference(cnf_transformation,[],[f34])).
% 2.19/0.65  fof(f34,plain,(
% 2.19/0.65    (((k3_orders_2(sK0,sK2,sK1) != k3_orders_2(sK0,sK3,sK1) & m1_orders_2(sK2,sK0,sK3) & r2_hidden(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 2.19/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f33,f32,f31,f30])).
% 2.19/0.65  fof(f30,plain,(
% 2.19/0.65    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k3_orders_2(X0,X2,X1) != k3_orders_2(X0,X3,X1) & m1_orders_2(X2,X0,X3) & r2_hidden(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (k3_orders_2(sK0,X2,X1) != k3_orders_2(sK0,X3,X1) & m1_orders_2(X2,sK0,X3) & r2_hidden(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 2.19/0.65    introduced(choice_axiom,[])).
% 2.19/0.65  fof(f31,plain,(
% 2.19/0.65    ? [X1] : (? [X2] : (? [X3] : (k3_orders_2(sK0,X2,X1) != k3_orders_2(sK0,X3,X1) & m1_orders_2(X2,sK0,X3) & r2_hidden(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (? [X3] : (k3_orders_2(sK0,X2,sK1) != k3_orders_2(sK0,X3,sK1) & m1_orders_2(X2,sK0,X3) & r2_hidden(sK1,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 2.19/0.65    introduced(choice_axiom,[])).
% 2.19/0.65  fof(f32,plain,(
% 2.19/0.65    ? [X2] : (? [X3] : (k3_orders_2(sK0,X2,sK1) != k3_orders_2(sK0,X3,sK1) & m1_orders_2(X2,sK0,X3) & r2_hidden(sK1,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X3] : (k3_orders_2(sK0,X3,sK1) != k3_orders_2(sK0,sK2,sK1) & m1_orders_2(sK2,sK0,X3) & r2_hidden(sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.19/0.65    introduced(choice_axiom,[])).
% 2.19/0.65  fof(f33,plain,(
% 2.19/0.65    ? [X3] : (k3_orders_2(sK0,X3,sK1) != k3_orders_2(sK0,sK2,sK1) & m1_orders_2(sK2,sK0,X3) & r2_hidden(sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) => (k3_orders_2(sK0,sK2,sK1) != k3_orders_2(sK0,sK3,sK1) & m1_orders_2(sK2,sK0,sK3) & r2_hidden(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.19/0.65    introduced(choice_axiom,[])).
% 2.19/0.65  fof(f14,plain,(
% 2.19/0.65    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k3_orders_2(X0,X2,X1) != k3_orders_2(X0,X3,X1) & m1_orders_2(X2,X0,X3) & r2_hidden(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.19/0.65    inference(flattening,[],[f13])).
% 2.19/0.65  fof(f13,plain,(
% 2.19/0.65    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((k3_orders_2(X0,X2,X1) != k3_orders_2(X0,X3,X1) & (m1_orders_2(X2,X0,X3) & r2_hidden(X1,X2))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 2.19/0.65    inference(ennf_transformation,[],[f12])).
% 2.19/0.65  fof(f12,negated_conjecture,(
% 2.19/0.65    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_orders_2(X2,X0,X3) & r2_hidden(X1,X2)) => k3_orders_2(X0,X2,X1) = k3_orders_2(X0,X3,X1))))))),
% 2.19/0.65    inference(negated_conjecture,[],[f11])).
% 2.19/0.65  fof(f11,conjecture,(
% 2.19/0.65    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_orders_2(X2,X0,X3) & r2_hidden(X1,X2)) => k3_orders_2(X0,X2,X1) = k3_orders_2(X0,X3,X1))))))),
% 2.19/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_orders_2)).
% 2.19/0.65  fof(f342,plain,(
% 2.19/0.65    ( ! [X14] : (~m1_subset_1(X14,u1_struct_0(sK0)) | m1_subset_1(k3_orders_2(sK0,sK3,X14),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl7_43),
% 2.19/0.65    inference(avatar_component_clause,[],[f341])).
% 2.19/0.65  fof(f1097,plain,(
% 2.19/0.65    ( ! [X0] : (~m1_subset_1(k3_orders_2(sK0,sK3,sK1),k1_zfmisc_1(X0)) | m1_subset_1(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),X0)) ) | ~spl7_13),
% 2.19/0.65    inference(resolution,[],[f207,f71])).
% 2.19/0.65  fof(f71,plain,(
% 2.19/0.65    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.19/0.65    inference(cnf_transformation,[],[f29])).
% 2.19/0.65  fof(f29,plain,(
% 2.19/0.65    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.19/0.65    inference(flattening,[],[f28])).
% 2.19/0.65  fof(f28,plain,(
% 2.19/0.65    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.19/0.65    inference(ennf_transformation,[],[f5])).
% 2.19/0.65  fof(f5,axiom,(
% 2.19/0.65    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.19/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 2.19/0.65  fof(f207,plain,(
% 2.19/0.65    r2_hidden(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),k3_orders_2(sK0,sK3,sK1)) | ~spl7_13),
% 2.19/0.65    inference(avatar_component_clause,[],[f205])).
% 2.19/0.65  fof(f1207,plain,(
% 2.19/0.65    ~spl7_13 | ~spl7_47 | ~spl7_46 | ~spl7_36 | spl7_48),
% 2.19/0.65    inference(avatar_split_clause,[],[f889,f449,f313,f441,f445,f205])).
% 2.19/0.65  fof(f313,plain,(
% 2.19/0.65    spl7_36 <=> ! [X1,X0] : (r2_orders_2(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X0,k3_orders_2(sK0,sK3,X1)))),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).
% 2.19/0.65  fof(f889,plain,(
% 2.19/0.65    ~m1_subset_1(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r2_hidden(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),k3_orders_2(sK0,sK3,sK1)) | (~spl7_36 | spl7_48)),
% 2.19/0.65    inference(resolution,[],[f450,f314])).
% 2.19/0.65  fof(f314,plain,(
% 2.19/0.65    ( ! [X0,X1] : (r2_orders_2(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X0,k3_orders_2(sK0,sK3,X1))) ) | ~spl7_36),
% 2.19/0.65    inference(avatar_component_clause,[],[f313])).
% 2.19/0.65  fof(f450,plain,(
% 2.19/0.65    ~r2_orders_2(sK0,sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),sK1) | spl7_48),
% 2.19/0.65    inference(avatar_component_clause,[],[f449])).
% 2.19/0.65  fof(f1205,plain,(
% 2.19/0.65    spl7_14 | ~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_46 | ~spl7_47 | ~spl7_26 | ~spl7_48 | ~spl7_49 | spl7_12),
% 2.19/0.65    inference(avatar_split_clause,[],[f1090,f201,f454,f449,f273,f445,f441,f97,f93,f89,f85,f213])).
% 2.19/0.65  fof(f273,plain,(
% 2.19/0.65    spl7_26 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 2.19/0.65  fof(f201,plain,(
% 2.19/0.65    spl7_12 <=> r2_hidden(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),k3_orders_2(sK0,sK2,sK1))),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 2.19/0.65  fof(f1090,plain,(
% 2.19/0.65    ~r2_hidden(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),sK2) | ~r2_orders_2(sK0,sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | spl7_12),
% 2.19/0.65    inference(resolution,[],[f202,f58])).
% 2.19/0.65  fof(f202,plain,(
% 2.19/0.65    ~r2_hidden(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),k3_orders_2(sK0,sK2,sK1)) | spl7_12),
% 2.19/0.65    inference(avatar_component_clause,[],[f201])).
% 2.19/0.65  fof(f1168,plain,(
% 2.19/0.65    ~spl7_48 | ~spl7_103 | spl7_49 | ~spl7_46 | ~spl7_69),
% 2.19/0.65    inference(avatar_split_clause,[],[f1128,f655,f441,f454,f1051,f449])).
% 2.19/0.65  fof(f655,plain,(
% 2.19/0.65    spl7_69 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK2) | ~r2_hidden(X0,sK3) | ~r2_orders_2(sK0,X0,sK1))),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_69])])).
% 2.19/0.65  fof(f1128,plain,(
% 2.19/0.65    r2_hidden(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),sK2) | ~r2_hidden(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),sK3) | ~r2_orders_2(sK0,sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),sK1) | (~spl7_46 | ~spl7_69)),
% 2.19/0.65    inference(resolution,[],[f442,f656])).
% 2.19/0.65  fof(f656,plain,(
% 2.19/0.65    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK2) | ~r2_hidden(X0,sK3) | ~r2_orders_2(sK0,X0,sK1)) ) | ~spl7_69),
% 2.19/0.65    inference(avatar_component_clause,[],[f655])).
% 2.19/0.65  fof(f442,plain,(
% 2.19/0.65    m1_subset_1(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),u1_struct_0(sK0)) | ~spl7_46),
% 2.19/0.65    inference(avatar_component_clause,[],[f441])).
% 2.19/0.65  fof(f1103,plain,(
% 2.19/0.65    spl7_14 | ~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_46 | ~spl7_47 | ~spl7_24 | spl7_103 | ~spl7_13),
% 2.19/0.65    inference(avatar_split_clause,[],[f1096,f205,f1051,f264,f445,f441,f97,f93,f89,f85,f213])).
% 2.19/0.65  fof(f1096,plain,(
% 2.19/0.65    r2_hidden(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~spl7_13),
% 2.19/0.65    inference(resolution,[],[f207,f57])).
% 2.19/0.65  fof(f57,plain,(
% 2.19/0.65    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.19/0.65    inference(cnf_transformation,[],[f36])).
% 2.19/0.65  fof(f1078,plain,(
% 2.19/0.65    spl7_46 | ~spl7_12 | ~spl7_35),
% 2.19/0.65    inference(avatar_split_clause,[],[f1072,f309,f201,f441])).
% 2.19/0.65  fof(f309,plain,(
% 2.19/0.65    spl7_35 <=> ! [X14] : (m1_subset_1(k3_orders_2(sK0,sK2,X14),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X14,u1_struct_0(sK0)))),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).
% 2.19/0.65  fof(f1072,plain,(
% 2.19/0.65    m1_subset_1(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),u1_struct_0(sK0)) | (~spl7_12 | ~spl7_35)),
% 2.19/0.65    inference(resolution,[],[f434,f405])).
% 2.19/0.65  fof(f405,plain,(
% 2.19/0.65    m1_subset_1(k3_orders_2(sK0,sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_35),
% 2.19/0.65    inference(resolution,[],[f310,f50])).
% 2.19/0.65  fof(f310,plain,(
% 2.19/0.65    ( ! [X14] : (~m1_subset_1(X14,u1_struct_0(sK0)) | m1_subset_1(k3_orders_2(sK0,sK2,X14),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl7_35),
% 2.19/0.65    inference(avatar_component_clause,[],[f309])).
% 2.19/0.65  fof(f434,plain,(
% 2.19/0.65    ( ! [X0] : (~m1_subset_1(k3_orders_2(sK0,sK2,sK1),k1_zfmisc_1(X0)) | m1_subset_1(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),X0)) ) | ~spl7_12),
% 2.19/0.65    inference(resolution,[],[f203,f71])).
% 2.19/0.65  fof(f203,plain,(
% 2.19/0.65    r2_hidden(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),k3_orders_2(sK0,sK2,sK1)) | ~spl7_12),
% 2.19/0.65    inference(avatar_component_clause,[],[f201])).
% 2.19/0.65  fof(f657,plain,(
% 2.19/0.65    ~spl7_58 | ~spl7_26 | ~spl7_24 | spl7_69 | ~spl7_22),
% 2.19/0.65    inference(avatar_split_clause,[],[f653,f256,f655,f264,f273,f555])).
% 2.19/0.65  fof(f555,plain,(
% 2.19/0.65    spl7_58 <=> r2_hidden(sK1,sK2)),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_58])])).
% 2.19/0.65  fof(f256,plain,(
% 2.19/0.65    spl7_22 <=> ! [X16,X15,X17] : (r2_hidden(X15,X16) | ~m1_subset_1(X15,u1_struct_0(sK0)) | ~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_orders_2(sK0,X15,sK1) | ~r2_hidden(X15,X17) | ~r2_hidden(sK1,X16) | ~m1_orders_2(X16,sK0,X17))),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 2.19/0.65  fof(f653,plain,(
% 2.19/0.65    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_orders_2(sK0,X0,sK1) | ~r2_hidden(X0,sK3) | ~r2_hidden(sK1,sK2) | r2_hidden(X0,sK2)) ) | ~spl7_22),
% 2.19/0.65    inference(resolution,[],[f257,f54])).
% 2.19/0.65  fof(f54,plain,(
% 2.19/0.65    m1_orders_2(sK2,sK0,sK3)),
% 2.19/0.65    inference(cnf_transformation,[],[f34])).
% 2.19/0.65  fof(f257,plain,(
% 2.19/0.65    ( ! [X17,X15,X16] : (~m1_orders_2(X16,sK0,X17) | ~m1_subset_1(X15,u1_struct_0(sK0)) | ~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_orders_2(sK0,X15,sK1) | ~r2_hidden(X15,X17) | ~r2_hidden(sK1,X16) | r2_hidden(X15,X16)) ) | ~spl7_22),
% 2.19/0.65    inference(avatar_component_clause,[],[f256])).
% 2.19/0.65  fof(f566,plain,(
% 2.19/0.65    spl7_58),
% 2.19/0.65    inference(avatar_contradiction_clause,[],[f562])).
% 2.19/0.65  fof(f562,plain,(
% 2.19/0.65    $false | spl7_58),
% 2.19/0.65    inference(resolution,[],[f557,f53])).
% 2.19/0.65  fof(f53,plain,(
% 2.19/0.65    r2_hidden(sK1,sK2)),
% 2.19/0.65    inference(cnf_transformation,[],[f34])).
% 2.19/0.65  fof(f557,plain,(
% 2.19/0.65    ~r2_hidden(sK1,sK2) | spl7_58),
% 2.19/0.65    inference(avatar_component_clause,[],[f555])).
% 2.19/0.65  fof(f461,plain,(
% 2.19/0.65    spl7_47),
% 2.19/0.65    inference(avatar_contradiction_clause,[],[f458])).
% 2.19/0.65  fof(f458,plain,(
% 2.19/0.65    $false | spl7_47),
% 2.19/0.65    inference(resolution,[],[f447,f50])).
% 2.19/0.65  fof(f447,plain,(
% 2.19/0.65    ~m1_subset_1(sK1,u1_struct_0(sK0)) | spl7_47),
% 2.19/0.65    inference(avatar_component_clause,[],[f445])).
% 2.19/0.65  fof(f457,plain,(
% 2.19/0.65    spl7_14 | ~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_46 | ~spl7_47 | ~spl7_26 | spl7_49 | ~spl7_12),
% 2.19/0.65    inference(avatar_split_clause,[],[f433,f201,f454,f273,f445,f441,f97,f93,f89,f85,f213])).
% 2.19/0.65  fof(f433,plain,(
% 2.19/0.65    r2_hidden(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~spl7_12),
% 2.19/0.65    inference(resolution,[],[f203,f57])).
% 2.19/0.65  fof(f452,plain,(
% 2.19/0.65    spl7_14 | ~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_46 | ~spl7_47 | ~spl7_26 | spl7_48 | ~spl7_12),
% 2.19/0.65    inference(avatar_split_clause,[],[f432,f201,f449,f273,f445,f441,f97,f93,f89,f85,f213])).
% 2.19/0.65  fof(f432,plain,(
% 2.19/0.65    r2_orders_2(sK0,sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~spl7_12),
% 2.19/0.65    inference(resolution,[],[f203,f56])).
% 2.19/0.65  fof(f56,plain,(
% 2.19/0.65    ( ! [X2,X0,X3,X1] : (r2_orders_2(X0,X1,X2) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.19/0.65    inference(cnf_transformation,[],[f36])).
% 2.19/0.65  fof(f365,plain,(
% 2.19/0.65    spl7_26),
% 2.19/0.65    inference(avatar_contradiction_clause,[],[f360])).
% 2.19/0.65  fof(f360,plain,(
% 2.19/0.65    $false | spl7_26),
% 2.19/0.65    inference(resolution,[],[f275,f51])).
% 2.19/0.65  fof(f51,plain,(
% 2.19/0.65    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.19/0.65    inference(cnf_transformation,[],[f34])).
% 2.19/0.65  fof(f275,plain,(
% 2.19/0.65    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | spl7_26),
% 2.19/0.65    inference(avatar_component_clause,[],[f273])).
% 2.19/0.65  fof(f357,plain,(
% 2.19/0.65    spl7_24),
% 2.19/0.65    inference(avatar_contradiction_clause,[],[f352])).
% 2.19/0.65  fof(f352,plain,(
% 2.19/0.65    $false | spl7_24),
% 2.19/0.65    inference(resolution,[],[f266,f52])).
% 2.19/0.65  fof(f52,plain,(
% 2.19/0.65    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.19/0.65    inference(cnf_transformation,[],[f34])).
% 2.19/0.65  fof(f266,plain,(
% 2.19/0.65    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | spl7_24),
% 2.19/0.65    inference(avatar_component_clause,[],[f264])).
% 2.19/0.65  fof(f343,plain,(
% 2.19/0.65    spl7_14 | ~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | spl7_43),
% 2.19/0.65    inference(avatar_split_clause,[],[f195,f341,f97,f93,f89,f85,f213])).
% 2.19/0.65  fof(f195,plain,(
% 2.19/0.65    ( ! [X14] : (m1_subset_1(k3_orders_2(sK0,sK3,X14),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X14,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 2.19/0.65    inference(resolution,[],[f52,f70])).
% 2.19/0.65  fof(f70,plain,(
% 2.19/0.65    ( ! [X2,X0,X1] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.19/0.65    inference(cnf_transformation,[],[f27])).
% 2.19/0.65  fof(f27,plain,(
% 2.19/0.65    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.19/0.65    inference(flattening,[],[f26])).
% 2.19/0.65  fof(f26,plain,(
% 2.19/0.65    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.19/0.65    inference(ennf_transformation,[],[f6])).
% 2.19/0.65  fof(f6,axiom,(
% 2.19/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.19/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_orders_2)).
% 2.19/0.65  fof(f315,plain,(
% 2.19/0.65    spl7_14 | ~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | spl7_36),
% 2.19/0.65    inference(avatar_split_clause,[],[f188,f313,f97,f93,f89,f85,f213])).
% 2.19/0.65  fof(f188,plain,(
% 2.19/0.65    ( ! [X0,X1] : (r2_orders_2(sK0,X0,X1) | ~r2_hidden(X0,k3_orders_2(sK0,sK3,X1)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 2.19/0.65    inference(resolution,[],[f52,f56])).
% 2.19/0.65  fof(f311,plain,(
% 2.19/0.65    spl7_14 | ~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | spl7_35),
% 2.19/0.65    inference(avatar_split_clause,[],[f185,f309,f97,f93,f89,f85,f213])).
% 2.19/0.65  fof(f185,plain,(
% 2.19/0.65    ( ! [X14] : (m1_subset_1(k3_orders_2(sK0,sK2,X14),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X14,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 2.19/0.65    inference(resolution,[],[f51,f70])).
% 2.19/0.65  fof(f271,plain,(
% 2.19/0.65    spl7_14 | ~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_24 | spl7_25),
% 2.19/0.65    inference(avatar_split_clause,[],[f174,f268,f264,f97,f93,f89,f85,f213])).
% 2.19/0.65  fof(f174,plain,(
% 2.19/0.65    r1_tarski(sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 2.19/0.65    inference(resolution,[],[f54,f60])).
% 2.19/0.65  fof(f60,plain,(
% 2.19/0.65    ( ! [X2,X0,X1] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.19/0.65    inference(cnf_transformation,[],[f20])).
% 2.19/0.65  fof(f20,plain,(
% 2.19/0.65    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.19/0.65    inference(flattening,[],[f19])).
% 2.19/0.65  fof(f19,plain,(
% 2.19/0.65    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.19/0.65    inference(ennf_transformation,[],[f9])).
% 2.19/0.65  fof(f9,axiom,(
% 2.19/0.65    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 2.19/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_orders_2)).
% 2.19/0.65  fof(f258,plain,(
% 2.19/0.65    spl7_14 | ~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | spl7_22),
% 2.19/0.65    inference(avatar_split_clause,[],[f171,f256,f97,f93,f89,f85,f213])).
% 2.19/0.65  fof(f171,plain,(
% 2.19/0.65    ( ! [X17,X15,X16] : (r2_hidden(X15,X16) | ~m1_orders_2(X16,sK0,X17) | ~r2_hidden(sK1,X16) | ~r2_hidden(X15,X17) | ~r2_orders_2(sK0,X15,sK1) | ~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X15,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 2.19/0.65    inference(resolution,[],[f50,f59])).
% 2.19/0.65  fof(f59,plain,(
% 2.19/0.65    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(X1,X4) | ~m1_orders_2(X4,X0,X3) | ~r2_hidden(X2,X4) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.19/0.65    inference(cnf_transformation,[],[f18])).
% 2.19/0.65  fof(f18,plain,(
% 2.19/0.65    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_hidden(X1,X4) | ~m1_orders_2(X4,X0,X3) | ~r2_hidden(X2,X4) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.19/0.65    inference(flattening,[],[f17])).
% 2.19/0.65  fof(f17,plain,(
% 2.19/0.65    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_hidden(X1,X4) | (~m1_orders_2(X4,X0,X3) | ~r2_hidden(X2,X4) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.19/0.65    inference(ennf_transformation,[],[f10])).
% 2.19/0.65  fof(f10,axiom,(
% 2.19/0.65    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_orders_2(X4,X0,X3) & r2_hidden(X2,X4) & r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) => r2_hidden(X1,X4)))))))),
% 2.19/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_orders_2)).
% 2.19/0.65  fof(f226,plain,(
% 2.19/0.65    ~spl7_14),
% 2.19/0.65    inference(avatar_contradiction_clause,[],[f225])).
% 2.19/0.65  fof(f225,plain,(
% 2.19/0.65    $false | ~spl7_14),
% 2.19/0.65    inference(resolution,[],[f215,f45])).
% 2.19/0.65  fof(f45,plain,(
% 2.19/0.65    ~v2_struct_0(sK0)),
% 2.19/0.65    inference(cnf_transformation,[],[f34])).
% 2.19/0.65  fof(f215,plain,(
% 2.19/0.65    v2_struct_0(sK0) | ~spl7_14),
% 2.19/0.65    inference(avatar_component_clause,[],[f213])).
% 2.19/0.65  fof(f224,plain,(
% 2.19/0.65    spl7_4),
% 2.19/0.65    inference(avatar_contradiction_clause,[],[f223])).
% 2.19/0.65  fof(f223,plain,(
% 2.19/0.65    $false | spl7_4),
% 2.19/0.65    inference(resolution,[],[f99,f49])).
% 2.19/0.65  fof(f49,plain,(
% 2.19/0.65    l1_orders_2(sK0)),
% 2.19/0.65    inference(cnf_transformation,[],[f34])).
% 2.19/0.65  fof(f99,plain,(
% 2.19/0.65    ~l1_orders_2(sK0) | spl7_4),
% 2.19/0.65    inference(avatar_component_clause,[],[f97])).
% 2.19/0.65  fof(f211,plain,(
% 2.19/0.65    spl7_3),
% 2.19/0.65    inference(avatar_contradiction_clause,[],[f210])).
% 2.19/0.65  fof(f210,plain,(
% 2.19/0.65    $false | spl7_3),
% 2.19/0.65    inference(resolution,[],[f95,f48])).
% 2.19/0.65  fof(f48,plain,(
% 2.19/0.65    v5_orders_2(sK0)),
% 2.19/0.65    inference(cnf_transformation,[],[f34])).
% 2.19/0.65  fof(f95,plain,(
% 2.19/0.65    ~v5_orders_2(sK0) | spl7_3),
% 2.19/0.65    inference(avatar_component_clause,[],[f93])).
% 2.19/0.65  fof(f209,plain,(
% 2.19/0.65    ~spl7_12 | ~spl7_13),
% 2.19/0.65    inference(avatar_split_clause,[],[f199,f205,f201])).
% 2.19/0.65  fof(f199,plain,(
% 2.19/0.65    ~r2_hidden(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),k3_orders_2(sK0,sK3,sK1)) | ~r2_hidden(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),k3_orders_2(sK0,sK2,sK1))),
% 2.19/0.65    inference(resolution,[],[f73,f74])).
% 2.19/0.65  fof(f74,plain,(
% 2.19/0.65    ( ! [X0,X1] : (sQ6_eqProxy(X0,X1) | ~r2_hidden(sK4(X0,X1),X1) | ~r2_hidden(sK4(X0,X1),X0)) )),
% 2.19/0.65    inference(equality_proxy_replacement,[],[f64,f72])).
% 2.19/0.65  fof(f72,plain,(
% 2.19/0.65    ! [X1,X0] : (sQ6_eqProxy(X0,X1) <=> X0 = X1)),
% 2.19/0.65    introduced(equality_proxy_definition,[new_symbols(naming,[sQ6_eqProxy])])).
% 2.19/0.65  fof(f64,plain,(
% 2.19/0.65    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK4(X0,X1),X1) | ~r2_hidden(sK4(X0,X1),X0)) )),
% 2.19/0.65    inference(cnf_transformation,[],[f39])).
% 2.19/0.65  fof(f39,plain,(
% 2.19/0.65    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK4(X0,X1),X1) | ~r2_hidden(sK4(X0,X1),X0)) & (r2_hidden(sK4(X0,X1),X1) | r2_hidden(sK4(X0,X1),X0))))),
% 2.19/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f38])).
% 2.19/0.65  fof(f38,plain,(
% 2.19/0.65    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK4(X0,X1),X1) | ~r2_hidden(sK4(X0,X1),X0)) & (r2_hidden(sK4(X0,X1),X1) | r2_hidden(sK4(X0,X1),X0))))),
% 2.19/0.65    introduced(choice_axiom,[])).
% 2.19/0.65  fof(f37,plain,(
% 2.19/0.65    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 2.19/0.65    inference(nnf_transformation,[],[f24])).
% 2.19/0.65  fof(f24,plain,(
% 2.19/0.65    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 2.19/0.65    inference(ennf_transformation,[],[f2])).
% 2.19/0.65  fof(f2,axiom,(
% 2.19/0.65    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 2.19/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 2.19/0.65  fof(f73,plain,(
% 2.19/0.65    ~sQ6_eqProxy(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1))),
% 2.19/0.65    inference(equality_proxy_replacement,[],[f55,f72])).
% 2.19/0.65  fof(f55,plain,(
% 2.19/0.65    k3_orders_2(sK0,sK2,sK1) != k3_orders_2(sK0,sK3,sK1)),
% 2.19/0.65    inference(cnf_transformation,[],[f34])).
% 2.19/0.65  fof(f208,plain,(
% 2.19/0.65    spl7_12 | spl7_13),
% 2.19/0.65    inference(avatar_split_clause,[],[f198,f205,f201])).
% 2.19/0.65  fof(f198,plain,(
% 2.19/0.65    r2_hidden(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),k3_orders_2(sK0,sK3,sK1)) | r2_hidden(sK4(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),k3_orders_2(sK0,sK2,sK1))),
% 2.19/0.65    inference(resolution,[],[f73,f75])).
% 2.19/0.65  fof(f75,plain,(
% 2.19/0.65    ( ! [X0,X1] : (sQ6_eqProxy(X0,X1) | r2_hidden(sK4(X0,X1),X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 2.19/0.65    inference(equality_proxy_replacement,[],[f63,f72])).
% 2.19/0.65  fof(f63,plain,(
% 2.19/0.65    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK4(X0,X1),X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 2.19/0.65    inference(cnf_transformation,[],[f39])).
% 2.19/0.65  fof(f177,plain,(
% 2.19/0.65    spl7_2),
% 2.19/0.65    inference(avatar_contradiction_clause,[],[f176])).
% 2.19/0.65  fof(f176,plain,(
% 2.19/0.65    $false | spl7_2),
% 2.19/0.65    inference(resolution,[],[f91,f47])).
% 2.19/0.65  fof(f47,plain,(
% 2.19/0.65    v4_orders_2(sK0)),
% 2.19/0.65    inference(cnf_transformation,[],[f34])).
% 2.19/0.65  fof(f91,plain,(
% 2.19/0.65    ~v4_orders_2(sK0) | spl7_2),
% 2.19/0.65    inference(avatar_component_clause,[],[f89])).
% 2.19/0.65  fof(f157,plain,(
% 2.19/0.65    spl7_1),
% 2.19/0.65    inference(avatar_contradiction_clause,[],[f156])).
% 2.19/0.65  fof(f156,plain,(
% 2.19/0.65    $false | spl7_1),
% 2.19/0.65    inference(resolution,[],[f87,f46])).
% 2.19/0.65  fof(f46,plain,(
% 2.19/0.65    v3_orders_2(sK0)),
% 2.19/0.65    inference(cnf_transformation,[],[f34])).
% 2.19/0.65  fof(f87,plain,(
% 2.19/0.65    ~v3_orders_2(sK0) | spl7_1),
% 2.19/0.65    inference(avatar_component_clause,[],[f85])).
% 2.19/0.65  % SZS output end Proof for theBenchmark
% 2.19/0.65  % (29084)------------------------------
% 2.19/0.65  % (29084)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.65  % (29084)Termination reason: Refutation
% 2.19/0.65  
% 2.19/0.65  % (29084)Memory used [KB]: 7036
% 2.19/0.65  % (29084)Time elapsed: 0.180 s
% 2.19/0.65  % (29084)------------------------------
% 2.19/0.65  % (29084)------------------------------
% 2.19/0.65  % (29068)Success in time 0.295 s
%------------------------------------------------------------------------------
