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
% DateTime   : Thu Dec  3 13:10:08 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 181 expanded)
%              Number of leaves         :   23 (  92 expanded)
%              Depth                    :    7
%              Number of atoms          :  445 (1059 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f140,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f44,f49,f54,f59,f64,f69,f74,f78,f82,f94,f109,f118,f123,f129,f135,f139])).

fof(f139,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f136,f132,f76,f61,f56,f51,f46,f41,f36])).

fof(f36,plain,
    ( spl3_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f41,plain,
    ( spl3_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f46,plain,
    ( spl3_3
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f51,plain,
    ( spl3_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f56,plain,
    ( spl3_5
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f61,plain,
    ( spl3_6
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f76,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f132,plain,
    ( spl3_21
  <=> r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f136,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_9
    | ~ spl3_21 ),
    inference(resolution,[],[f134,f77])).

fof(f77,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0)
        | v2_struct_0(X0) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f76])).

fof(f134,plain,
    ( r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f132])).

fof(f135,plain,
    ( ~ spl3_8
    | spl3_21
    | ~ spl3_6
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f130,f127,f61,f132,f71])).

fof(f71,plain,
    ( spl3_8
  <=> r2_hidden(sK1,k3_orders_2(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f127,plain,
    ( spl3_20
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
        | ~ r2_hidden(sK1,k3_orders_2(sK0,sK2,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f130,plain,
    ( r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    | ~ r2_hidden(sK1,k3_orders_2(sK0,sK2,sK1))
    | ~ spl3_6
    | ~ spl3_20 ),
    inference(resolution,[],[f128,f63])).

fof(f63,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f61])).

fof(f128,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
        | ~ r2_hidden(sK1,k3_orders_2(sK0,sK2,X0)) )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f127])).

fof(f129,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | spl3_20
    | ~ spl3_10
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f125,f121,f80,f127,f61,f56,f51,f46,f41,f36])).

fof(f80,plain,
    ( spl3_10
  <=> ! [X1,X0,X2] :
        ( r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
        | ~ r2_orders_2(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f121,plain,
    ( spl3_19
  <=> ! [X0] :
        ( r2_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(sK1,k3_orders_2(sK0,sK2,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f125,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(sK1,k3_orders_2(sK0,sK2,X0))
        | r2_hidden(X0,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl3_10
    | ~ spl3_19 ),
    inference(duplicate_literal_removal,[],[f124])).

fof(f124,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(sK1,k3_orders_2(sK0,sK2,X0))
        | r2_hidden(X0,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl3_10
    | ~ spl3_19 ),
    inference(resolution,[],[f122,f81])).

fof(f81,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_orders_2(X0,X1,X2)
        | r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0)
        | v2_struct_0(X0) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f80])).

fof(f122,plain,
    ( ! [X0] :
        ( r2_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(sK1,k3_orders_2(sK0,sK2,X0)) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f121])).

fof(f123,plain,
    ( spl3_19
    | ~ spl3_6
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f119,f116,f61,f121])).

fof(f116,plain,
    ( spl3_18
  <=> ! [X1,X0] :
        ( r2_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k3_orders_2(sK0,sK2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f119,plain,
    ( ! [X0] :
        ( r2_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(sK1,k3_orders_2(sK0,sK2,X0)) )
    | ~ spl3_6
    | ~ spl3_18 ),
    inference(resolution,[],[f117,f63])).

fof(f117,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k3_orders_2(sK0,sK2,X1)) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f116])).

fof(f118,plain,
    ( spl3_18
    | ~ spl3_7
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f114,f107,f66,f116])).

fof(f66,plain,
    ( spl3_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f107,plain,
    ( spl3_16
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,k3_orders_2(sK0,X1,X2))
        | r2_orders_2(sK0,X0,X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f114,plain,
    ( ! [X0,X1] :
        ( r2_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k3_orders_2(sK0,sK2,X1)) )
    | ~ spl3_7
    | ~ spl3_16 ),
    inference(resolution,[],[f108,f68])).

fof(f68,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f66])).

fof(f108,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,X0,X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k3_orders_2(sK0,X1,X2)) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f107])).

fof(f109,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | spl3_16
    | ~ spl3_5
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f100,f92,f56,f107,f51,f46,f41,f36])).

fof(f92,plain,
    ( spl3_13
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
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f100,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k3_orders_2(sK0,X1,X2))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_orders_2(sK0,X0,X2)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl3_5
    | ~ spl3_13 ),
    inference(resolution,[],[f93,f58])).

fof(f58,plain,
    ( l1_orders_2(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f56])).

fof(f93,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ l1_orders_2(X0)
        | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | r2_orders_2(X0,X1,X2)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0)
        | v2_struct_0(X0) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f92])).

fof(f94,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f32,f92])).

fof(f32,plain,(
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
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f82,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f30,f80])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
      | ~ r2_orders_2(X0,X1,X2)
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
              ( ( ( r2_orders_2(X0,X1,X2)
                  | ~ r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) )
                & ( r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) )
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
             => ( r2_orders_2(X0,X1,X2)
              <=> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_orders_2)).

fof(f78,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f29,f76])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_orders_2)).

fof(f74,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f28,f71])).

fof(f28,plain,(
    r2_hidden(sK1,k3_orders_2(sK0,sK2,sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( r2_hidden(sK1,k3_orders_2(sK0,sK2,sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f16,f15,f14])).

fof(f14,plain,
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

fof(f15,plain,
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

fof(f16,plain,
    ( ? [X2] :
        ( r2_hidden(sK1,k3_orders_2(sK0,X2,sK1))
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( r2_hidden(sK1,k3_orders_2(sK0,sK2,sK1))
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
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
    inference(flattening,[],[f6])).

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
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
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
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_orders_2)).

fof(f69,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f27,f66])).

fof(f27,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f64,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f26,f61])).

fof(f26,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f59,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f25,f56])).

fof(f25,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f54,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f24,f51])).

fof(f24,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f49,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f23,f46])).

fof(f23,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f44,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f22,f41])).

fof(f22,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f39,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f21,f36])).

fof(f21,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:28:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.42  % (21836)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 0.20/0.43  % (21836)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f140,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f39,f44,f49,f54,f59,f64,f69,f74,f78,f82,f94,f109,f118,f123,f129,f135,f139])).
% 0.20/0.43  fof(f139,plain,(
% 0.20/0.43    spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_9 | ~spl3_21),
% 0.20/0.43    inference(avatar_split_clause,[],[f136,f132,f76,f61,f56,f51,f46,f41,f36])).
% 0.20/0.43  fof(f36,plain,(
% 0.20/0.43    spl3_1 <=> v2_struct_0(sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.43  fof(f41,plain,(
% 0.20/0.43    spl3_2 <=> v3_orders_2(sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.43  fof(f46,plain,(
% 0.20/0.43    spl3_3 <=> v4_orders_2(sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.43  fof(f51,plain,(
% 0.20/0.43    spl3_4 <=> v5_orders_2(sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.43  fof(f56,plain,(
% 0.20/0.43    spl3_5 <=> l1_orders_2(sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.43  fof(f61,plain,(
% 0.20/0.43    spl3_6 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.43  fof(f76,plain,(
% 0.20/0.43    spl3_9 <=> ! [X1,X0] : (~r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.43  fof(f132,plain,(
% 0.20/0.43    spl3_21 <=> r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.20/0.43  fof(f136,plain,(
% 0.20/0.43    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | (~spl3_9 | ~spl3_21)),
% 0.20/0.43    inference(resolution,[],[f134,f77])).
% 0.20/0.43  fof(f77,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) ) | ~spl3_9),
% 0.20/0.43    inference(avatar_component_clause,[],[f76])).
% 0.20/0.43  fof(f134,plain,(
% 0.20/0.43    r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | ~spl3_21),
% 0.20/0.43    inference(avatar_component_clause,[],[f132])).
% 0.20/0.43  fof(f135,plain,(
% 0.20/0.43    ~spl3_8 | spl3_21 | ~spl3_6 | ~spl3_20),
% 0.20/0.43    inference(avatar_split_clause,[],[f130,f127,f61,f132,f71])).
% 0.20/0.43  fof(f71,plain,(
% 0.20/0.43    spl3_8 <=> r2_hidden(sK1,k3_orders_2(sK0,sK2,sK1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.43  fof(f127,plain,(
% 0.20/0.43    spl3_20 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | ~r2_hidden(sK1,k3_orders_2(sK0,sK2,X0)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.20/0.43  fof(f130,plain,(
% 0.20/0.43    r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | ~r2_hidden(sK1,k3_orders_2(sK0,sK2,sK1)) | (~spl3_6 | ~spl3_20)),
% 0.20/0.43    inference(resolution,[],[f128,f63])).
% 0.20/0.43  fof(f63,plain,(
% 0.20/0.43    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl3_6),
% 0.20/0.43    inference(avatar_component_clause,[],[f61])).
% 0.20/0.43  fof(f128,plain,(
% 0.20/0.43    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | ~r2_hidden(sK1,k3_orders_2(sK0,sK2,X0))) ) | ~spl3_20),
% 0.20/0.43    inference(avatar_component_clause,[],[f127])).
% 0.20/0.43  fof(f129,plain,(
% 0.20/0.43    spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6 | spl3_20 | ~spl3_10 | ~spl3_19),
% 0.20/0.43    inference(avatar_split_clause,[],[f125,f121,f80,f127,f61,f56,f51,f46,f41,f36])).
% 0.20/0.43  fof(f80,plain,(
% 0.20/0.43    spl3_10 <=> ! [X1,X0,X2] : (r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.43  fof(f121,plain,(
% 0.20/0.43    spl3_19 <=> ! [X0] : (r2_orders_2(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK1,k3_orders_2(sK0,sK2,X0)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.20/0.43  fof(f125,plain,(
% 0.20/0.43    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK1,k3_orders_2(sK0,sK2,X0)) | r2_hidden(X0,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl3_10 | ~spl3_19)),
% 0.20/0.43    inference(duplicate_literal_removal,[],[f124])).
% 0.20/0.43  fof(f124,plain,(
% 0.20/0.43    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK1,k3_orders_2(sK0,sK2,X0)) | r2_hidden(X0,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl3_10 | ~spl3_19)),
% 0.20/0.43    inference(resolution,[],[f122,f81])).
% 0.20/0.43  fof(f81,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~r2_orders_2(X0,X1,X2) | r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) ) | ~spl3_10),
% 0.20/0.43    inference(avatar_component_clause,[],[f80])).
% 0.20/0.43  fof(f122,plain,(
% 0.20/0.43    ( ! [X0] : (r2_orders_2(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK1,k3_orders_2(sK0,sK2,X0))) ) | ~spl3_19),
% 0.20/0.43    inference(avatar_component_clause,[],[f121])).
% 0.20/0.43  fof(f123,plain,(
% 0.20/0.43    spl3_19 | ~spl3_6 | ~spl3_18),
% 0.20/0.43    inference(avatar_split_clause,[],[f119,f116,f61,f121])).
% 0.20/0.43  fof(f116,plain,(
% 0.20/0.43    spl3_18 <=> ! [X1,X0] : (r2_orders_2(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X0,k3_orders_2(sK0,sK2,X1)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.43  fof(f119,plain,(
% 0.20/0.43    ( ! [X0] : (r2_orders_2(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK1,k3_orders_2(sK0,sK2,X0))) ) | (~spl3_6 | ~spl3_18)),
% 0.20/0.43    inference(resolution,[],[f117,f63])).
% 0.20/0.43  fof(f117,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_orders_2(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X0,k3_orders_2(sK0,sK2,X1))) ) | ~spl3_18),
% 0.20/0.43    inference(avatar_component_clause,[],[f116])).
% 0.20/0.43  fof(f118,plain,(
% 0.20/0.43    spl3_18 | ~spl3_7 | ~spl3_16),
% 0.20/0.43    inference(avatar_split_clause,[],[f114,f107,f66,f116])).
% 0.20/0.43  fof(f66,plain,(
% 0.20/0.43    spl3_7 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.43  fof(f107,plain,(
% 0.20/0.43    spl3_16 <=> ! [X1,X0,X2] : (~r2_hidden(X0,k3_orders_2(sK0,X1,X2)) | r2_orders_2(sK0,X0,X2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.43  fof(f114,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r2_orders_2(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X0,k3_orders_2(sK0,sK2,X1))) ) | (~spl3_7 | ~spl3_16)),
% 0.20/0.43    inference(resolution,[],[f108,f68])).
% 0.20/0.43  fof(f68,plain,(
% 0.20/0.43    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_7),
% 0.20/0.43    inference(avatar_component_clause,[],[f66])).
% 0.20/0.43  fof(f108,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,X0,X2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X0,k3_orders_2(sK0,X1,X2))) ) | ~spl3_16),
% 0.20/0.43    inference(avatar_component_clause,[],[f107])).
% 0.20/0.43  fof(f109,plain,(
% 0.20/0.43    spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | spl3_16 | ~spl3_5 | ~spl3_13),
% 0.20/0.43    inference(avatar_split_clause,[],[f100,f92,f56,f107,f51,f46,f41,f36])).
% 0.20/0.43  fof(f92,plain,(
% 0.20/0.43    spl3_13 <=> ! [X1,X3,X0,X2] : (r2_orders_2(X0,X1,X2) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.43  fof(f100,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_orders_2(sK0,X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_orders_2(sK0,X0,X2) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl3_5 | ~spl3_13)),
% 0.20/0.43    inference(resolution,[],[f93,f58])).
% 0.20/0.43  fof(f58,plain,(
% 0.20/0.43    l1_orders_2(sK0) | ~spl3_5),
% 0.20/0.43    inference(avatar_component_clause,[],[f56])).
% 0.20/0.43  fof(f93,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r2_orders_2(X0,X1,X2) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) ) | ~spl3_13),
% 0.20/0.43    inference(avatar_component_clause,[],[f92])).
% 0.20/0.43  fof(f94,plain,(
% 0.20/0.43    spl3_13),
% 0.20/0.43    inference(avatar_split_clause,[],[f32,f92])).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (r2_orders_2(X0,X1,X2) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f20])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2)) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.43    inference(flattening,[],[f19])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | (~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2))) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.43    inference(nnf_transformation,[],[f13])).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.43    inference(flattening,[],[f12])).
% 0.20/0.43  fof(f12,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).
% 0.20/0.43  fof(f82,plain,(
% 0.20/0.43    spl3_10),
% 0.20/0.43    inference(avatar_split_clause,[],[f30,f80])).
% 0.20/0.43  fof(f30,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f18])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | ~r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))) & (r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.43    inference(nnf_transformation,[],[f11])).
% 0.20/0.43  fof(f11,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.43    inference(flattening,[],[f10])).
% 0.20/0.43  fof(f10,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_orders_2)).
% 0.20/0.43  fof(f78,plain,(
% 0.20/0.43    spl3_9),
% 0.20/0.43    inference(avatar_split_clause,[],[f29,f76])).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f9])).
% 0.20/0.43  fof(f9,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (~r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.43    inference(flattening,[],[f8])).
% 0.20/0.43  fof(f8,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (~r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_orders_2)).
% 0.20/0.43  fof(f74,plain,(
% 0.20/0.43    spl3_8),
% 0.20/0.43    inference(avatar_split_clause,[],[f28,f71])).
% 0.20/0.43  fof(f28,plain,(
% 0.20/0.43    r2_hidden(sK1,k3_orders_2(sK0,sK2,sK1))),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    ((r2_hidden(sK1,k3_orders_2(sK0,sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f16,f15,f14])).
% 0.20/0.43  fof(f14,plain,(
% 0.20/0.43    ? [X0] : (? [X1] : (? [X2] : (r2_hidden(X1,k3_orders_2(X0,X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (r2_hidden(X1,k3_orders_2(sK0,X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    ? [X1] : (? [X2] : (r2_hidden(X1,k3_orders_2(sK0,X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (r2_hidden(sK1,k3_orders_2(sK0,X2,sK1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    ? [X2] : (r2_hidden(sK1,k3_orders_2(sK0,X2,sK1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (r2_hidden(sK1,k3_orders_2(sK0,sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f7,plain,(
% 0.20/0.43    ? [X0] : (? [X1] : (? [X2] : (r2_hidden(X1,k3_orders_2(X0,X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.43    inference(flattening,[],[f6])).
% 0.20/0.43  fof(f6,plain,(
% 0.20/0.43    ? [X0] : (? [X1] : (? [X2] : (r2_hidden(X1,k3_orders_2(X0,X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,negated_conjecture,(
% 0.20/0.43    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~r2_hidden(X1,k3_orders_2(X0,X2,X1)))))),
% 0.20/0.43    inference(negated_conjecture,[],[f4])).
% 0.20/0.43  fof(f4,conjecture,(
% 0.20/0.43    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~r2_hidden(X1,k3_orders_2(X0,X2,X1)))))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_orders_2)).
% 0.20/0.43  fof(f69,plain,(
% 0.20/0.43    spl3_7),
% 0.20/0.43    inference(avatar_split_clause,[],[f27,f66])).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f64,plain,(
% 0.20/0.43    spl3_6),
% 0.20/0.43    inference(avatar_split_clause,[],[f26,f61])).
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f59,plain,(
% 0.20/0.43    spl3_5),
% 0.20/0.43    inference(avatar_split_clause,[],[f25,f56])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    l1_orders_2(sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f54,plain,(
% 0.20/0.43    spl3_4),
% 0.20/0.43    inference(avatar_split_clause,[],[f24,f51])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    v5_orders_2(sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f49,plain,(
% 0.20/0.43    spl3_3),
% 0.20/0.43    inference(avatar_split_clause,[],[f23,f46])).
% 0.20/0.43  fof(f23,plain,(
% 0.20/0.43    v4_orders_2(sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f44,plain,(
% 0.20/0.43    spl3_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f22,f41])).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    v3_orders_2(sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f39,plain,(
% 0.20/0.43    ~spl3_1),
% 0.20/0.43    inference(avatar_split_clause,[],[f21,f36])).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    ~v2_struct_0(sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (21836)------------------------------
% 0.20/0.43  % (21836)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (21836)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (21836)Memory used [KB]: 5373
% 0.20/0.43  % (21836)Time elapsed: 0.035 s
% 0.20/0.43  % (21836)------------------------------
% 0.20/0.43  % (21836)------------------------------
% 0.20/0.43  % (21819)Success in time 0.08 s
%------------------------------------------------------------------------------
