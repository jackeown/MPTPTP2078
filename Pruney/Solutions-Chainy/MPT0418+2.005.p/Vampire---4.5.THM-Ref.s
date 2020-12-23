%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 120 expanded)
%              Number of leaves         :   14 (  49 expanded)
%              Depth                    :   13
%              Number of atoms          :  256 ( 546 expanded)
%              Number of equality atoms :   15 (  31 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f90,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f42,f46,f50,f60,f62,f73,f85,f89])).

fof(f89,plain,
    ( ~ spl4_4
    | spl4_2
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f88,f71,f37,f48])).

fof(f48,plain,
    ( spl4_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f37,plain,
    ( spl4_2
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f71,plain,
    ( spl4_7
  <=> r2_hidden(sK2,k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f88,plain,
    ( r2_hidden(sK2,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_7 ),
    inference(superposition,[],[f72,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(f72,plain,
    ( r2_hidden(sK2,k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f71])).

fof(f85,plain,
    ( ~ spl4_4
    | spl4_6 ),
    inference(avatar_split_clause,[],[f83,f67,f48])).

fof(f67,plain,
    ( spl4_6
  <=> m1_subset_1(k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f83,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl4_6 ),
    inference(duplicate_literal_removal,[],[f82])).

fof(f82,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl4_6 ),
    inference(superposition,[],[f68,f24])).

fof(f68,plain,
    ( ~ m1_subset_1(k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f67])).

fof(f73,plain,
    ( ~ spl4_5
    | ~ spl4_6
    | ~ spl4_3
    | spl4_7
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f63,f34,f71,f44,f67,f57])).

fof(f57,plain,
    ( spl4_5
  <=> m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f44,plain,
    ( spl4_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f34,plain,
    ( spl4_1
  <=> r2_hidden(k3_subset_1(sK0,sK2),k7_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f63,plain,
    ( r2_hidden(sK2,k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_1 ),
    inference(resolution,[],[f40,f31])).

fof(f31,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(k3_subset_1(X0,X4),X1)
      | r2_hidden(X4,k7_setfam_1(X0,X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | k7_setfam_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k3_subset_1(X0,sK3(X0,X1,X2)),X1)
                  | ~ r2_hidden(sK3(X0,X1,X2),X2) )
                & ( r2_hidden(k3_subset_1(X0,sK3(X0,X1,X2)),X1)
                  | r2_hidden(sK3(X0,X1,X2),X2) )
                & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(X0)) ) )
            & ( ! [X4] :
                  ( ( ( r2_hidden(X4,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X4),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X4),X1)
                      | ~ r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(k3_subset_1(X0,X3),X1)
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,k1_zfmisc_1(X0)) )
     => ( ( ~ r2_hidden(k3_subset_1(X0,sK3(X0,X1,X2)),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( r2_hidden(k3_subset_1(X0,sK3(X0,X1,X2)),X1)
          | r2_hidden(sK3(X0,X1,X2),X2) )
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ? [X3] :
                  ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(k3_subset_1(X0,X3),X1)
                    | r2_hidden(X3,X2) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
            & ( ! [X4] :
                  ( ( ( r2_hidden(X4,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X4),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X4),X1)
                      | ~ r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ? [X3] :
                  ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(k3_subset_1(X0,X3),X1)
                    | r2_hidden(X3,X2) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
            & ( ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X3),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X3),X1)
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ? [X3] :
                  ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(k3_subset_1(X0,X3),X1)
                    | r2_hidden(X3,X2) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
            & ( ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X3),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X3),X1)
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).

fof(f40,plain,
    ( r2_hidden(k3_subset_1(sK0,sK2),k7_setfam_1(sK0,sK1))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f62,plain,
    ( ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f61,f57,f48])).

fof(f61,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl4_5 ),
    inference(resolution,[],[f58,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f58,plain,
    ( ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f57])).

fof(f60,plain,
    ( ~ spl4_5
    | ~ spl4_4
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f55,f44,f37,f34,f48,f57])).

fof(f55,plain,
    ( r2_hidden(k3_subset_1(sK0,sK2),k7_setfam_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(resolution,[],[f54,f45])).

fof(f45,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f54,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | r2_hidden(k3_subset_1(X0,sK2),k7_setfam_1(X0,sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | ~ m1_subset_1(k7_setfam_1(X0,sK1),k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl4_2 ),
    inference(resolution,[],[f53,f41])).

fof(f41,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(duplicate_literal_removal,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(superposition,[],[f32,f24])).

fof(f32,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k7_setfam_1(X0,X1))
      | r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | k7_setfam_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f50,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f20,f48])).

fof(f20,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ( ~ r2_hidden(sK2,sK1)
      | ~ r2_hidden(k3_subset_1(sK0,sK2),k7_setfam_1(sK0,sK1)) )
    & ( r2_hidden(sK2,sK1)
      | r2_hidden(k3_subset_1(sK0,sK2),k7_setfam_1(sK0,sK1)) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13,f12])).

fof(f12,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r2_hidden(X2,X1)
              | ~ r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) )
            & ( r2_hidden(X2,X1)
              | r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( ( ~ r2_hidden(X2,sK1)
            | ~ r2_hidden(k3_subset_1(sK0,X2),k7_setfam_1(sK0,sK1)) )
          & ( r2_hidden(X2,sK1)
            | r2_hidden(k3_subset_1(sK0,X2),k7_setfam_1(sK0,sK1)) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X2] :
        ( ( ~ r2_hidden(X2,sK1)
          | ~ r2_hidden(k3_subset_1(sK0,X2),k7_setfam_1(sK0,sK1)) )
        & ( r2_hidden(X2,sK1)
          | r2_hidden(k3_subset_1(sK0,X2),k7_setfam_1(sK0,sK1)) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ( ~ r2_hidden(sK2,sK1)
        | ~ r2_hidden(k3_subset_1(sK0,sK2),k7_setfam_1(sK0,sK1)) )
      & ( r2_hidden(sK2,sK1)
        | r2_hidden(k3_subset_1(sK0,sK2),k7_setfam_1(sK0,sK1)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
          <~> r2_hidden(X2,X1) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
            <=> r2_hidden(X2,X1) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
          <=> r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_setfam_1)).

fof(f46,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f21,f44])).

fof(f21,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f42,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f22,f37,f34])).

fof(f22,plain,
    ( r2_hidden(sK2,sK1)
    | r2_hidden(k3_subset_1(sK0,sK2),k7_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f39,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f23,f37,f34])).

fof(f23,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ r2_hidden(k3_subset_1(sK0,sK2),k7_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:23:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.43  % (24974)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.43  % (24974)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f90,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f39,f42,f46,f50,f60,f62,f73,f85,f89])).
% 0.21/0.43  fof(f89,plain,(
% 0.21/0.43    ~spl4_4 | spl4_2 | ~spl4_7),
% 0.21/0.43    inference(avatar_split_clause,[],[f88,f71,f37,f48])).
% 0.21/0.43  fof(f48,plain,(
% 0.21/0.43    spl4_4 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.43  fof(f37,plain,(
% 0.21/0.43    spl4_2 <=> r2_hidden(sK2,sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.43  fof(f71,plain,(
% 0.21/0.43    spl4_7 <=> r2_hidden(sK2,k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.43  fof(f88,plain,(
% 0.21/0.43    r2_hidden(sK2,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl4_7),
% 0.21/0.43    inference(superposition,[],[f72,f24])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,plain,(
% 0.21/0.43    ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.43    inference(ennf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).
% 0.21/0.43  fof(f72,plain,(
% 0.21/0.43    r2_hidden(sK2,k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))) | ~spl4_7),
% 0.21/0.43    inference(avatar_component_clause,[],[f71])).
% 0.21/0.43  fof(f85,plain,(
% 0.21/0.43    ~spl4_4 | spl4_6),
% 0.21/0.43    inference(avatar_split_clause,[],[f83,f67,f48])).
% 0.21/0.43  fof(f67,plain,(
% 0.21/0.43    spl4_6 <=> m1_subset_1(k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.43  fof(f83,plain,(
% 0.21/0.43    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl4_6),
% 0.21/0.43    inference(duplicate_literal_removal,[],[f82])).
% 0.21/0.43  fof(f82,plain,(
% 0.21/0.43    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl4_6),
% 0.21/0.43    inference(superposition,[],[f68,f24])).
% 0.21/0.43  fof(f68,plain,(
% 0.21/0.43    ~m1_subset_1(k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl4_6),
% 0.21/0.43    inference(avatar_component_clause,[],[f67])).
% 0.21/0.43  fof(f73,plain,(
% 0.21/0.43    ~spl4_5 | ~spl4_6 | ~spl4_3 | spl4_7 | ~spl4_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f63,f34,f71,f44,f67,f57])).
% 0.21/0.43  fof(f57,plain,(
% 0.21/0.43    spl4_5 <=> m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.43  fof(f44,plain,(
% 0.21/0.43    spl4_3 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    spl4_1 <=> r2_hidden(k3_subset_1(sK0,sK2),k7_setfam_1(sK0,sK1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.43  fof(f63,plain,(
% 0.21/0.43    r2_hidden(sK2,k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~m1_subset_1(k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl4_1),
% 0.21/0.43    inference(resolution,[],[f40,f31])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    ( ! [X4,X0,X1] : (~r2_hidden(k3_subset_1(X0,X4),X1) | r2_hidden(X4,k7_setfam_1(X0,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(X0)) | ~m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.43    inference(equality_resolution,[],[f27])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(k3_subset_1(X0,X4),X1) | ~m1_subset_1(X4,k1_zfmisc_1(X0)) | k7_setfam_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f19])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ((~r2_hidden(k3_subset_1(X0,sK3(X0,X1,X2)),X1) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(k3_subset_1(X0,sK3(X0,X1,X2)),X1) | r2_hidden(sK3(X0,X1,X2),X2)) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(X0)))) & (! [X4] : (((r2_hidden(X4,X2) | ~r2_hidden(k3_subset_1(X0,X4),X1)) & (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0))) => ((~r2_hidden(k3_subset_1(X0,sK3(X0,X1,X2)),X1) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(k3_subset_1(X0,sK3(X0,X1,X2)),X1) | r2_hidden(sK3(X0,X1,X2),X2)) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(X0))))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X4] : (((r2_hidden(X4,X2) | ~r2_hidden(k3_subset_1(X0,X4),X1)) & (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.43    inference(rectify,[],[f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(k3_subset_1(X0,X3),X1)) & (r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.43    inference(flattening,[],[f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(k3_subset_1(X0,X3),X1)) & (r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.43    inference(nnf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ! [X0,X1] : (! [X2] : ((k7_setfam_1(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.43    inference(ennf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k7_setfam_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1))))))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    r2_hidden(k3_subset_1(sK0,sK2),k7_setfam_1(sK0,sK1)) | ~spl4_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f34])).
% 0.21/0.43  fof(f62,plain,(
% 0.21/0.43    ~spl4_4 | spl4_5),
% 0.21/0.43    inference(avatar_split_clause,[],[f61,f57,f48])).
% 0.21/0.43  fof(f61,plain,(
% 0.21/0.43    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl4_5),
% 0.21/0.43    inference(resolution,[],[f58,f25])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ( ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,plain,(
% 0.21/0.43    ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.43    inference(ennf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).
% 0.21/0.43  fof(f58,plain,(
% 0.21/0.43    ~m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl4_5),
% 0.21/0.43    inference(avatar_component_clause,[],[f57])).
% 0.21/0.43  fof(f60,plain,(
% 0.21/0.43    ~spl4_5 | ~spl4_4 | spl4_1 | ~spl4_2 | ~spl4_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f55,f44,f37,f34,f48,f57])).
% 0.21/0.43  fof(f55,plain,(
% 0.21/0.43    r2_hidden(k3_subset_1(sK0,sK2),k7_setfam_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) | (~spl4_2 | ~spl4_3)),
% 0.21/0.43    inference(resolution,[],[f54,f45])).
% 0.21/0.43  fof(f45,plain,(
% 0.21/0.43    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl4_3),
% 0.21/0.43    inference(avatar_component_clause,[],[f44])).
% 0.21/0.43  fof(f54,plain,(
% 0.21/0.43    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | r2_hidden(k3_subset_1(X0,sK2),k7_setfam_1(X0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(k7_setfam_1(X0,sK1),k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | ~spl4_2),
% 0.21/0.43    inference(resolution,[],[f53,f41])).
% 0.21/0.43  fof(f41,plain,(
% 0.21/0.43    r2_hidden(sK2,sK1) | ~spl4_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f37])).
% 0.21/0.43  fof(f53,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.43    inference(duplicate_literal_removal,[],[f52])).
% 0.21/0.43  fof(f52,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.43    inference(superposition,[],[f32,f24])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    ( ! [X4,X0,X1] : (~r2_hidden(X4,k7_setfam_1(X0,X1)) | r2_hidden(k3_subset_1(X0,X4),X1) | ~m1_subset_1(X4,k1_zfmisc_1(X0)) | ~m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.43    inference(equality_resolution,[],[f26])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    ( ! [X4,X2,X0,X1] : (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,k1_zfmisc_1(X0)) | k7_setfam_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f19])).
% 0.21/0.43  fof(f50,plain,(
% 0.21/0.43    spl4_4),
% 0.21/0.43    inference(avatar_split_clause,[],[f20,f48])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ((~r2_hidden(sK2,sK1) | ~r2_hidden(k3_subset_1(sK0,sK2),k7_setfam_1(sK0,sK1))) & (r2_hidden(sK2,sK1) | r2_hidden(k3_subset_1(sK0,sK2),k7_setfam_1(sK0,sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13,f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ? [X0,X1] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))) & (r2_hidden(X2,X1) | r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : ((~r2_hidden(X2,sK1) | ~r2_hidden(k3_subset_1(sK0,X2),k7_setfam_1(sK0,sK1))) & (r2_hidden(X2,sK1) | r2_hidden(k3_subset_1(sK0,X2),k7_setfam_1(sK0,sK1))) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ? [X2] : ((~r2_hidden(X2,sK1) | ~r2_hidden(k3_subset_1(sK0,X2),k7_setfam_1(sK0,sK1))) & (r2_hidden(X2,sK1) | r2_hidden(k3_subset_1(sK0,X2),k7_setfam_1(sK0,sK1))) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => ((~r2_hidden(sK2,sK1) | ~r2_hidden(k3_subset_1(sK0,sK2),k7_setfam_1(sK0,sK1))) & (r2_hidden(sK2,sK1) | r2_hidden(k3_subset_1(sK0,sK2),k7_setfam_1(sK0,sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ? [X0,X1] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))) & (r2_hidden(X2,X1) | r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.43    inference(flattening,[],[f10])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ? [X0,X1] : (? [X2] : (((~r2_hidden(X2,X1) | ~r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))) & (r2_hidden(X2,X1) | r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.43    inference(nnf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,plain,(
% 0.21/0.43    ? [X0,X1] : (? [X2] : ((r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) <~> r2_hidden(X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.43    inference(ennf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) <=> r2_hidden(X2,X1))))),
% 0.21/0.43    inference(negated_conjecture,[],[f4])).
% 0.21/0.43  fof(f4,conjecture,(
% 0.21/0.43    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) <=> r2_hidden(X2,X1))))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_setfam_1)).
% 0.21/0.43  fof(f46,plain,(
% 0.21/0.43    spl4_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f21,f44])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  fof(f42,plain,(
% 0.21/0.43    spl4_1 | spl4_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f22,f37,f34])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    r2_hidden(sK2,sK1) | r2_hidden(k3_subset_1(sK0,sK2),k7_setfam_1(sK0,sK1))),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    ~spl4_1 | ~spl4_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f23,f37,f34])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ~r2_hidden(sK2,sK1) | ~r2_hidden(k3_subset_1(sK0,sK2),k7_setfam_1(sK0,sK1))),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (24974)------------------------------
% 0.21/0.43  % (24974)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (24974)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (24974)Memory used [KB]: 10618
% 0.21/0.43  % (24974)Time elapsed: 0.029 s
% 0.21/0.43  % (24974)------------------------------
% 0.21/0.43  % (24974)------------------------------
% 0.21/0.44  % (24967)Success in time 0.078 s
%------------------------------------------------------------------------------
