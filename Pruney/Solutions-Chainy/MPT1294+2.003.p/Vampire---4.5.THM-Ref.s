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
% DateTime   : Thu Dec  3 13:13:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 207 expanded)
%              Number of leaves         :   22 (  85 expanded)
%              Depth                    :   12
%              Number of atoms          :  377 ( 908 expanded)
%              Number of equality atoms :   92 ( 224 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f177,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f53,f57,f62,f72,f76,f102,f106,f117,f128,f144,f157,f173,f175,f176])).

fof(f176,plain,
    ( k1_xboole_0 != k7_setfam_1(sK0,k1_xboole_0)
    | sK1 != k7_setfam_1(sK0,k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f175,plain,(
    ~ spl3_16 ),
    inference(avatar_contradiction_clause,[],[f174])).

fof(f174,plain,
    ( $false
    | ~ spl3_16 ),
    inference(resolution,[],[f156,f63])).

fof(f63,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f26,f39])).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f26,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f156,plain,
    ( r2_hidden(sK2(sK0,k7_setfam_1(sK0,k1_xboole_0),k7_setfam_1(sK0,k1_xboole_0)),k1_xboole_0)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl3_16
  <=> r2_hidden(sK2(sK0,k7_setfam_1(sK0,k1_xboole_0),k7_setfam_1(sK0,k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f173,plain,
    ( ~ spl3_11
    | spl3_3
    | ~ spl3_10
    | spl3_15 ),
    inference(avatar_split_clause,[],[f172,f152,f100,f51,f104])).

fof(f104,plain,
    ( spl3_11
  <=> m1_subset_1(k7_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f51,plain,
    ( spl3_3
  <=> k1_xboole_0 = k7_setfam_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f100,plain,
    ( spl3_10
  <=> k1_xboole_0 = k7_setfam_1(sK0,k7_setfam_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f152,plain,
    ( spl3_15
  <=> m1_subset_1(sK2(sK0,k7_setfam_1(sK0,k1_xboole_0),k7_setfam_1(sK0,k1_xboole_0)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f172,plain,
    ( k1_xboole_0 = k7_setfam_1(sK0,k1_xboole_0)
    | ~ m1_subset_1(k7_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_10
    | spl3_15 ),
    inference(forward_demodulation,[],[f171,f101])).

fof(f101,plain,
    ( k1_xboole_0 = k7_setfam_1(sK0,k7_setfam_1(sK0,k1_xboole_0))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f100])).

fof(f171,plain,
    ( k7_setfam_1(sK0,k1_xboole_0) = k7_setfam_1(sK0,k7_setfam_1(sK0,k1_xboole_0))
    | ~ m1_subset_1(k7_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl3_15 ),
    inference(duplicate_literal_removal,[],[f170])).

fof(f170,plain,
    ( k7_setfam_1(sK0,k1_xboole_0) = k7_setfam_1(sK0,k7_setfam_1(sK0,k1_xboole_0))
    | ~ m1_subset_1(k7_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(k7_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl3_15 ),
    inference(resolution,[],[f153,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(X0))
      | k7_setfam_1(X0,X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1)
                  | ~ r2_hidden(sK2(X0,X1,X2),X2) )
                & ( r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1)
                  | r2_hidden(sK2(X0,X1,X2),X2) )
                & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(X0)) ) )
            & ( ! [X4] :
                  ( ( ( r2_hidden(X4,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X4),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X4),X1)
                      | ~ r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f17])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(k3_subset_1(X0,X3),X1)
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,k1_zfmisc_1(X0)) )
     => ( ( ~ r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1)
          | r2_hidden(sK2(X0,X1,X2),X2) )
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

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
            & ( ! [X4] :
                  ( ( ( r2_hidden(X4,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X4),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X4),X1)
                      | ~ r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(rectify,[],[f15])).

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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f153,plain,
    ( ~ m1_subset_1(sK2(sK0,k7_setfam_1(sK0,k1_xboole_0),k7_setfam_1(sK0,k1_xboole_0)),k1_zfmisc_1(sK0))
    | spl3_15 ),
    inference(avatar_component_clause,[],[f152])).

fof(f157,plain,
    ( ~ spl3_11
    | ~ spl3_15
    | spl3_16
    | ~ spl3_5
    | ~ spl3_10
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f150,f141,f100,f60,f155,f152,f104])).

fof(f60,plain,
    ( spl3_5
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f141,plain,
    ( spl3_14
  <=> r2_hidden(k3_subset_1(sK0,sK2(sK0,k7_setfam_1(sK0,k1_xboole_0),k7_setfam_1(sK0,k1_xboole_0))),k7_setfam_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f150,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | r2_hidden(sK2(sK0,k7_setfam_1(sK0,k1_xboole_0),k7_setfam_1(sK0,k1_xboole_0)),k1_xboole_0)
    | ~ m1_subset_1(sK2(sK0,k7_setfam_1(sK0,k1_xboole_0),k7_setfam_1(sK0,k1_xboole_0)),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k7_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_10
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f149,f101])).

fof(f149,plain,
    ( r2_hidden(sK2(sK0,k7_setfam_1(sK0,k1_xboole_0),k7_setfam_1(sK0,k1_xboole_0)),k1_xboole_0)
    | ~ m1_subset_1(sK2(sK0,k7_setfam_1(sK0,k1_xboole_0),k7_setfam_1(sK0,k1_xboole_0)),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k7_setfam_1(sK0,k7_setfam_1(sK0,k1_xboole_0)),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(k7_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_10
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f145,f101])).

fof(f145,plain,
    ( r2_hidden(sK2(sK0,k7_setfam_1(sK0,k1_xboole_0),k7_setfam_1(sK0,k1_xboole_0)),k7_setfam_1(sK0,k7_setfam_1(sK0,k1_xboole_0)))
    | ~ m1_subset_1(sK2(sK0,k7_setfam_1(sK0,k1_xboole_0),k7_setfam_1(sK0,k1_xboole_0)),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k7_setfam_1(sK0,k7_setfam_1(sK0,k1_xboole_0)),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(k7_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_14 ),
    inference(resolution,[],[f142,f37])).

fof(f37,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(k3_subset_1(X0,X4),X1)
      | r2_hidden(X4,k7_setfam_1(X0,X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | k7_setfam_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f142,plain,
    ( r2_hidden(k3_subset_1(sK0,sK2(sK0,k7_setfam_1(sK0,k1_xboole_0),k7_setfam_1(sK0,k1_xboole_0))),k7_setfam_1(sK0,k1_xboole_0))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f141])).

fof(f144,plain,
    ( spl3_14
    | spl3_3
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f139,f126,f104,f100,f51,f141])).

% (23434)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
fof(f126,plain,
    ( spl3_13
  <=> ! [X0] :
        ( r2_hidden(k3_subset_1(sK0,sK2(sK0,X0,k7_setfam_1(sK0,k1_xboole_0))),X0)
        | k7_setfam_1(sK0,k1_xboole_0) = k7_setfam_1(sK0,X0)
        | r2_hidden(k3_subset_1(sK0,sK2(sK0,X0,k7_setfam_1(sK0,k1_xboole_0))),k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f139,plain,
    ( k1_xboole_0 = k7_setfam_1(sK0,k1_xboole_0)
    | r2_hidden(k3_subset_1(sK0,sK2(sK0,k7_setfam_1(sK0,k1_xboole_0),k7_setfam_1(sK0,k1_xboole_0))),k7_setfam_1(sK0,k1_xboole_0))
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f136,f101])).

fof(f136,plain,
    ( r2_hidden(k3_subset_1(sK0,sK2(sK0,k7_setfam_1(sK0,k1_xboole_0),k7_setfam_1(sK0,k1_xboole_0))),k7_setfam_1(sK0,k1_xboole_0))
    | k7_setfam_1(sK0,k1_xboole_0) = k7_setfam_1(sK0,k7_setfam_1(sK0,k1_xboole_0))
    | ~ spl3_11
    | ~ spl3_13 ),
    inference(resolution,[],[f131,f105])).

fof(f105,plain,
    ( m1_subset_1(k7_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f104])).

fof(f131,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | r2_hidden(k3_subset_1(sK0,sK2(sK0,X1,k7_setfam_1(sK0,k1_xboole_0))),X1)
        | k7_setfam_1(sK0,k1_xboole_0) = k7_setfam_1(sK0,X1) )
    | ~ spl3_13 ),
    inference(resolution,[],[f127,f63])).

fof(f127,plain,
    ( ! [X0] :
        ( r2_hidden(k3_subset_1(sK0,sK2(sK0,X0,k7_setfam_1(sK0,k1_xboole_0))),k1_xboole_0)
        | k7_setfam_1(sK0,k1_xboole_0) = k7_setfam_1(sK0,X0)
        | r2_hidden(k3_subset_1(sK0,sK2(sK0,X0,k7_setfam_1(sK0,k1_xboole_0))),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f126])).

fof(f128,plain,
    ( ~ spl3_11
    | spl3_13
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f123,f115,f104,f126,f104])).

fof(f115,plain,
    ( spl3_12
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k7_setfam_1(sK0,k1_xboole_0))
        | r2_hidden(k3_subset_1(sK0,X0),k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f123,plain,
    ( ! [X0] :
        ( r2_hidden(k3_subset_1(sK0,sK2(sK0,X0,k7_setfam_1(sK0,k1_xboole_0))),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | r2_hidden(k3_subset_1(sK0,sK2(sK0,X0,k7_setfam_1(sK0,k1_xboole_0))),k1_xboole_0)
        | k7_setfam_1(sK0,k1_xboole_0) = k7_setfam_1(sK0,X0)
        | ~ m1_subset_1(k7_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) )
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(duplicate_literal_removal,[],[f122])).

fof(f122,plain,
    ( ! [X0] :
        ( r2_hidden(k3_subset_1(sK0,sK2(sK0,X0,k7_setfam_1(sK0,k1_xboole_0))),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | r2_hidden(k3_subset_1(sK0,sK2(sK0,X0,k7_setfam_1(sK0,k1_xboole_0))),k1_xboole_0)
        | k7_setfam_1(sK0,k1_xboole_0) = k7_setfam_1(sK0,X0)
        | k7_setfam_1(sK0,k1_xboole_0) = k7_setfam_1(sK0,X0)
        | ~ m1_subset_1(k7_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(resolution,[],[f121,f31])).

fof(f121,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2(sK0,X0,k7_setfam_1(sK0,k1_xboole_0)),k1_zfmisc_1(sK0))
        | r2_hidden(k3_subset_1(sK0,sK2(sK0,X0,k7_setfam_1(sK0,k1_xboole_0))),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | r2_hidden(k3_subset_1(sK0,sK2(sK0,X0,k7_setfam_1(sK0,k1_xboole_0))),k1_xboole_0)
        | k7_setfam_1(sK0,k1_xboole_0) = k7_setfam_1(sK0,X0) )
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(resolution,[],[f120,f105])).

fof(f120,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(k7_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X2)))
        | k7_setfam_1(sK0,k1_xboole_0) = k7_setfam_1(X2,X3)
        | r2_hidden(k3_subset_1(X2,sK2(X2,X3,k7_setfam_1(sK0,k1_xboole_0))),X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
        | r2_hidden(k3_subset_1(sK0,sK2(X2,X3,k7_setfam_1(sK0,k1_xboole_0))),k1_xboole_0)
        | ~ m1_subset_1(sK2(X2,X3,k7_setfam_1(sK0,k1_xboole_0)),k1_zfmisc_1(sK0)) )
    | ~ spl3_12 ),
    inference(resolution,[],[f32,f116])).

fof(f116,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k7_setfam_1(sK0,k1_xboole_0))
        | r2_hidden(k3_subset_1(sK0,X0),k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f115])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1)
      | k7_setfam_1(X0,X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f117,plain,
    ( ~ spl3_5
    | spl3_12
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f111,f104,f115,f60])).

fof(f111,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k7_setfam_1(sK0,k1_xboole_0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | r2_hidden(k3_subset_1(sK0,X0),k1_xboole_0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
    | ~ spl3_11 ),
    inference(resolution,[],[f105,f38])).

fof(f38,plain,(
    ! [X4,X0,X1] :
      ( ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ r2_hidden(X4,k7_setfam_1(X0,X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | k7_setfam_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f106,plain,
    ( spl3_11
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f77,f60,f104])).

fof(f77,plain,
    ( m1_subset_1(k7_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_5 ),
    inference(resolution,[],[f61,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f61,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f60])).

fof(f102,plain,
    ( spl3_10
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f78,f60,f100])).

fof(f78,plain,
    ( k1_xboole_0 = k7_setfam_1(sK0,k7_setfam_1(sK0,k1_xboole_0))
    | ~ spl3_5 ),
    inference(resolution,[],[f61,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(f76,plain,
    ( spl3_5
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f75,f55,f42,f60])).

fof(f42,plain,
    ( spl3_1
  <=> k1_xboole_0 = k7_setfam_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f55,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f75,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f74,f43])).

fof(f43,plain,
    ( k1_xboole_0 = k7_setfam_1(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f74,plain,
    ( m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_4 ),
    inference(resolution,[],[f28,f56])).

fof(f56,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f55])).

fof(f72,plain,
    ( spl3_6
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f68,f55,f42,f70])).

fof(f70,plain,
    ( spl3_6
  <=> sK1 = k7_setfam_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f68,plain,
    ( sK1 = k7_setfam_1(sK0,k1_xboole_0)
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f67,f43])).

fof(f67,plain,
    ( sK1 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))
    | ~ spl3_4 ),
    inference(resolution,[],[f27,f56])).

fof(f62,plain,
    ( spl3_5
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f58,f55,f45,f60])).

fof(f45,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f58,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(superposition,[],[f56,f46])).

fof(f46,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f57,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f21,f55])).

fof(f21,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ( ( k1_xboole_0 = sK1
        & k1_xboole_0 != k7_setfam_1(sK0,sK1) )
      | ( k1_xboole_0 = k7_setfam_1(sK0,sK1)
        & k1_xboole_0 != sK1 ) )
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f12])).

fof(f12,plain,
    ( ? [X0,X1] :
        ( ( ( k1_xboole_0 = X1
            & k1_xboole_0 != k7_setfam_1(X0,X1) )
          | ( k1_xboole_0 = k7_setfam_1(X0,X1)
            & k1_xboole_0 != X1 ) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ( ( k1_xboole_0 = sK1
          & k1_xboole_0 != k7_setfam_1(sK0,sK1) )
        | ( k1_xboole_0 = k7_setfam_1(sK0,sK1)
          & k1_xboole_0 != sK1 ) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 = X1
          & k1_xboole_0 != k7_setfam_1(X0,X1) )
        | ( k1_xboole_0 = k7_setfam_1(X0,X1)
          & k1_xboole_0 != X1 ) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( ~ ( k1_xboole_0 = X1
              & k1_xboole_0 != k7_setfam_1(X0,X1) )
          & ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
              & k1_xboole_0 != X1 ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ~ ( k1_xboole_0 = X1
            & k1_xboole_0 != k7_setfam_1(X0,X1) )
        & ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
            & k1_xboole_0 != X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tops_2)).

fof(f53,plain,
    ( ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f48,f51,f45])).

fof(f48,plain,
    ( k1_xboole_0 != k7_setfam_1(sK0,k1_xboole_0)
    | k1_xboole_0 != sK1 ),
    inference(inner_rewriting,[],[f22])).

fof(f22,plain,
    ( k1_xboole_0 != k7_setfam_1(sK0,sK1)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f13])).

fof(f47,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f25,f45,f42])).

fof(f25,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = k7_setfam_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n003.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:18:42 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.47  % (23426)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (23427)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (23427)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (23435)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f177,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f47,f53,f57,f62,f72,f76,f102,f106,f117,f128,f144,f157,f173,f175,f176])).
% 0.21/0.48  fof(f176,plain,(
% 0.21/0.48    k1_xboole_0 != k7_setfam_1(sK0,k1_xboole_0) | sK1 != k7_setfam_1(sK0,k1_xboole_0) | k1_xboole_0 = sK1),
% 0.21/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.48  fof(f175,plain,(
% 0.21/0.48    ~spl3_16),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f174])).
% 0.21/0.48  fof(f174,plain,(
% 0.21/0.48    $false | ~spl3_16),
% 0.21/0.48    inference(resolution,[],[f156,f63])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.48    inference(superposition,[],[f26,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.48    inference(flattening,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.48    inference(nnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.21/0.48  fof(f156,plain,(
% 0.21/0.48    r2_hidden(sK2(sK0,k7_setfam_1(sK0,k1_xboole_0),k7_setfam_1(sK0,k1_xboole_0)),k1_xboole_0) | ~spl3_16),
% 0.21/0.48    inference(avatar_component_clause,[],[f155])).
% 0.21/0.48  fof(f155,plain,(
% 0.21/0.48    spl3_16 <=> r2_hidden(sK2(sK0,k7_setfam_1(sK0,k1_xboole_0),k7_setfam_1(sK0,k1_xboole_0)),k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.48  fof(f173,plain,(
% 0.21/0.48    ~spl3_11 | spl3_3 | ~spl3_10 | spl3_15),
% 0.21/0.48    inference(avatar_split_clause,[],[f172,f152,f100,f51,f104])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    spl3_11 <=> m1_subset_1(k7_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    spl3_3 <=> k1_xboole_0 = k7_setfam_1(sK0,k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    spl3_10 <=> k1_xboole_0 = k7_setfam_1(sK0,k7_setfam_1(sK0,k1_xboole_0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.48  fof(f152,plain,(
% 0.21/0.48    spl3_15 <=> m1_subset_1(sK2(sK0,k7_setfam_1(sK0,k1_xboole_0),k7_setfam_1(sK0,k1_xboole_0)),k1_zfmisc_1(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.48  fof(f172,plain,(
% 0.21/0.48    k1_xboole_0 = k7_setfam_1(sK0,k1_xboole_0) | ~m1_subset_1(k7_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) | (~spl3_10 | spl3_15)),
% 0.21/0.48    inference(forward_demodulation,[],[f171,f101])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    k1_xboole_0 = k7_setfam_1(sK0,k7_setfam_1(sK0,k1_xboole_0)) | ~spl3_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f100])).
% 0.21/0.48  fof(f171,plain,(
% 0.21/0.48    k7_setfam_1(sK0,k1_xboole_0) = k7_setfam_1(sK0,k7_setfam_1(sK0,k1_xboole_0)) | ~m1_subset_1(k7_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl3_15),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f170])).
% 0.21/0.48  fof(f170,plain,(
% 0.21/0.48    k7_setfam_1(sK0,k1_xboole_0) = k7_setfam_1(sK0,k7_setfam_1(sK0,k1_xboole_0)) | ~m1_subset_1(k7_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(k7_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl3_15),
% 0.21/0.48    inference(resolution,[],[f153,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(X0)) | k7_setfam_1(X0,X1) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ((~r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1) | r2_hidden(sK2(X0,X1,X2),X2)) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(X0)))) & (! [X4] : (((r2_hidden(X4,X2) | ~r2_hidden(k3_subset_1(X0,X4),X1)) & (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0))) => ((~r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1) | r2_hidden(sK2(X0,X1,X2),X2)) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(X0))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X4] : (((r2_hidden(X4,X2) | ~r2_hidden(k3_subset_1(X0,X4),X1)) & (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.48    inference(rectify,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(k3_subset_1(X0,X3),X1)) & (r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.48    inference(flattening,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(k3_subset_1(X0,X3),X1)) & (r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.48    inference(nnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : ((k7_setfam_1(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k7_setfam_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1))))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).
% 0.21/0.48  fof(f153,plain,(
% 0.21/0.48    ~m1_subset_1(sK2(sK0,k7_setfam_1(sK0,k1_xboole_0),k7_setfam_1(sK0,k1_xboole_0)),k1_zfmisc_1(sK0)) | spl3_15),
% 0.21/0.48    inference(avatar_component_clause,[],[f152])).
% 0.21/0.48  fof(f157,plain,(
% 0.21/0.48    ~spl3_11 | ~spl3_15 | spl3_16 | ~spl3_5 | ~spl3_10 | ~spl3_14),
% 0.21/0.48    inference(avatar_split_clause,[],[f150,f141,f100,f60,f155,f152,f104])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    spl3_5 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    spl3_14 <=> r2_hidden(k3_subset_1(sK0,sK2(sK0,k7_setfam_1(sK0,k1_xboole_0),k7_setfam_1(sK0,k1_xboole_0))),k7_setfam_1(sK0,k1_xboole_0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.48  fof(f150,plain,(
% 0.21/0.48    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | r2_hidden(sK2(sK0,k7_setfam_1(sK0,k1_xboole_0),k7_setfam_1(sK0,k1_xboole_0)),k1_xboole_0) | ~m1_subset_1(sK2(sK0,k7_setfam_1(sK0,k1_xboole_0),k7_setfam_1(sK0,k1_xboole_0)),k1_zfmisc_1(sK0)) | ~m1_subset_1(k7_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) | (~spl3_10 | ~spl3_14)),
% 0.21/0.48    inference(forward_demodulation,[],[f149,f101])).
% 0.21/0.48  fof(f149,plain,(
% 0.21/0.48    r2_hidden(sK2(sK0,k7_setfam_1(sK0,k1_xboole_0),k7_setfam_1(sK0,k1_xboole_0)),k1_xboole_0) | ~m1_subset_1(sK2(sK0,k7_setfam_1(sK0,k1_xboole_0),k7_setfam_1(sK0,k1_xboole_0)),k1_zfmisc_1(sK0)) | ~m1_subset_1(k7_setfam_1(sK0,k7_setfam_1(sK0,k1_xboole_0)),k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(k7_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) | (~spl3_10 | ~spl3_14)),
% 0.21/0.48    inference(forward_demodulation,[],[f145,f101])).
% 0.21/0.48  fof(f145,plain,(
% 0.21/0.48    r2_hidden(sK2(sK0,k7_setfam_1(sK0,k1_xboole_0),k7_setfam_1(sK0,k1_xboole_0)),k7_setfam_1(sK0,k7_setfam_1(sK0,k1_xboole_0))) | ~m1_subset_1(sK2(sK0,k7_setfam_1(sK0,k1_xboole_0),k7_setfam_1(sK0,k1_xboole_0)),k1_zfmisc_1(sK0)) | ~m1_subset_1(k7_setfam_1(sK0,k7_setfam_1(sK0,k1_xboole_0)),k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(k7_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_14),
% 0.21/0.48    inference(resolution,[],[f142,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X4,X0,X1] : (~r2_hidden(k3_subset_1(X0,X4),X1) | r2_hidden(X4,k7_setfam_1(X0,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(X0)) | ~m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.48    inference(equality_resolution,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(k3_subset_1(X0,X4),X1) | ~m1_subset_1(X4,k1_zfmisc_1(X0)) | k7_setfam_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f142,plain,(
% 0.21/0.48    r2_hidden(k3_subset_1(sK0,sK2(sK0,k7_setfam_1(sK0,k1_xboole_0),k7_setfam_1(sK0,k1_xboole_0))),k7_setfam_1(sK0,k1_xboole_0)) | ~spl3_14),
% 0.21/0.48    inference(avatar_component_clause,[],[f141])).
% 0.21/0.48  fof(f144,plain,(
% 0.21/0.48    spl3_14 | spl3_3 | ~spl3_10 | ~spl3_11 | ~spl3_13),
% 0.21/0.48    inference(avatar_split_clause,[],[f139,f126,f104,f100,f51,f141])).
% 0.21/0.48  % (23434)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    spl3_13 <=> ! [X0] : (r2_hidden(k3_subset_1(sK0,sK2(sK0,X0,k7_setfam_1(sK0,k1_xboole_0))),X0) | k7_setfam_1(sK0,k1_xboole_0) = k7_setfam_1(sK0,X0) | r2_hidden(k3_subset_1(sK0,sK2(sK0,X0,k7_setfam_1(sK0,k1_xboole_0))),k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.48  fof(f139,plain,(
% 0.21/0.48    k1_xboole_0 = k7_setfam_1(sK0,k1_xboole_0) | r2_hidden(k3_subset_1(sK0,sK2(sK0,k7_setfam_1(sK0,k1_xboole_0),k7_setfam_1(sK0,k1_xboole_0))),k7_setfam_1(sK0,k1_xboole_0)) | (~spl3_10 | ~spl3_11 | ~spl3_13)),
% 0.21/0.48    inference(forward_demodulation,[],[f136,f101])).
% 0.21/0.48  fof(f136,plain,(
% 0.21/0.48    r2_hidden(k3_subset_1(sK0,sK2(sK0,k7_setfam_1(sK0,k1_xboole_0),k7_setfam_1(sK0,k1_xboole_0))),k7_setfam_1(sK0,k1_xboole_0)) | k7_setfam_1(sK0,k1_xboole_0) = k7_setfam_1(sK0,k7_setfam_1(sK0,k1_xboole_0)) | (~spl3_11 | ~spl3_13)),
% 0.21/0.48    inference(resolution,[],[f131,f105])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    m1_subset_1(k7_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f104])).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | r2_hidden(k3_subset_1(sK0,sK2(sK0,X1,k7_setfam_1(sK0,k1_xboole_0))),X1) | k7_setfam_1(sK0,k1_xboole_0) = k7_setfam_1(sK0,X1)) ) | ~spl3_13),
% 0.21/0.48    inference(resolution,[],[f127,f63])).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(k3_subset_1(sK0,sK2(sK0,X0,k7_setfam_1(sK0,k1_xboole_0))),k1_xboole_0) | k7_setfam_1(sK0,k1_xboole_0) = k7_setfam_1(sK0,X0) | r2_hidden(k3_subset_1(sK0,sK2(sK0,X0,k7_setfam_1(sK0,k1_xboole_0))),X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))) ) | ~spl3_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f126])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    ~spl3_11 | spl3_13 | ~spl3_11 | ~spl3_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f123,f115,f104,f126,f104])).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    spl3_12 <=> ! [X0] : (~r2_hidden(X0,k7_setfam_1(sK0,k1_xboole_0)) | r2_hidden(k3_subset_1(sK0,X0),k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(k3_subset_1(sK0,sK2(sK0,X0,k7_setfam_1(sK0,k1_xboole_0))),X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | r2_hidden(k3_subset_1(sK0,sK2(sK0,X0,k7_setfam_1(sK0,k1_xboole_0))),k1_xboole_0) | k7_setfam_1(sK0,k1_xboole_0) = k7_setfam_1(sK0,X0) | ~m1_subset_1(k7_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))) ) | (~spl3_11 | ~spl3_12)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f122])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(k3_subset_1(sK0,sK2(sK0,X0,k7_setfam_1(sK0,k1_xboole_0))),X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | r2_hidden(k3_subset_1(sK0,sK2(sK0,X0,k7_setfam_1(sK0,k1_xboole_0))),k1_xboole_0) | k7_setfam_1(sK0,k1_xboole_0) = k7_setfam_1(sK0,X0) | k7_setfam_1(sK0,k1_xboole_0) = k7_setfam_1(sK0,X0) | ~m1_subset_1(k7_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))) ) | (~spl3_11 | ~spl3_12)),
% 0.21/0.49    inference(resolution,[],[f121,f31])).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(sK2(sK0,X0,k7_setfam_1(sK0,k1_xboole_0)),k1_zfmisc_1(sK0)) | r2_hidden(k3_subset_1(sK0,sK2(sK0,X0,k7_setfam_1(sK0,k1_xboole_0))),X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | r2_hidden(k3_subset_1(sK0,sK2(sK0,X0,k7_setfam_1(sK0,k1_xboole_0))),k1_xboole_0) | k7_setfam_1(sK0,k1_xboole_0) = k7_setfam_1(sK0,X0)) ) | (~spl3_11 | ~spl3_12)),
% 0.21/0.49    inference(resolution,[],[f120,f105])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    ( ! [X2,X3] : (~m1_subset_1(k7_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X2))) | k7_setfam_1(sK0,k1_xboole_0) = k7_setfam_1(X2,X3) | r2_hidden(k3_subset_1(X2,sK2(X2,X3,k7_setfam_1(sK0,k1_xboole_0))),X3) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) | r2_hidden(k3_subset_1(sK0,sK2(X2,X3,k7_setfam_1(sK0,k1_xboole_0))),k1_xboole_0) | ~m1_subset_1(sK2(X2,X3,k7_setfam_1(sK0,k1_xboole_0)),k1_zfmisc_1(sK0))) ) | ~spl3_12),
% 0.21/0.49    inference(resolution,[],[f32,f116])).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,k7_setfam_1(sK0,k1_xboole_0)) | r2_hidden(k3_subset_1(sK0,X0),k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) ) | ~spl3_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f115])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1) | k7_setfam_1(X0,X1) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    ~spl3_5 | spl3_12 | ~spl3_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f111,f104,f115,f60])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,k7_setfam_1(sK0,k1_xboole_0)) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | r2_hidden(k3_subset_1(sK0,X0),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))) ) | ~spl3_11),
% 0.21/0.49    inference(resolution,[],[f105,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X4,X0,X1] : (~m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~r2_hidden(X4,k7_setfam_1(X0,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(X0)) | r2_hidden(k3_subset_1(X0,X4),X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.49    inference(equality_resolution,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X1] : (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,k1_zfmisc_1(X0)) | k7_setfam_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    spl3_11 | ~spl3_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f77,f60,f104])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    m1_subset_1(k7_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_5),
% 0.21/0.49    inference(resolution,[],[f61,f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f60])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    spl3_10 | ~spl3_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f78,f60,f100])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    k1_xboole_0 = k7_setfam_1(sK0,k7_setfam_1(sK0,k1_xboole_0)) | ~spl3_5),
% 0.21/0.49    inference(resolution,[],[f61,f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    spl3_5 | ~spl3_1 | ~spl3_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f75,f55,f42,f60])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    spl3_1 <=> k1_xboole_0 = k7_setfam_1(sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | (~spl3_1 | ~spl3_4)),
% 0.21/0.49    inference(forward_demodulation,[],[f74,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    k1_xboole_0 = k7_setfam_1(sK0,sK1) | ~spl3_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f42])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_4),
% 0.21/0.49    inference(resolution,[],[f28,f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f55])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    spl3_6 | ~spl3_1 | ~spl3_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f68,f55,f42,f70])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    spl3_6 <=> sK1 = k7_setfam_1(sK0,k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    sK1 = k7_setfam_1(sK0,k1_xboole_0) | (~spl3_1 | ~spl3_4)),
% 0.21/0.49    inference(forward_demodulation,[],[f67,f43])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    sK1 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)) | ~spl3_4),
% 0.21/0.49    inference(resolution,[],[f27,f56])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    spl3_5 | ~spl3_2 | ~spl3_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f58,f55,f45,f60])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    spl3_2 <=> k1_xboole_0 = sK1),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | (~spl3_2 | ~spl3_4)),
% 0.21/0.49    inference(superposition,[],[f56,f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    k1_xboole_0 = sK1 | ~spl3_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f45])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    spl3_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f21,f55])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ((k1_xboole_0 = sK1 & k1_xboole_0 != k7_setfam_1(sK0,sK1)) | (k1_xboole_0 = k7_setfam_1(sK0,sK1) & k1_xboole_0 != sK1)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ? [X0,X1] : (((k1_xboole_0 = X1 & k1_xboole_0 != k7_setfam_1(X0,X1)) | (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (((k1_xboole_0 = sK1 & k1_xboole_0 != k7_setfam_1(sK0,sK1)) | (k1_xboole_0 = k7_setfam_1(sK0,sK1) & k1_xboole_0 != sK1)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ? [X0,X1] : (((k1_xboole_0 = X1 & k1_xboole_0 != k7_setfam_1(X0,X1)) | (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (~(k1_xboole_0 = X1 & k1_xboole_0 != k7_setfam_1(X0,X1)) & ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1)))),
% 0.21/0.49    inference(negated_conjecture,[],[f6])).
% 0.21/0.49  fof(f6,conjecture,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (~(k1_xboole_0 = X1 & k1_xboole_0 != k7_setfam_1(X0,X1)) & ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tops_2)).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ~spl3_2 | ~spl3_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f48,f51,f45])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    k1_xboole_0 != k7_setfam_1(sK0,k1_xboole_0) | k1_xboole_0 != sK1),
% 0.21/0.49    inference(inner_rewriting,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    k1_xboole_0 != k7_setfam_1(sK0,sK1) | k1_xboole_0 != sK1),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    spl3_1 | spl3_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f25,f45,f42])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    k1_xboole_0 = sK1 | k1_xboole_0 = k7_setfam_1(sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (23427)------------------------------
% 0.21/0.49  % (23427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (23427)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (23427)Memory used [KB]: 10746
% 0.21/0.49  % (23427)Time elapsed: 0.055 s
% 0.21/0.49  % (23427)------------------------------
% 0.21/0.49  % (23427)------------------------------
% 0.21/0.49  % (23420)Success in time 0.126 s
%------------------------------------------------------------------------------
