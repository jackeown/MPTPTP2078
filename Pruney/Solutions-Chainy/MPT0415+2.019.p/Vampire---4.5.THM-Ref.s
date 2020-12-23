%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:24 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 180 expanded)
%              Number of leaves         :   18 (  70 expanded)
%              Depth                    :   12
%              Number of atoms          :  335 ( 816 expanded)
%              Number of equality atoms :   71 ( 180 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f131,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f47,f51,f61,f67,f81,f90,f104,f115,f126,f130])).

fof(f130,plain,(
    ~ spl3_10 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | ~ spl3_10 ),
    inference(resolution,[],[f114,f52])).

fof(f52,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f25,f38])).

fof(f38,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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

fof(f25,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f114,plain,
    ( r2_hidden(sK2(sK0,sK1,sK1),k1_xboole_0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl3_10
  <=> r2_hidden(sK2(sK0,sK1,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f126,plain,
    ( ~ spl3_3
    | spl3_2
    | ~ spl3_1
    | spl3_9 ),
    inference(avatar_split_clause,[],[f125,f110,f41,f45,f49])).

fof(f49,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f45,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f41,plain,
    ( spl3_1
  <=> k1_xboole_0 = k7_setfam_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f110,plain,
    ( spl3_9
  <=> m1_subset_1(sK2(sK0,sK1,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f125,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_1
    | spl3_9 ),
    inference(forward_demodulation,[],[f124,f42])).

fof(f42,plain,
    ( k1_xboole_0 = k7_setfam_1(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f124,plain,
    ( sK1 = k7_setfam_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl3_9 ),
    inference(duplicate_literal_removal,[],[f123])).

fof(f123,plain,
    ( sK1 = k7_setfam_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl3_9 ),
    inference(resolution,[],[f111,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(X0))
      | k7_setfam_1(X0,X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f18])).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
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

fof(f111,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1,sK1),k1_zfmisc_1(sK0))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f110])).

fof(f115,plain,
    ( ~ spl3_3
    | ~ spl3_9
    | spl3_10
    | ~ spl3_5
    | ~ spl3_1
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f108,f101,f41,f65,f113,f110,f49])).

fof(f65,plain,
    ( spl3_5
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f101,plain,
    ( spl3_8
  <=> r2_hidden(k3_subset_1(sK0,sK2(sK0,sK1,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f108,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | r2_hidden(sK2(sK0,sK1,sK1),k1_xboole_0)
    | ~ m1_subset_1(sK2(sK0,sK1,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_1
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f107,f42])).

fof(f107,plain,
    ( r2_hidden(sK2(sK0,sK1,sK1),k1_xboole_0)
    | ~ m1_subset_1(sK2(sK0,sK1,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_1
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f105,f42])).

fof(f105,plain,
    ( r2_hidden(sK2(sK0,sK1,sK1),k7_setfam_1(sK0,sK1))
    | ~ m1_subset_1(sK2(sK0,sK1,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_8 ),
    inference(resolution,[],[f102,f36])).

fof(f36,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(k3_subset_1(X0,X4),X1)
      | r2_hidden(X4,k7_setfam_1(X0,X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | k7_setfam_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f102,plain,
    ( r2_hidden(k3_subset_1(sK0,sK2(sK0,sK1,sK1)),sK1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f101])).

fof(f104,plain,
    ( spl3_8
    | spl3_2
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f99,f88,f49,f41,f45,f101])).

fof(f88,plain,
    ( spl3_7
  <=> ! [X0] :
        ( r2_hidden(k3_subset_1(sK0,sK2(sK0,X0,sK1)),X0)
        | sK1 = k7_setfam_1(sK0,X0)
        | r2_hidden(k3_subset_1(sK0,sK2(sK0,X0,sK1)),k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f99,plain,
    ( k1_xboole_0 = sK1
    | r2_hidden(k3_subset_1(sK0,sK2(sK0,sK1,sK1)),sK1)
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f96,f42])).

fof(f96,plain,
    ( r2_hidden(k3_subset_1(sK0,sK2(sK0,sK1,sK1)),sK1)
    | sK1 = k7_setfam_1(sK0,sK1)
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(resolution,[],[f92,f50])).

fof(f50,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f92,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | r2_hidden(k3_subset_1(sK0,sK2(sK0,X1,sK1)),X1)
        | sK1 = k7_setfam_1(sK0,X1) )
    | ~ spl3_7 ),
    inference(resolution,[],[f89,f52])).

fof(f89,plain,
    ( ! [X0] :
        ( r2_hidden(k3_subset_1(sK0,sK2(sK0,X0,sK1)),k1_xboole_0)
        | sK1 = k7_setfam_1(sK0,X0)
        | r2_hidden(k3_subset_1(sK0,sK2(sK0,X0,sK1)),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f88])).

fof(f90,plain,
    ( ~ spl3_3
    | spl3_7
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f86,f78,f49,f88,f49])).

fof(f78,plain,
    ( spl3_6
  <=> ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | r2_hidden(k3_subset_1(sK0,X1),k1_xboole_0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f86,plain,
    ( ! [X0] :
        ( r2_hidden(k3_subset_1(sK0,sK2(sK0,X0,sK1)),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | r2_hidden(k3_subset_1(sK0,sK2(sK0,X0,sK1)),k1_xboole_0)
        | sK1 = k7_setfam_1(sK0,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(duplicate_literal_removal,[],[f85])).

fof(f85,plain,
    ( ! [X0] :
        ( r2_hidden(k3_subset_1(sK0,sK2(sK0,X0,sK1)),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | r2_hidden(k3_subset_1(sK0,sK2(sK0,X0,sK1)),k1_xboole_0)
        | sK1 = k7_setfam_1(sK0,X0)
        | sK1 = k7_setfam_1(sK0,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(resolution,[],[f84,f30])).

fof(f84,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2(sK0,X0,sK1),k1_zfmisc_1(sK0))
        | r2_hidden(k3_subset_1(sK0,sK2(sK0,X0,sK1)),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | r2_hidden(k3_subset_1(sK0,sK2(sK0,X0,sK1)),k1_xboole_0)
        | sK1 = k7_setfam_1(sK0,X0) )
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(resolution,[],[f83,f50])).

fof(f83,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(X2)))
        | sK1 = k7_setfam_1(X2,X3)
        | r2_hidden(k3_subset_1(X2,sK2(X2,X3,sK1)),X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
        | r2_hidden(k3_subset_1(sK0,sK2(X2,X3,sK1)),k1_xboole_0)
        | ~ m1_subset_1(sK2(X2,X3,sK1),k1_zfmisc_1(sK0)) )
    | ~ spl3_6 ),
    inference(resolution,[],[f31,f79])).

fof(f79,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | r2_hidden(k3_subset_1(sK0,X1),k1_xboole_0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK0)) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f78])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1)
      | k7_setfam_1(X0,X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f81,plain,
    ( ~ spl3_5
    | spl3_6
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f75,f59,f49,f78,f65])).

fof(f59,plain,
    ( spl3_4
  <=> sK1 = k7_setfam_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f75,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | ~ r2_hidden(X1,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
        | r2_hidden(k3_subset_1(sK0,X1),k1_xboole_0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
    | ~ spl3_4 ),
    inference(superposition,[],[f37,f60])).

fof(f60,plain,
    ( sK1 = k7_setfam_1(sK0,k1_xboole_0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f59])).

fof(f37,plain,(
    ! [X4,X0,X1] :
      ( ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ r2_hidden(X4,k7_setfam_1(X0,X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | k7_setfam_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f67,plain,
    ( spl3_5
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f63,f49,f41,f65])).

fof(f63,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f62,f42])).

fof(f62,plain,
    ( m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_3 ),
    inference(resolution,[],[f27,f50])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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
    ( spl3_4
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f57,f49,f41,f59])).

fof(f57,plain,
    ( sK1 = k7_setfam_1(sK0,k1_xboole_0)
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f56,f42])).

fof(f56,plain,
    ( sK1 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))
    | ~ spl3_3 ),
    inference(resolution,[],[f26,f50])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(f51,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f22,f49])).

fof(f22,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k1_xboole_0 = k7_setfam_1(sK0,sK1)
    & k1_xboole_0 != sK1
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f13])).

fof(f13,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 = k7_setfam_1(X0,X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( k1_xboole_0 = k7_setfam_1(sK0,sK1)
      & k1_xboole_0 != sK1
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k7_setfam_1(X0,X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k7_setfam_1(X0,X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
            & k1_xboole_0 != X1 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).

fof(f47,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f23,f45])).

fof(f23,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f14])).

fof(f43,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f24,f41])).

fof(f24,plain,(
    k1_xboole_0 = k7_setfam_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:14:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (7143)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.47  % (7143)Refutation not found, incomplete strategy% (7143)------------------------------
% 0.22/0.47  % (7143)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (7143)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (7143)Memory used [KB]: 6140
% 0.22/0.47  % (7143)Time elapsed: 0.009 s
% 0.22/0.47  % (7143)------------------------------
% 0.22/0.47  % (7143)------------------------------
% 0.22/0.48  % (7149)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (7144)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (7149)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f131,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f43,f47,f51,f61,f67,f81,f90,f104,f115,f126,f130])).
% 0.22/0.50  fof(f130,plain,(
% 0.22/0.50    ~spl3_10),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f129])).
% 0.22/0.50  fof(f129,plain,(
% 0.22/0.50    $false | ~spl3_10),
% 0.22/0.50    inference(resolution,[],[f114,f52])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.50    inference(superposition,[],[f25,f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.50    inference(equality_resolution,[],[f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.22/0.50    inference(flattening,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.22/0.50    inference(nnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.22/0.50  fof(f114,plain,(
% 0.22/0.50    r2_hidden(sK2(sK0,sK1,sK1),k1_xboole_0) | ~spl3_10),
% 0.22/0.50    inference(avatar_component_clause,[],[f113])).
% 0.22/0.50  fof(f113,plain,(
% 0.22/0.50    spl3_10 <=> r2_hidden(sK2(sK0,sK1,sK1),k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.50  fof(f126,plain,(
% 0.22/0.50    ~spl3_3 | spl3_2 | ~spl3_1 | spl3_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f125,f110,f41,f45,f49])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    spl3_2 <=> k1_xboole_0 = sK1),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    spl3_1 <=> k1_xboole_0 = k7_setfam_1(sK0,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.50  fof(f110,plain,(
% 0.22/0.50    spl3_9 <=> m1_subset_1(sK2(sK0,sK1,sK1),k1_zfmisc_1(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.50  fof(f125,plain,(
% 0.22/0.50    k1_xboole_0 = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | (~spl3_1 | spl3_9)),
% 0.22/0.50    inference(forward_demodulation,[],[f124,f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    k1_xboole_0 = k7_setfam_1(sK0,sK1) | ~spl3_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f41])).
% 0.22/0.50  fof(f124,plain,(
% 0.22/0.50    sK1 = k7_setfam_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl3_9),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f123])).
% 0.22/0.50  fof(f123,plain,(
% 0.22/0.50    sK1 = k7_setfam_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl3_9),
% 0.22/0.50    inference(resolution,[],[f111,f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(X0)) | k7_setfam_1(X0,X1) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ((~r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1) | r2_hidden(sK2(X0,X1,X2),X2)) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(X0)))) & (! [X4] : (((r2_hidden(X4,X2) | ~r2_hidden(k3_subset_1(X0,X4),X1)) & (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0))) => ((~r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1) | r2_hidden(sK2(X0,X1,X2),X2)) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(X0))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X4] : (((r2_hidden(X4,X2) | ~r2_hidden(k3_subset_1(X0,X4),X1)) & (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    inference(rectify,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(k3_subset_1(X0,X3),X1)) & (r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    inference(flattening,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(k3_subset_1(X0,X3),X1)) & (r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    inference(nnf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : ((k7_setfam_1(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k7_setfam_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).
% 0.22/0.50  fof(f111,plain,(
% 0.22/0.50    ~m1_subset_1(sK2(sK0,sK1,sK1),k1_zfmisc_1(sK0)) | spl3_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f110])).
% 0.22/0.50  fof(f115,plain,(
% 0.22/0.50    ~spl3_3 | ~spl3_9 | spl3_10 | ~spl3_5 | ~spl3_1 | ~spl3_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f108,f101,f41,f65,f113,f110,f49])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    spl3_5 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    spl3_8 <=> r2_hidden(k3_subset_1(sK0,sK2(sK0,sK1,sK1)),sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.50  fof(f108,plain,(
% 0.22/0.50    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | r2_hidden(sK2(sK0,sK1,sK1),k1_xboole_0) | ~m1_subset_1(sK2(sK0,sK1,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | (~spl3_1 | ~spl3_8)),
% 0.22/0.50    inference(forward_demodulation,[],[f107,f42])).
% 0.22/0.50  fof(f107,plain,(
% 0.22/0.50    r2_hidden(sK2(sK0,sK1,sK1),k1_xboole_0) | ~m1_subset_1(sK2(sK0,sK1,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | (~spl3_1 | ~spl3_8)),
% 0.22/0.50    inference(forward_demodulation,[],[f105,f42])).
% 0.22/0.50  fof(f105,plain,(
% 0.22/0.50    r2_hidden(sK2(sK0,sK1,sK1),k7_setfam_1(sK0,sK1)) | ~m1_subset_1(sK2(sK0,sK1,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_8),
% 0.22/0.50    inference(resolution,[],[f102,f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ( ! [X4,X0,X1] : (~r2_hidden(k3_subset_1(X0,X4),X1) | r2_hidden(X4,k7_setfam_1(X0,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(X0)) | ~m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.50    inference(equality_resolution,[],[f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(k3_subset_1(X0,X4),X1) | ~m1_subset_1(X4,k1_zfmisc_1(X0)) | k7_setfam_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    r2_hidden(k3_subset_1(sK0,sK2(sK0,sK1,sK1)),sK1) | ~spl3_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f101])).
% 0.22/0.50  fof(f104,plain,(
% 0.22/0.50    spl3_8 | spl3_2 | ~spl3_1 | ~spl3_3 | ~spl3_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f99,f88,f49,f41,f45,f101])).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    spl3_7 <=> ! [X0] : (r2_hidden(k3_subset_1(sK0,sK2(sK0,X0,sK1)),X0) | sK1 = k7_setfam_1(sK0,X0) | r2_hidden(k3_subset_1(sK0,sK2(sK0,X0,sK1)),k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    k1_xboole_0 = sK1 | r2_hidden(k3_subset_1(sK0,sK2(sK0,sK1,sK1)),sK1) | (~spl3_1 | ~spl3_3 | ~spl3_7)),
% 0.22/0.50    inference(forward_demodulation,[],[f96,f42])).
% 0.22/0.50  fof(f96,plain,(
% 0.22/0.50    r2_hidden(k3_subset_1(sK0,sK2(sK0,sK1,sK1)),sK1) | sK1 = k7_setfam_1(sK0,sK1) | (~spl3_3 | ~spl3_7)),
% 0.22/0.50    inference(resolution,[],[f92,f50])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f49])).
% 0.22/0.50  fof(f92,plain,(
% 0.22/0.50    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | r2_hidden(k3_subset_1(sK0,sK2(sK0,X1,sK1)),X1) | sK1 = k7_setfam_1(sK0,X1)) ) | ~spl3_7),
% 0.22/0.50    inference(resolution,[],[f89,f52])).
% 0.22/0.50  fof(f89,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(k3_subset_1(sK0,sK2(sK0,X0,sK1)),k1_xboole_0) | sK1 = k7_setfam_1(sK0,X0) | r2_hidden(k3_subset_1(sK0,sK2(sK0,X0,sK1)),X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))) ) | ~spl3_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f88])).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    ~spl3_3 | spl3_7 | ~spl3_3 | ~spl3_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f86,f78,f49,f88,f49])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    spl3_6 <=> ! [X1] : (~r2_hidden(X1,sK1) | r2_hidden(k3_subset_1(sK0,X1),k1_xboole_0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.50  fof(f86,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(k3_subset_1(sK0,sK2(sK0,X0,sK1)),X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | r2_hidden(k3_subset_1(sK0,sK2(sK0,X0,sK1)),k1_xboole_0) | sK1 = k7_setfam_1(sK0,X0) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))) ) | (~spl3_3 | ~spl3_6)),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f85])).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(k3_subset_1(sK0,sK2(sK0,X0,sK1)),X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | r2_hidden(k3_subset_1(sK0,sK2(sK0,X0,sK1)),k1_xboole_0) | sK1 = k7_setfam_1(sK0,X0) | sK1 = k7_setfam_1(sK0,X0) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))) ) | (~spl3_3 | ~spl3_6)),
% 0.22/0.50    inference(resolution,[],[f84,f30])).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(sK2(sK0,X0,sK1),k1_zfmisc_1(sK0)) | r2_hidden(k3_subset_1(sK0,sK2(sK0,X0,sK1)),X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | r2_hidden(k3_subset_1(sK0,sK2(sK0,X0,sK1)),k1_xboole_0) | sK1 = k7_setfam_1(sK0,X0)) ) | (~spl3_3 | ~spl3_6)),
% 0.22/0.50    inference(resolution,[],[f83,f50])).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    ( ! [X2,X3] : (~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(X2))) | sK1 = k7_setfam_1(X2,X3) | r2_hidden(k3_subset_1(X2,sK2(X2,X3,sK1)),X3) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) | r2_hidden(k3_subset_1(sK0,sK2(X2,X3,sK1)),k1_xboole_0) | ~m1_subset_1(sK2(X2,X3,sK1),k1_zfmisc_1(sK0))) ) | ~spl3_6),
% 0.22/0.50    inference(resolution,[],[f31,f79])).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    ( ! [X1] : (~r2_hidden(X1,sK1) | r2_hidden(k3_subset_1(sK0,X1),k1_xboole_0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) ) | ~spl3_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f78])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1) | k7_setfam_1(X0,X1) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    ~spl3_5 | spl3_6 | ~spl3_3 | ~spl3_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f75,f59,f49,f78,f65])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    spl3_4 <=> sK1 = k7_setfam_1(sK0,k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    ( ! [X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~r2_hidden(X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | r2_hidden(k3_subset_1(sK0,X1),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))) ) | ~spl3_4),
% 0.22/0.50    inference(superposition,[],[f37,f60])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    sK1 = k7_setfam_1(sK0,k1_xboole_0) | ~spl3_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f59])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ( ! [X4,X0,X1] : (~m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~r2_hidden(X4,k7_setfam_1(X0,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(X0)) | r2_hidden(k3_subset_1(X0,X4),X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.50    inference(equality_resolution,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X1] : (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,k1_zfmisc_1(X0)) | k7_setfam_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    spl3_5 | ~spl3_1 | ~spl3_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f63,f49,f41,f65])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | (~spl3_1 | ~spl3_3)),
% 0.22/0.50    inference(forward_demodulation,[],[f62,f42])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_3),
% 0.22/0.50    inference(resolution,[],[f27,f50])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    spl3_4 | ~spl3_1 | ~spl3_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f57,f49,f41,f59])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    sK1 = k7_setfam_1(sK0,k1_xboole_0) | (~spl3_1 | ~spl3_3)),
% 0.22/0.50    inference(forward_demodulation,[],[f56,f42])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    sK1 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)) | ~spl3_3),
% 0.22/0.50    inference(resolution,[],[f26,f50])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1) )),
% 0.22/0.50    inference(cnf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,plain,(
% 0.22/0.50    ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    spl3_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f22,f49])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    k1_xboole_0 = k7_setfam_1(sK0,sK1) & k1_xboole_0 != sK1 & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ? [X0,X1] : (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (k1_xboole_0 = k7_setfam_1(sK0,sK1) & k1_xboole_0 != sK1 & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f9,plain,(
% 0.22/0.50    ? [X0,X1] : (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    inference(flattening,[],[f8])).
% 0.22/0.50  fof(f8,plain,(
% 0.22/0.50    ? [X0,X1] : ((k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 0.22/0.50    inference(negated_conjecture,[],[f6])).
% 0.22/0.50  fof(f6,conjecture,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ~spl3_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f23,f45])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    k1_xboole_0 != sK1),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    spl3_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f24,f41])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    k1_xboole_0 = k7_setfam_1(sK0,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (7149)------------------------------
% 0.22/0.50  % (7149)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (7149)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (7149)Memory used [KB]: 10746
% 0.22/0.50  % (7149)Time elapsed: 0.074 s
% 0.22/0.50  % (7149)------------------------------
% 0.22/0.50  % (7149)------------------------------
% 0.22/0.50  % (7142)Success in time 0.135 s
%------------------------------------------------------------------------------
