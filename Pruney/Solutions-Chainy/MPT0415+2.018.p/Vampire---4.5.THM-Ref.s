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
% DateTime   : Thu Dec  3 12:46:23 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 136 expanded)
%              Number of leaves         :   17 (  55 expanded)
%              Depth                    :   14
%              Number of atoms          :  301 ( 582 expanded)
%              Number of equality atoms :   51 ( 116 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f153,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f60,f64,f68,f74,f95,f111,f123,f143])).

fof(f143,plain,
    ( ~ spl4_3
    | spl4_2
    | ~ spl4_1
    | ~ spl4_7
    | spl4_8 ),
    inference(avatar_split_clause,[],[f142,f120,f109,f54,f58,f62])).

fof(f62,plain,
    ( spl4_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f58,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f54,plain,
    ( spl4_1
  <=> k1_xboole_0 = k7_setfam_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f109,plain,
    ( spl4_7
  <=> ! [X0] :
        ( r2_hidden(k3_subset_1(sK0,sK3(sK0,X0,sK1)),X0)
        | sK1 = k7_setfam_1(sK0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f120,plain,
    ( spl4_8
  <=> m1_subset_1(k3_subset_1(sK0,sK3(sK0,sK1,sK1)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f142,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_1
    | ~ spl4_7
    | spl4_8 ),
    inference(forward_demodulation,[],[f141,f55])).

fof(f55,plain,
    ( k1_xboole_0 = k7_setfam_1(sK0,sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f141,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | sK1 = k7_setfam_1(sK0,sK1)
    | ~ spl4_7
    | spl4_8 ),
    inference(duplicate_literal_removal,[],[f136])).

fof(f136,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | sK1 = k7_setfam_1(sK0,sK1)
    | ~ spl4_7
    | spl4_8 ),
    inference(resolution,[],[f113,f121])).

fof(f121,plain,
    ( ~ m1_subset_1(k3_subset_1(sK0,sK3(sK0,sK1,sK1)),k1_zfmisc_1(sK0))
    | spl4_8 ),
    inference(avatar_component_clause,[],[f120])).

fof(f113,plain,
    ( ! [X2,X1] :
        ( m1_subset_1(k3_subset_1(sK0,sK3(sK0,X1,sK1)),X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | sK1 = k7_setfam_1(sK0,X1) )
    | ~ spl4_7 ),
    inference(resolution,[],[f110,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f110,plain,
    ( ! [X0] :
        ( r2_hidden(k3_subset_1(sK0,sK3(sK0,X0,sK1)),X0)
        | sK1 = k7_setfam_1(sK0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f109])).

fof(f123,plain,
    ( ~ spl4_8
    | ~ spl4_3
    | spl4_2
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f118,f109,f93,f54,f58,f62,f120])).

fof(f93,plain,
    ( spl4_6
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f118,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(k3_subset_1(sK0,sK3(sK0,sK1,sK1)),k1_zfmisc_1(sK0))
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f116,f55])).

fof(f116,plain,
    ( sK1 = k7_setfam_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(k3_subset_1(sK0,sK3(sK0,sK1,sK1)),k1_zfmisc_1(sK0))
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(resolution,[],[f110,f94])).

fof(f94,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f93])).

fof(f111,plain,
    ( ~ spl4_3
    | spl4_7
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f107,f93,f62,f109,f62])).

fof(f107,plain,
    ( ! [X0] :
        ( r2_hidden(k3_subset_1(sK0,sK3(sK0,X0,sK1)),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | sK1 = k7_setfam_1(sK0,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(duplicate_literal_removal,[],[f105])).

fof(f105,plain,
    ( ! [X0] :
        ( r2_hidden(k3_subset_1(sK0,sK3(sK0,X0,sK1)),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | sK1 = k7_setfam_1(sK0,X0)
        | sK1 = k7_setfam_1(sK0,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(resolution,[],[f103,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(X0))
      | k7_setfam_1(X0,X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).

fof(f31,plain,(
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

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

% (15220)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
fof(f103,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(sK0,X0,sK1),k1_zfmisc_1(sK0))
        | r2_hidden(k3_subset_1(sK0,sK3(sK0,X0,sK1)),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | sK1 = k7_setfam_1(sK0,X0) )
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(resolution,[],[f101,f63])).

fof(f63,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f101,plain,
    ( ! [X12,X11] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(X11)))
        | sK1 = k7_setfam_1(X11,X12)
        | r2_hidden(k3_subset_1(X11,sK3(X11,X12,sK1)),X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(X11)))
        | ~ m1_subset_1(sK3(X11,X12,sK1),k1_zfmisc_1(sK0)) )
    | ~ spl4_6 ),
    inference(resolution,[],[f46,f94])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(k3_subset_1(X0,sK3(X0,X1,X2)),X1)
      | k7_setfam_1(X0,X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f95,plain,
    ( ~ spl4_3
    | spl4_6
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f91,f72,f66,f93,f62])).

fof(f66,plain,
    ( spl4_4
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f72,plain,
    ( spl4_5
  <=> sK1 = k7_setfam_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f91,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(superposition,[],[f88,f73])).

fof(f73,plain,
    ( sK1 = k7_setfam_1(sK0,k1_xboole_0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f72])).

fof(f88,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k7_setfam_1(X0,k1_xboole_0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ m1_subset_1(k7_setfam_1(X0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl4_4 ),
    inference(resolution,[],[f85,f37])).

fof(f37,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f85,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X3)))
        | ~ m1_subset_1(k7_setfam_1(X3,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X3)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
        | ~ r2_hidden(X4,k7_setfam_1(X3,k1_xboole_0)) )
    | ~ spl4_4 ),
    inference(resolution,[],[f83,f37])).

fof(f83,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r2_hidden(X0,k7_setfam_1(X1,X2)) )
    | ~ spl4_4 ),
    inference(resolution,[],[f81,f67])).

fof(f67,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f66])).

fof(f81,plain,(
    ! [X10,X8,X7,X9] :
      ( ~ v1_xboole_0(X10)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X8))
      | ~ m1_subset_1(k7_setfam_1(X8,X9),k1_zfmisc_1(k1_zfmisc_1(X8)))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(X8)))
      | ~ m1_subset_1(X9,k1_zfmisc_1(X10))
      | ~ r2_hidden(X7,k7_setfam_1(X8,X9)) ) ),
    inference(resolution,[],[f52,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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

fof(f52,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ r2_hidden(X4,k7_setfam_1(X0,X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f43])).

% (15223)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% (15223)Refutation not found, incomplete strategy% (15223)------------------------------
% (15223)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15223)Termination reason: Refutation not found, incomplete strategy

% (15223)Memory used [KB]: 10618
% (15223)Time elapsed: 0.116 s
% (15223)------------------------------
% (15223)------------------------------
% (15219)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | k7_setfam_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f74,plain,
    ( ~ spl4_3
    | spl4_5
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f69,f54,f72,f62])).

fof(f69,plain,
    ( sK1 = k7_setfam_1(sK0,k1_xboole_0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_1 ),
    inference(superposition,[],[f41,f55])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(f68,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f36,f66])).

fof(f36,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f64,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f33,f62])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( k1_xboole_0 = k7_setfam_1(sK0,sK1)
    & k1_xboole_0 != sK1
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f24])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 = k7_setfam_1(X0,X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( k1_xboole_0 = k7_setfam_1(sK0,sK1)
      & k1_xboole_0 != sK1
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k7_setfam_1(X0,X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k7_setfam_1(X0,X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
            & k1_xboole_0 != X1 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).

fof(f60,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f34,f58])).

fof(f34,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f25])).

fof(f56,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f35,f54])).

fof(f35,plain,(
    k1_xboole_0 = k7_setfam_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:42:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (15218)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.48  % (15216)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.48  % (15208)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.48  % (15210)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.49  % (15216)Refutation not found, incomplete strategy% (15216)------------------------------
% 0.22/0.49  % (15216)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (15216)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (15216)Memory used [KB]: 1663
% 0.22/0.49  % (15216)Time elapsed: 0.069 s
% 0.22/0.49  % (15216)------------------------------
% 0.22/0.49  % (15216)------------------------------
% 0.22/0.51  % (15212)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.51  % (15222)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.51  % (15207)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.51  % (15205)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.51  % (15203)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (15206)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (15215)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (15203)Refutation not found, incomplete strategy% (15203)------------------------------
% 0.22/0.51  % (15203)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (15203)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (15203)Memory used [KB]: 6140
% 0.22/0.51  % (15203)Time elapsed: 0.092 s
% 0.22/0.51  % (15203)------------------------------
% 0.22/0.51  % (15203)------------------------------
% 0.22/0.51  % (15206)Refutation not found, incomplete strategy% (15206)------------------------------
% 0.22/0.51  % (15206)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (15206)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (15206)Memory used [KB]: 10618
% 0.22/0.51  % (15206)Time elapsed: 0.090 s
% 0.22/0.51  % (15206)------------------------------
% 0.22/0.51  % (15206)------------------------------
% 0.22/0.52  % (15211)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.52  % (15204)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (15221)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.52  % (15209)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.52  % (15204)Refutation not found, incomplete strategy% (15204)------------------------------
% 0.22/0.52  % (15204)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (15204)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (15204)Memory used [KB]: 10618
% 0.22/0.52  % (15204)Time elapsed: 0.102 s
% 0.22/0.52  % (15204)------------------------------
% 0.22/0.52  % (15204)------------------------------
% 0.22/0.52  % (15214)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.52  % (15213)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.52  % (15214)Refutation not found, incomplete strategy% (15214)------------------------------
% 0.22/0.52  % (15214)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (15214)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (15214)Memory used [KB]: 10618
% 0.22/0.52  % (15214)Time elapsed: 0.106 s
% 0.22/0.52  % (15214)------------------------------
% 0.22/0.52  % (15214)------------------------------
% 0.22/0.52  % (15213)Refutation not found, incomplete strategy% (15213)------------------------------
% 0.22/0.52  % (15213)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (15213)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (15213)Memory used [KB]: 6012
% 0.22/0.52  % (15213)Time elapsed: 0.103 s
% 0.22/0.52  % (15213)------------------------------
% 0.22/0.52  % (15213)------------------------------
% 0.22/0.53  % (15209)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f153,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f56,f60,f64,f68,f74,f95,f111,f123,f143])).
% 0.22/0.53  fof(f143,plain,(
% 0.22/0.53    ~spl4_3 | spl4_2 | ~spl4_1 | ~spl4_7 | spl4_8),
% 0.22/0.53    inference(avatar_split_clause,[],[f142,f120,f109,f54,f58,f62])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    spl4_3 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    spl4_2 <=> k1_xboole_0 = sK1),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    spl4_1 <=> k1_xboole_0 = k7_setfam_1(sK0,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.53  fof(f109,plain,(
% 0.22/0.53    spl4_7 <=> ! [X0] : (r2_hidden(k3_subset_1(sK0,sK3(sK0,X0,sK1)),X0) | sK1 = k7_setfam_1(sK0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.53  fof(f120,plain,(
% 0.22/0.53    spl4_8 <=> m1_subset_1(k3_subset_1(sK0,sK3(sK0,sK1,sK1)),k1_zfmisc_1(sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.53  fof(f142,plain,(
% 0.22/0.53    k1_xboole_0 = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | (~spl4_1 | ~spl4_7 | spl4_8)),
% 0.22/0.53    inference(forward_demodulation,[],[f141,f55])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    k1_xboole_0 = k7_setfam_1(sK0,sK1) | ~spl4_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f54])).
% 0.22/0.53  fof(f141,plain,(
% 0.22/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | sK1 = k7_setfam_1(sK0,sK1) | (~spl4_7 | spl4_8)),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f136])).
% 0.22/0.53  fof(f136,plain,(
% 0.22/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | sK1 = k7_setfam_1(sK0,sK1) | (~spl4_7 | spl4_8)),
% 0.22/0.53    inference(resolution,[],[f113,f121])).
% 0.22/0.53  fof(f121,plain,(
% 0.22/0.53    ~m1_subset_1(k3_subset_1(sK0,sK3(sK0,sK1,sK1)),k1_zfmisc_1(sK0)) | spl4_8),
% 0.22/0.53    inference(avatar_component_clause,[],[f120])).
% 0.22/0.53  fof(f113,plain,(
% 0.22/0.53    ( ! [X2,X1] : (m1_subset_1(k3_subset_1(sK0,sK3(sK0,X1,sK1)),X2) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | sK1 = k7_setfam_1(sK0,X1)) ) | ~spl4_7),
% 0.22/0.53    inference(resolution,[],[f110,f49])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.53    inference(flattening,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.22/0.53  fof(f110,plain,(
% 0.22/0.53    ( ! [X0] : (r2_hidden(k3_subset_1(sK0,sK3(sK0,X0,sK1)),X0) | sK1 = k7_setfam_1(sK0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))) ) | ~spl4_7),
% 0.22/0.53    inference(avatar_component_clause,[],[f109])).
% 0.22/0.53  fof(f123,plain,(
% 0.22/0.53    ~spl4_8 | ~spl4_3 | spl4_2 | ~spl4_1 | ~spl4_6 | ~spl4_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f118,f109,f93,f54,f58,f62,f120])).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    spl4_6 <=> ! [X0] : (~r2_hidden(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.53  fof(f118,plain,(
% 0.22/0.53    k1_xboole_0 = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(k3_subset_1(sK0,sK3(sK0,sK1,sK1)),k1_zfmisc_1(sK0)) | (~spl4_1 | ~spl4_6 | ~spl4_7)),
% 0.22/0.53    inference(forward_demodulation,[],[f116,f55])).
% 0.22/0.53  fof(f116,plain,(
% 0.22/0.53    sK1 = k7_setfam_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(k3_subset_1(sK0,sK3(sK0,sK1,sK1)),k1_zfmisc_1(sK0)) | (~spl4_6 | ~spl4_7)),
% 0.22/0.53    inference(resolution,[],[f110,f94])).
% 0.22/0.53  fof(f94,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) ) | ~spl4_6),
% 0.22/0.53    inference(avatar_component_clause,[],[f93])).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    ~spl4_3 | spl4_7 | ~spl4_3 | ~spl4_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f107,f93,f62,f109,f62])).
% 0.22/0.53  fof(f107,plain,(
% 0.22/0.53    ( ! [X0] : (r2_hidden(k3_subset_1(sK0,sK3(sK0,X0,sK1)),X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | sK1 = k7_setfam_1(sK0,X0) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))) ) | (~spl4_3 | ~spl4_6)),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f105])).
% 0.22/0.53  fof(f105,plain,(
% 0.22/0.53    ( ! [X0] : (r2_hidden(k3_subset_1(sK0,sK3(sK0,X0,sK1)),X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | sK1 = k7_setfam_1(sK0,X0) | sK1 = k7_setfam_1(sK0,X0) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))) ) | (~spl4_3 | ~spl4_6)),
% 0.22/0.53    inference(resolution,[],[f103,f45])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(X0)) | k7_setfam_1(X0,X1) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ((~r2_hidden(k3_subset_1(X0,sK3(X0,X1,X2)),X1) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(k3_subset_1(X0,sK3(X0,X1,X2)),X1) | r2_hidden(sK3(X0,X1,X2),X2)) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(X0)))) & (! [X4] : (((r2_hidden(X4,X2) | ~r2_hidden(k3_subset_1(X0,X4),X1)) & (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0))) => ((~r2_hidden(k3_subset_1(X0,sK3(X0,X1,X2)),X1) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(k3_subset_1(X0,sK3(X0,X1,X2)),X1) | r2_hidden(sK3(X0,X1,X2),X2)) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(X0))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X4] : (((r2_hidden(X4,X2) | ~r2_hidden(k3_subset_1(X0,X4),X1)) & (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.53    inference(rectify,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(k3_subset_1(X0,X3),X1)) & (r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.53    inference(flattening,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(k3_subset_1(X0,X3),X1)) & (r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.53    inference(nnf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : ((k7_setfam_1(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k7_setfam_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).
% 0.22/0.53  % (15220)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.53  fof(f103,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(sK3(sK0,X0,sK1),k1_zfmisc_1(sK0)) | r2_hidden(k3_subset_1(sK0,sK3(sK0,X0,sK1)),X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | sK1 = k7_setfam_1(sK0,X0)) ) | (~spl4_3 | ~spl4_6)),
% 0.22/0.53    inference(resolution,[],[f101,f63])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl4_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f62])).
% 0.22/0.53  fof(f101,plain,(
% 0.22/0.53    ( ! [X12,X11] : (~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(X11))) | sK1 = k7_setfam_1(X11,X12) | r2_hidden(k3_subset_1(X11,sK3(X11,X12,sK1)),X12) | ~m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(X11))) | ~m1_subset_1(sK3(X11,X12,sK1),k1_zfmisc_1(sK0))) ) | ~spl4_6),
% 0.22/0.53    inference(resolution,[],[f46,f94])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(k3_subset_1(X0,sK3(X0,X1,X2)),X1) | k7_setfam_1(X0,X1) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f32])).
% 0.22/0.53  fof(f95,plain,(
% 0.22/0.53    ~spl4_3 | spl4_6 | ~spl4_4 | ~spl4_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f91,f72,f66,f93,f62])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    spl4_4 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    spl4_5 <=> sK1 = k7_setfam_1(sK0,k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))) ) | (~spl4_4 | ~spl4_5)),
% 0.22/0.53    inference(superposition,[],[f88,f73])).
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    sK1 = k7_setfam_1(sK0,k1_xboole_0) | ~spl4_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f72])).
% 0.22/0.53  fof(f88,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(X1,k7_setfam_1(X0,k1_xboole_0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(k7_setfam_1(X0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | ~spl4_4),
% 0.22/0.53    inference(resolution,[],[f85,f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    ( ! [X4,X3] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X3))) | ~m1_subset_1(k7_setfam_1(X3,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X3))) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | ~r2_hidden(X4,k7_setfam_1(X3,k1_xboole_0))) ) | ~spl4_4),
% 0.22/0.53    inference(resolution,[],[f83,f37])).
% 0.22/0.53  fof(f83,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r2_hidden(X0,k7_setfam_1(X1,X2))) ) | ~spl4_4),
% 0.22/0.53    inference(resolution,[],[f81,f67])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    v1_xboole_0(k1_xboole_0) | ~spl4_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f66])).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    ( ! [X10,X8,X7,X9] : (~v1_xboole_0(X10) | ~m1_subset_1(X7,k1_zfmisc_1(X8)) | ~m1_subset_1(k7_setfam_1(X8,X9),k1_zfmisc_1(k1_zfmisc_1(X8))) | ~m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(X8))) | ~m1_subset_1(X9,k1_zfmisc_1(X10)) | ~r2_hidden(X7,k7_setfam_1(X8,X9))) )),
% 0.22/0.53    inference(resolution,[],[f52,f50])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ( ! [X4,X0,X1] : (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,k7_setfam_1(X0,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(X0)) | ~m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.53    inference(equality_resolution,[],[f43])).
% 0.22/0.53  % (15223)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.53  % (15223)Refutation not found, incomplete strategy% (15223)------------------------------
% 0.22/0.53  % (15223)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (15223)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (15223)Memory used [KB]: 10618
% 0.22/0.53  % (15223)Time elapsed: 0.116 s
% 0.22/0.53  % (15223)------------------------------
% 0.22/0.53  % (15223)------------------------------
% 0.22/0.53  % (15219)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X1] : (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,k1_zfmisc_1(X0)) | k7_setfam_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f32])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    ~spl4_3 | spl4_5 | ~spl4_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f69,f54,f72,f62])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    sK1 = k7_setfam_1(sK0,k1_xboole_0) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl4_1),
% 0.22/0.53    inference(superposition,[],[f41,f55])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    spl4_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f36,f66])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    v1_xboole_0(k1_xboole_0)),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    v1_xboole_0(k1_xboole_0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    spl4_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f33,f62])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    k1_xboole_0 = k7_setfam_1(sK0,sK1) & k1_xboole_0 != sK1 & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ? [X0,X1] : (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (k1_xboole_0 = k7_setfam_1(sK0,sK1) & k1_xboole_0 != sK1 & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ? [X0,X1] : (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.53    inference(flattening,[],[f13])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ? [X0,X1] : ((k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.53    inference(ennf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 0.22/0.53    inference(negated_conjecture,[],[f10])).
% 0.22/0.53  fof(f10,conjecture,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    ~spl4_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f34,f58])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    k1_xboole_0 != sK1),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    spl4_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f35,f54])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    k1_xboole_0 = k7_setfam_1(sK0,sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (15209)------------------------------
% 0.22/0.53  % (15209)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (15209)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (15209)Memory used [KB]: 10746
% 0.22/0.53  % (15209)Time elapsed: 0.078 s
% 0.22/0.53  % (15209)------------------------------
% 0.22/0.53  % (15209)------------------------------
% 0.22/0.53  % (15202)Success in time 0.171 s
%------------------------------------------------------------------------------
