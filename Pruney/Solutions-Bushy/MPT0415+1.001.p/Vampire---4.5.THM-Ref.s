%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0415+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 162 expanded)
%              Number of leaves         :   25 (  67 expanded)
%              Depth                    :   14
%              Number of atoms          :  318 ( 478 expanded)
%              Number of equality atoms :   53 ( 110 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f206,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f57,f61,f65,f70,f86,f98,f182,f194,f195,f201,f205])).

fof(f205,plain,
    ( spl4_10
    | ~ spl4_3
    | ~ spl4_5
    | spl4_12 ),
    inference(avatar_split_clause,[],[f203,f199,f68,f59,f189])).

fof(f189,plain,
    ( spl4_10
  <=> o_0_0_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f59,plain,
    ( spl4_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f68,plain,
    ( spl4_5
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f199,plain,
    ( spl4_12
  <=> m1_subset_1(sK2(sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f203,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | o_0_0_xboole_0 = sK1
    | ~ spl4_5
    | spl4_12 ),
    inference(resolution,[],[f202,f37])).

fof(f37,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f4,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f202,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2(sK1),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | o_0_0_xboole_0 = X0 )
    | ~ spl4_5
    | spl4_12 ),
    inference(resolution,[],[f200,f76])).

fof(f76,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(X1,X2)
        | ~ m1_subset_1(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
        | o_0_0_xboole_0 = X0 )
    | ~ spl4_5 ),
    inference(resolution,[],[f75,f47])).

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f75,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,X1)
        | o_0_0_xboole_0 = X1
        | ~ m1_subset_1(X0,X1) )
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f74,f69])).

fof(f69,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f38,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f200,plain,
    ( ~ m1_subset_1(sK2(sK1),k1_zfmisc_1(sK0))
    | spl4_12 ),
    inference(avatar_component_clause,[],[f199])).

fof(f201,plain,
    ( ~ spl4_12
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f197,f192,f199])).

fof(f192,plain,
    ( spl4_11
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | ~ m1_subset_1(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f197,plain,
    ( ~ m1_subset_1(sK2(sK1),k1_zfmisc_1(sK0))
    | ~ spl4_11 ),
    inference(resolution,[],[f193,f37])).

fof(f193,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f192])).

fof(f195,plain,
    ( o_0_0_xboole_0 != sK1
    | o_0_0_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f194,plain,
    ( spl4_10
    | spl4_11
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f185,f180,f68,f192,f189])).

fof(f180,plain,
    ( spl4_9
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f185,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | o_0_0_xboole_0 = sK1
        | ~ m1_subset_1(X0,sK1) )
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(resolution,[],[f181,f75])).

fof(f181,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f180])).

fof(f182,plain,
    ( ~ spl4_3
    | spl4_9
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f178,f96,f84,f63,f180,f59])).

fof(f63,plain,
    ( spl4_4
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f84,plain,
    ( spl4_7
  <=> sK1 = k7_setfam_1(sK0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f96,plain,
    ( spl4_8
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f178,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) )
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f177,f85])).

fof(f85,plain,
    ( sK1 = k7_setfam_1(sK0,o_0_0_xboole_0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f84])).

fof(f177,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | ~ r2_hidden(X0,k7_setfam_1(sK0,o_0_0_xboole_0)) )
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f175,f85])).

fof(f175,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k7_setfam_1(sK0,o_0_0_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | ~ r2_hidden(X0,k7_setfam_1(sK0,o_0_0_xboole_0)) )
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(resolution,[],[f173,f97])).

fof(f97,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f96])).

fof(f173,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X1)))
        | ~ m1_subset_1(k7_setfam_1(X1,o_0_0_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r2_hidden(X0,k7_setfam_1(X1,o_0_0_xboole_0)) )
    | ~ spl4_4 ),
    inference(resolution,[],[f171,f64])).

fof(f64,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f63])).

fof(f171,plain,(
    ! [X8,X7,X9] :
      ( ~ v1_xboole_0(X9)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X8))
      | ~ m1_subset_1(k7_setfam_1(X8,X9),k1_zfmisc_1(k1_zfmisc_1(X8)))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(X8)))
      | ~ r2_hidden(X7,k7_setfam_1(X8,X9)) ) ),
    inference(resolution,[],[f49,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f49,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ r2_hidden(X4,k7_setfam_1(X0,X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | k7_setfam_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).

fof(f30,plain,(
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
            & ( ! [X4] :
                  ( ( ( r2_hidden(X4,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X4),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X4),X1)
                      | ~ r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(rectify,[],[f28])).

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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f98,plain,
    ( spl4_8
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f94,f68,f59,f51,f96])).

fof(f51,plain,
    ( spl4_1
  <=> k1_xboole_0 = k7_setfam_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f94,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f93,f69])).

fof(f93,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f91,f52])).

fof(f52,plain,
    ( k1_xboole_0 = k7_setfam_1(sK0,sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f91,plain,
    ( m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_3 ),
    inference(resolution,[],[f40,f60])).

fof(f60,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f86,plain,
    ( ~ spl4_3
    | spl4_7
    | ~ spl4_1
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f81,f68,f51,f84,f59])).

fof(f81,plain,
    ( sK1 = k7_setfam_1(sK0,o_0_0_xboole_0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_1
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f80,f69])).

fof(f80,plain,
    ( sK1 = k7_setfam_1(sK0,k1_xboole_0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_1 ),
    inference(superposition,[],[f39,f52])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(f70,plain,
    ( spl4_5
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f66,f63,f68])).

fof(f66,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl4_4 ),
    inference(resolution,[],[f36,f64])).

fof(f65,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f35,f63])).

fof(f35,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f61,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f32,f59])).

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( k1_xboole_0 = k7_setfam_1(sK0,sK1)
    & k1_xboole_0 != sK1
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( k7_setfam_1(X0,X1) = k1_xboole_0
        & k1_xboole_0 != X1
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( k1_xboole_0 = k7_setfam_1(sK0,sK1)
      & k1_xboole_0 != sK1
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k7_setfam_1(X0,X1) = k1_xboole_0
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k7_setfam_1(X0,X1) = k1_xboole_0
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ~ ( k7_setfam_1(X0,X1) = k1_xboole_0
            & k1_xboole_0 != X1 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ~ ( k7_setfam_1(X0,X1) = k1_xboole_0
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).

fof(f57,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f33,f55])).

fof(f55,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f33,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f24])).

fof(f53,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f34,f51])).

fof(f34,plain,(
    k1_xboole_0 = k7_setfam_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

%------------------------------------------------------------------------------
