%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0418+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:29 EST 2020

% Result     : Theorem 1.64s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 161 expanded)
%              Number of leaves         :   19 (  61 expanded)
%              Depth                    :   12
%              Number of atoms          :  304 ( 638 expanded)
%              Number of equality atoms :   25 (  50 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1939,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1377,f1382,f1391,f1392,f1482,f1764,f1808,f1813,f1818,f1909,f1910,f1938])).

fof(f1938,plain,
    ( ~ spl32_2
    | ~ spl32_4
    | spl32_9
    | ~ spl32_18
    | ~ spl32_20
    | ~ spl32_21 ),
    inference(avatar_contradiction_clause,[],[f1937])).

fof(f1937,plain,
    ( $false
    | ~ spl32_2
    | ~ spl32_4
    | spl32_9
    | ~ spl32_18
    | ~ spl32_20
    | ~ spl32_21 ),
    inference(subsumption_resolution,[],[f1936,f1390])).

fof(f1390,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl32_4 ),
    inference(avatar_component_clause,[],[f1388])).

fof(f1388,plain,
    ( spl32_4
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_4])])).

fof(f1936,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ spl32_2
    | spl32_9
    | ~ spl32_18
    | ~ spl32_20
    | ~ spl32_21 ),
    inference(forward_demodulation,[],[f1929,f1812])).

fof(f1812,plain,
    ( sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl32_20 ),
    inference(avatar_component_clause,[],[f1810])).

fof(f1810,plain,
    ( spl32_20
  <=> sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_20])])).

fof(f1929,plain,
    ( ~ r2_hidden(k3_subset_1(sK0,k4_xboole_0(sK0,sK2)),sK1)
    | ~ spl32_2
    | spl32_9
    | ~ spl32_18
    | ~ spl32_21 ),
    inference(unit_resulting_resolution,[],[f1381,f1763,f1817,f1480,f1304])).

fof(f1304,plain,(
    ! [X4,X0,X1] :
      ( ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | r2_hidden(X4,k7_setfam_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f953])).

fof(f953,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | k7_setfam_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f825])).

fof(f825,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k3_subset_1(X0,sK6(X0,X1,X2)),X1)
                  | ~ r2_hidden(sK6(X0,X1,X2),X2) )
                & ( r2_hidden(k3_subset_1(X0,sK6(X0,X1,X2)),X1)
                  | r2_hidden(sK6(X0,X1,X2),X2) )
                & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(X0)) ) )
            & ( ! [X4] :
                  ( ( ( r2_hidden(X4,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X4),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X4),X1)
                      | ~ r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f823,f824])).

fof(f824,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(k3_subset_1(X0,X3),X1)
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,k1_zfmisc_1(X0)) )
     => ( ( ~ r2_hidden(k3_subset_1(X0,sK6(X0,X1,X2)),X1)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( r2_hidden(k3_subset_1(X0,sK6(X0,X1,X2)),X1)
          | r2_hidden(sK6(X0,X1,X2),X2) )
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f823,plain,(
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
    inference(rectify,[],[f822])).

fof(f822,plain,(
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
    inference(flattening,[],[f821])).

fof(f821,plain,(
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
    inference(nnf_transformation,[],[f620])).

fof(f620,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f552])).

fof(f552,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_setfam_1)).

fof(f1480,plain,
    ( ~ r2_hidden(k4_xboole_0(sK0,sK2),k7_setfam_1(sK0,sK1))
    | spl32_9 ),
    inference(avatar_component_clause,[],[f1479])).

fof(f1479,plain,
    ( spl32_9
  <=> r2_hidden(k4_xboole_0(sK0,sK2),k7_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_9])])).

fof(f1817,plain,
    ( m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl32_21 ),
    inference(avatar_component_clause,[],[f1815])).

fof(f1815,plain,
    ( spl32_21
  <=> m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_21])])).

fof(f1763,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl32_18 ),
    inference(avatar_component_clause,[],[f1761])).

fof(f1761,plain,
    ( spl32_18
  <=> m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_18])])).

fof(f1381,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl32_2 ),
    inference(avatar_component_clause,[],[f1379])).

fof(f1379,plain,
    ( spl32_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_2])])).

fof(f1910,plain,
    ( k3_subset_1(sK0,sK2) != k4_xboole_0(sK0,sK2)
    | r2_hidden(k3_subset_1(sK0,sK2),k7_setfam_1(sK0,sK1))
    | ~ r2_hidden(k4_xboole_0(sK0,sK2),k7_setfam_1(sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1909,plain,
    ( ~ spl32_2
    | spl32_4
    | ~ spl32_9
    | ~ spl32_18
    | ~ spl32_20
    | ~ spl32_21 ),
    inference(avatar_contradiction_clause,[],[f1908])).

fof(f1908,plain,
    ( $false
    | ~ spl32_2
    | spl32_4
    | ~ spl32_9
    | ~ spl32_18
    | ~ spl32_20
    | ~ spl32_21 ),
    inference(subsumption_resolution,[],[f1907,f1389])).

fof(f1389,plain,
    ( ~ r2_hidden(sK2,sK1)
    | spl32_4 ),
    inference(avatar_component_clause,[],[f1388])).

fof(f1907,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl32_2
    | ~ spl32_9
    | ~ spl32_18
    | ~ spl32_20
    | ~ spl32_21 ),
    inference(forward_demodulation,[],[f1876,f1812])).

fof(f1876,plain,
    ( r2_hidden(k3_subset_1(sK0,k4_xboole_0(sK0,sK2)),sK1)
    | ~ spl32_2
    | ~ spl32_9
    | ~ spl32_18
    | ~ spl32_21 ),
    inference(unit_resulting_resolution,[],[f1763,f1481,f1381,f1817,f1305])).

fof(f1305,plain,(
    ! [X4,X0,X1] :
      ( ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ r2_hidden(X4,k7_setfam_1(X0,X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f952])).

fof(f952,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | k7_setfam_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f825])).

fof(f1481,plain,
    ( r2_hidden(k4_xboole_0(sK0,sK2),k7_setfam_1(sK0,sK1))
    | ~ spl32_9 ),
    inference(avatar_component_clause,[],[f1479])).

fof(f1818,plain,
    ( spl32_21
    | ~ spl32_2 ),
    inference(avatar_split_clause,[],[f1499,f1379,f1815])).

fof(f1499,plain,
    ( m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl32_2 ),
    inference(unit_resulting_resolution,[],[f1381,f958])).

fof(f958,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f623])).

fof(f623,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f559])).

fof(f559,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f1813,plain,
    ( spl32_20
    | ~ spl32_1 ),
    inference(avatar_split_clause,[],[f1477,f1374,f1810])).

fof(f1374,plain,
    ( spl32_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_1])])).

fof(f1477,plain,
    ( sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl32_1 ),
    inference(backward_demodulation,[],[f1455,f1459])).

fof(f1459,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl32_1 ),
    inference(unit_resulting_resolution,[],[f1376,f982])).

fof(f982,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f647])).

fof(f647,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f462])).

fof(f462,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f1376,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl32_1 ),
    inference(avatar_component_clause,[],[f1374])).

fof(f1455,plain,
    ( sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2))
    | ~ spl32_1 ),
    inference(unit_resulting_resolution,[],[f1376,f981])).

fof(f981,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f646])).

fof(f646,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f487])).

fof(f487,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f1808,plain,
    ( spl32_19
    | ~ spl32_1 ),
    inference(avatar_split_clause,[],[f1459,f1374,f1805])).

fof(f1805,plain,
    ( spl32_19
  <=> k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_19])])).

fof(f1764,plain,
    ( spl32_18
    | ~ spl32_1 ),
    inference(avatar_split_clause,[],[f1476,f1374,f1761])).

fof(f1476,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl32_1 ),
    inference(backward_demodulation,[],[f1439,f1459])).

fof(f1439,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl32_1 ),
    inference(unit_resulting_resolution,[],[f1376,f983])).

fof(f983,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f648])).

fof(f648,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f466])).

fof(f466,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f1482,plain,
    ( spl32_9
    | ~ spl32_1
    | ~ spl32_3 ),
    inference(avatar_split_clause,[],[f1470,f1384,f1374,f1479])).

fof(f1384,plain,
    ( spl32_3
  <=> r2_hidden(k3_subset_1(sK0,sK2),k7_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_3])])).

fof(f1470,plain,
    ( r2_hidden(k4_xboole_0(sK0,sK2),k7_setfam_1(sK0,sK1))
    | ~ spl32_1
    | ~ spl32_3 ),
    inference(backward_demodulation,[],[f1386,f1459])).

fof(f1386,plain,
    ( r2_hidden(k3_subset_1(sK0,sK2),k7_setfam_1(sK0,sK1))
    | ~ spl32_3 ),
    inference(avatar_component_clause,[],[f1384])).

fof(f1392,plain,
    ( ~ spl32_3
    | ~ spl32_4 ),
    inference(avatar_split_clause,[],[f940,f1388,f1384])).

fof(f940,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ r2_hidden(k3_subset_1(sK0,sK2),k7_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f810])).

fof(f810,plain,
    ( ( ~ r2_hidden(sK2,sK1)
      | ~ r2_hidden(k3_subset_1(sK0,sK2),k7_setfam_1(sK0,sK1)) )
    & ( r2_hidden(sK2,sK1)
      | r2_hidden(k3_subset_1(sK0,sK2),k7_setfam_1(sK0,sK1)) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f807,f809,f808])).

fof(f808,plain,
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

fof(f809,plain,
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

fof(f807,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f806])).

fof(f806,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f616])).

fof(f616,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
          <~> r2_hidden(X2,X1) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f603])).

fof(f603,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
            <=> r2_hidden(X2,X1) ) ) ) ),
    inference(negated_conjecture,[],[f602])).

fof(f602,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
          <=> r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_setfam_1)).

fof(f1391,plain,
    ( spl32_3
    | spl32_4 ),
    inference(avatar_split_clause,[],[f939,f1388,f1384])).

fof(f939,plain,
    ( r2_hidden(sK2,sK1)
    | r2_hidden(k3_subset_1(sK0,sK2),k7_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f810])).

fof(f1382,plain,(
    spl32_2 ),
    inference(avatar_split_clause,[],[f937,f1379])).

fof(f937,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f810])).

fof(f1377,plain,(
    spl32_1 ),
    inference(avatar_split_clause,[],[f938,f1374])).

fof(f938,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f810])).
%------------------------------------------------------------------------------
