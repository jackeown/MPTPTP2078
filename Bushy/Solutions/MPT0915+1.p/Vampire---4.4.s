%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t75_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:13 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 213 expanded)
%              Number of leaves         :   17 (  71 expanded)
%              Depth                    :   10
%              Number of atoms          :  353 (1059 expanded)
%              Number of equality atoms :  159 ( 693 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f201,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f70,f77,f84,f91,f98,f105,f112,f119,f126,f146,f161,f169,f184,f200])).

fof(f200,plain,
    ( spl9_3
    | spl9_5
    | spl9_7
    | spl9_9
    | spl9_11
    | spl9_13
    | ~ spl9_14
    | ~ spl9_16
    | spl9_23 ),
    inference(avatar_contradiction_clause,[],[f199])).

fof(f199,plain,
    ( $false
    | ~ spl9_3
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_23 ),
    inference(subsumption_resolution,[],[f198,f195])).

fof(f195,plain,
    ( k6_mcart_1(sK3,sK4,sK5,sK6) != k2_mcart_1(k1_mcart_1(sK6))
    | ~ spl9_3
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_14
    | ~ spl9_23 ),
    inference(backward_demodulation,[],[f194,f139])).

fof(f139,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK6) != k6_mcart_1(sK3,sK4,sK5,sK6)
    | ~ spl9_23 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl9_23
  <=> k6_mcart_1(sK0,sK1,sK2,sK6) != k6_mcart_1(sK3,sK4,sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f194,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | ~ spl9_3
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_14 ),
    inference(subsumption_resolution,[],[f193,f69])).

fof(f69,plain,
    ( k1_xboole_0 != sK0
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl9_3
  <=> k1_xboole_0 != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f193,plain,
    ( k1_xboole_0 = sK0
    | k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_14 ),
    inference(subsumption_resolution,[],[f192,f83])).

fof(f83,plain,
    ( k1_xboole_0 != sK2
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl9_7
  <=> k1_xboole_0 != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f192,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | ~ spl9_5
    | ~ spl9_14 ),
    inference(subsumption_resolution,[],[f186,f76])).

fof(f76,plain,
    ( k1_xboole_0 != sK1
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl9_5
  <=> k1_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f186,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | ~ spl9_14 ),
    inference(resolution,[],[f43,f111])).

fof(f111,plain,
    ( m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl9_14
  <=> m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t75_mcart_1.p',t50_mcart_1)).

fof(f198,plain,
    ( k6_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f197,f90])).

fof(f90,plain,
    ( k1_xboole_0 != sK3
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl9_9
  <=> k1_xboole_0 != sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f197,plain,
    ( k1_xboole_0 = sK3
    | k6_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f196,f104])).

fof(f104,plain,
    ( k1_xboole_0 != sK5
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl9_13
  <=> k1_xboole_0 != sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f196,plain,
    ( k1_xboole_0 = sK5
    | k1_xboole_0 = sK3
    | k6_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | ~ spl9_11
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f187,f97])).

fof(f97,plain,
    ( k1_xboole_0 != sK4
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl9_11
  <=> k1_xboole_0 != sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f187,plain,
    ( k1_xboole_0 = sK4
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK3
    | k6_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | ~ spl9_16 ),
    inference(resolution,[],[f43,f118])).

fof(f118,plain,
    ( m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5))
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl9_16
  <=> m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f184,plain,
    ( spl9_3
    | spl9_5
    | spl9_7
    | spl9_9
    | spl9_11
    | spl9_13
    | ~ spl9_14
    | ~ spl9_16
    | spl9_21 ),
    inference(avatar_contradiction_clause,[],[f183])).

fof(f183,plain,
    ( $false
    | ~ spl9_3
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f182,f179])).

fof(f179,plain,
    ( k5_mcart_1(sK3,sK4,sK5,sK6) != k1_mcart_1(k1_mcart_1(sK6))
    | ~ spl9_3
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_14
    | ~ spl9_21 ),
    inference(backward_demodulation,[],[f178,f133])).

fof(f133,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK6) != k5_mcart_1(sK3,sK4,sK5,sK6)
    | ~ spl9_21 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl9_21
  <=> k5_mcart_1(sK0,sK1,sK2,sK6) != k5_mcart_1(sK3,sK4,sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f178,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | ~ spl9_3
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_14 ),
    inference(subsumption_resolution,[],[f177,f69])).

fof(f177,plain,
    ( k1_xboole_0 = sK0
    | k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_14 ),
    inference(subsumption_resolution,[],[f176,f83])).

fof(f176,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | ~ spl9_5
    | ~ spl9_14 ),
    inference(subsumption_resolution,[],[f170,f76])).

fof(f170,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | ~ spl9_14 ),
    inference(resolution,[],[f42,f111])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f182,plain,
    ( k5_mcart_1(sK3,sK4,sK5,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f181,f90])).

fof(f181,plain,
    ( k1_xboole_0 = sK3
    | k5_mcart_1(sK3,sK4,sK5,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f180,f104])).

fof(f180,plain,
    ( k1_xboole_0 = sK5
    | k1_xboole_0 = sK3
    | k5_mcart_1(sK3,sK4,sK5,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | ~ spl9_11
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f171,f97])).

fof(f171,plain,
    ( k1_xboole_0 = sK4
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK3
    | k5_mcart_1(sK3,sK4,sK5,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | ~ spl9_16 ),
    inference(resolution,[],[f42,f118])).

fof(f169,plain,
    ( spl9_26
    | spl9_3
    | spl9_5
    | spl9_7
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f155,f110,f82,f75,f68,f167])).

fof(f167,plain,
    ( spl9_26
  <=> k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f155,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6)
    | ~ spl9_3
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_14 ),
    inference(subsumption_resolution,[],[f154,f69])).

fof(f154,plain,
    ( k1_xboole_0 = sK0
    | k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6)
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_14 ),
    inference(subsumption_resolution,[],[f153,f83])).

fof(f153,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6)
    | ~ spl9_5
    | ~ spl9_14 ),
    inference(subsumption_resolution,[],[f147,f76])).

fof(f147,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6)
    | ~ spl9_14 ),
    inference(resolution,[],[f44,f111])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f161,plain,
    ( spl9_3
    | spl9_5
    | spl9_7
    | spl9_9
    | spl9_11
    | spl9_13
    | ~ spl9_14
    | ~ spl9_16
    | spl9_25 ),
    inference(avatar_contradiction_clause,[],[f160])).

fof(f160,plain,
    ( $false
    | ~ spl9_3
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_25 ),
    inference(subsumption_resolution,[],[f159,f156])).

fof(f156,plain,
    ( k7_mcart_1(sK3,sK4,sK5,sK6) != k2_mcart_1(sK6)
    | ~ spl9_3
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_14
    | ~ spl9_25 ),
    inference(backward_demodulation,[],[f155,f145])).

fof(f145,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK6) != k7_mcart_1(sK3,sK4,sK5,sK6)
    | ~ spl9_25 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl9_25
  <=> k7_mcart_1(sK0,sK1,sK2,sK6) != k7_mcart_1(sK3,sK4,sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f159,plain,
    ( k7_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(sK6)
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f158,f90])).

fof(f158,plain,
    ( k1_xboole_0 = sK3
    | k7_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(sK6)
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f157,f104])).

fof(f157,plain,
    ( k1_xboole_0 = sK5
    | k1_xboole_0 = sK3
    | k7_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(sK6)
    | ~ spl9_11
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f148,f97])).

fof(f148,plain,
    ( k1_xboole_0 = sK4
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK3
    | k7_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(sK6)
    | ~ spl9_16 ),
    inference(resolution,[],[f44,f118])).

fof(f146,plain,
    ( ~ spl9_21
    | ~ spl9_23
    | ~ spl9_25 ),
    inference(avatar_split_clause,[],[f56,f144,f138,f132])).

fof(f56,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK6) != k7_mcart_1(sK3,sK4,sK5,sK6)
    | k6_mcart_1(sK0,sK1,sK2,sK6) != k6_mcart_1(sK3,sK4,sK5,sK6)
    | k5_mcart_1(sK0,sK1,sK2,sK6) != k5_mcart_1(sK3,sK4,sK5,sK6) ),
    inference(forward_demodulation,[],[f55,f33])).

fof(f33,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ? [X6] :
          ( ? [X7] :
              ( ( k7_mcart_1(X0,X1,X2,X6) != k7_mcart_1(X3,X4,X5,X7)
                | k6_mcart_1(X0,X1,X2,X6) != k6_mcart_1(X3,X4,X5,X7)
                | k5_mcart_1(X0,X1,X2,X6) != k5_mcart_1(X3,X4,X5,X7) )
              & X6 = X7
              & m1_subset_1(X7,k3_zfmisc_1(X3,X4,X5)) )
          & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
      & k1_xboole_0 != X5
      & k1_xboole_0 != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ~ ( ? [X6] :
              ( ? [X7] :
                  ( ~ ( k7_mcart_1(X0,X1,X2,X6) = k7_mcart_1(X3,X4,X5,X7)
                      & k6_mcart_1(X0,X1,X2,X6) = k6_mcart_1(X3,X4,X5,X7)
                      & k5_mcart_1(X0,X1,X2,X6) = k5_mcart_1(X3,X4,X5,X7) )
                  & X6 = X7
                  & m1_subset_1(X7,k3_zfmisc_1(X3,X4,X5)) )
              & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
          & k1_xboole_0 != X5
          & k1_xboole_0 != X4
          & k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ~ ( ? [X6] :
            ( ? [X7] :
                ( ~ ( k7_mcart_1(X0,X1,X2,X6) = k7_mcart_1(X3,X4,X5,X7)
                    & k6_mcart_1(X0,X1,X2,X6) = k6_mcart_1(X3,X4,X5,X7)
                    & k5_mcart_1(X0,X1,X2,X6) = k5_mcart_1(X3,X4,X5,X7) )
                & X6 = X7
                & m1_subset_1(X7,k3_zfmisc_1(X3,X4,X5)) )
            & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X5
        & k1_xboole_0 != X4
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t75_mcart_1.p',t75_mcart_1)).

fof(f55,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK6) != k6_mcart_1(sK3,sK4,sK5,sK6)
    | k5_mcart_1(sK0,sK1,sK2,sK6) != k5_mcart_1(sK3,sK4,sK5,sK6)
    | k7_mcart_1(sK0,sK1,sK2,sK6) != k7_mcart_1(sK3,sK4,sK5,sK7) ),
    inference(forward_demodulation,[],[f54,f33])).

fof(f54,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK6) != k5_mcart_1(sK3,sK4,sK5,sK6)
    | k6_mcart_1(sK0,sK1,sK2,sK6) != k6_mcart_1(sK3,sK4,sK5,sK7)
    | k7_mcart_1(sK0,sK1,sK2,sK6) != k7_mcart_1(sK3,sK4,sK5,sK7) ),
    inference(forward_demodulation,[],[f31,f33])).

fof(f31,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK6) != k5_mcart_1(sK3,sK4,sK5,sK7)
    | k6_mcart_1(sK0,sK1,sK2,sK6) != k6_mcart_1(sK3,sK4,sK5,sK7)
    | k7_mcart_1(sK0,sK1,sK2,sK6) != k7_mcart_1(sK3,sK4,sK5,sK7) ),
    inference(cnf_transformation,[],[f21])).

fof(f126,plain,(
    spl9_18 ),
    inference(avatar_split_clause,[],[f52,f124])).

fof(f124,plain,
    ( spl9_18
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f52,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t75_mcart_1.p',d2_xboole_0)).

fof(f119,plain,(
    spl9_16 ),
    inference(avatar_split_clause,[],[f53,f117])).

fof(f53,plain,(
    m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(forward_demodulation,[],[f32,f33])).

fof(f32,plain,(
    m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f21])).

fof(f112,plain,(
    spl9_14 ),
    inference(avatar_split_clause,[],[f34,f110])).

fof(f34,plain,(
    m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f21])).

fof(f105,plain,(
    ~ spl9_13 ),
    inference(avatar_split_clause,[],[f40,f103])).

fof(f40,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f21])).

fof(f98,plain,(
    ~ spl9_11 ),
    inference(avatar_split_clause,[],[f39,f96])).

fof(f39,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f21])).

fof(f91,plain,(
    ~ spl9_9 ),
    inference(avatar_split_clause,[],[f38,f89])).

fof(f38,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f21])).

fof(f84,plain,(
    ~ spl9_7 ),
    inference(avatar_split_clause,[],[f37,f82])).

fof(f37,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f21])).

fof(f77,plain,(
    ~ spl9_5 ),
    inference(avatar_split_clause,[],[f36,f75])).

fof(f36,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f21])).

fof(f70,plain,(
    ~ spl9_3 ),
    inference(avatar_split_clause,[],[f35,f68])).

fof(f35,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f21])).

fof(f63,plain,(
    spl9_0 ),
    inference(avatar_split_clause,[],[f33,f61])).

fof(f61,plain,
    ( spl9_0
  <=> sK6 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_0])])).
%------------------------------------------------------------------------------
