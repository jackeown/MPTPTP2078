%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:28 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 255 expanded)
%              Number of leaves         :   25 ( 109 expanded)
%              Depth                    :   11
%              Number of atoms          :  518 (1221 expanded)
%              Number of equality atoms :  231 ( 604 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f261,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f48,f53,f58,f63,f85,f98,f157,f165,f173,f182,f194,f199,f218,f224,f250,f260])).

fof(f260,plain,
    ( spl11_1
    | spl11_2
    | spl11_3
    | ~ spl11_4
    | spl11_5
    | ~ spl11_15
    | ~ spl11_20 ),
    inference(avatar_contradiction_clause,[],[f257])).

fof(f257,plain,
    ( $false
    | spl11_1
    | spl11_2
    | spl11_3
    | ~ spl11_4
    | spl11_5
    | ~ spl11_15
    | ~ spl11_20 ),
    inference(unit_resulting_resolution,[],[f42,f47,f52,f193,f57,f62,f249,f29])).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sK6(X3,X4) != X4
      | k6_mcart_1(X0,X1,X2,X3) = X4
      | ~ m1_subset_1(X4,X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( ( k6_mcart_1(X0,X1,X2,X3) = X4
                  | ( sK6(X3,X4) != X4
                    & k3_mcart_1(sK5(X3,X4),sK6(X3,X4),sK7(X3,X4)) = X3 ) )
                & ( ! [X8,X9,X10] :
                      ( X4 = X9
                      | k3_mcart_1(X8,X9,X10) != X3 )
                  | k6_mcart_1(X0,X1,X2,X3) != X4 ) )
              | ~ m1_subset_1(X4,X1) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f14,f15])).

fof(f15,plain,(
    ! [X4,X3] :
      ( ? [X5,X6,X7] :
          ( X4 != X6
          & k3_mcart_1(X5,X6,X7) = X3 )
     => ( sK6(X3,X4) != X4
        & k3_mcart_1(sK5(X3,X4),sK6(X3,X4),sK7(X3,X4)) = X3 ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( ( k6_mcart_1(X0,X1,X2,X3) = X4
                  | ? [X5,X6,X7] :
                      ( X4 != X6
                      & k3_mcart_1(X5,X6,X7) = X3 ) )
                & ( ! [X8,X9,X10] :
                      ( X4 = X9
                      | k3_mcart_1(X8,X9,X10) != X3 )
                  | k6_mcart_1(X0,X1,X2,X3) != X4 ) )
              | ~ m1_subset_1(X4,X1) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(rectify,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( ( k6_mcart_1(X0,X1,X2,X3) = X4
                  | ? [X5,X6,X7] :
                      ( X4 != X6
                      & k3_mcart_1(X5,X6,X7) = X3 ) )
                & ( ! [X5,X6,X7] :
                      ( X4 = X6
                      | k3_mcart_1(X5,X6,X7) != X3 )
                  | k6_mcart_1(X0,X1,X2,X3) != X4 ) )
              | ~ m1_subset_1(X4,X1) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( k6_mcart_1(X0,X1,X2,X3) = X4
              <=> ! [X5,X6,X7] :
                    ( X4 = X6
                    | k3_mcart_1(X5,X6,X7) != X3 ) )
              | ~ m1_subset_1(X4,X1) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ! [X4] :
                  ( m1_subset_1(X4,X1)
                 => ( k6_mcart_1(X0,X1,X2,X3) = X4
                  <=> ! [X5,X6,X7] :
                        ( k3_mcart_1(X5,X6,X7) = X3
                       => X4 = X6 ) ) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_mcart_1)).

fof(f249,plain,
    ( sK3 = sK6(sK4,sK3)
    | ~ spl11_20 ),
    inference(avatar_component_clause,[],[f247])).

fof(f247,plain,
    ( spl11_20
  <=> sK3 = sK6(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f62,plain,
    ( sK3 != k6_mcart_1(sK0,sK1,sK2,sK4)
    | spl11_5 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl11_5
  <=> sK3 = k6_mcart_1(sK0,sK1,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f57,plain,
    ( m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl11_4
  <=> m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f193,plain,
    ( m1_subset_1(sK3,sK1)
    | ~ spl11_15 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl11_15
  <=> m1_subset_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).

fof(f52,plain,
    ( k1_xboole_0 != sK2
    | spl11_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl11_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f47,plain,
    ( k1_xboole_0 != sK1
    | spl11_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl11_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f42,plain,
    ( k1_xboole_0 != sK0
    | spl11_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl11_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f250,plain,
    ( spl11_20
    | ~ spl11_17
    | ~ spl11_18 ),
    inference(avatar_split_clause,[],[f240,f221,f215,f247])).

fof(f215,plain,
    ( spl11_17
  <=> ! [X7,X8,X6] :
        ( sK4 != k3_mcart_1(X6,X7,X8)
        | sK3 = X7 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).

fof(f221,plain,
    ( spl11_18
  <=> sK4 = k3_mcart_1(sK5(sK4,sK3),sK6(sK4,sK3),sK7(sK4,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f240,plain,
    ( sK3 = sK6(sK4,sK3)
    | ~ spl11_17
    | ~ spl11_18 ),
    inference(trivial_inequality_removal,[],[f239])).

fof(f239,plain,
    ( sK4 != sK4
    | sK3 = sK6(sK4,sK3)
    | ~ spl11_17
    | ~ spl11_18 ),
    inference(superposition,[],[f216,f223])).

fof(f223,plain,
    ( sK4 = k3_mcart_1(sK5(sK4,sK3),sK6(sK4,sK3),sK7(sK4,sK3))
    | ~ spl11_18 ),
    inference(avatar_component_clause,[],[f221])).

fof(f216,plain,
    ( ! [X6,X8,X7] :
        ( sK4 != k3_mcart_1(X6,X7,X8)
        | sK3 = X7 )
    | ~ spl11_17 ),
    inference(avatar_component_clause,[],[f215])).

fof(f224,plain,
    ( spl11_18
    | spl11_5
    | ~ spl11_7
    | ~ spl11_15 ),
    inference(avatar_split_clause,[],[f201,f191,f96,f60,f221])).

fof(f96,plain,
    ( spl11_7
  <=> ! [X0] :
        ( sK4 = k3_mcart_1(sK5(sK4,X0),sK6(sK4,X0),sK7(sK4,X0))
        | ~ m1_subset_1(X0,sK1)
        | k6_mcart_1(sK0,sK1,sK2,sK4) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f201,plain,
    ( sK4 = k3_mcart_1(sK5(sK4,sK3),sK6(sK4,sK3),sK7(sK4,sK3))
    | spl11_5
    | ~ spl11_7
    | ~ spl11_15 ),
    inference(subsumption_resolution,[],[f200,f62])).

fof(f200,plain,
    ( sK4 = k3_mcart_1(sK5(sK4,sK3),sK6(sK4,sK3),sK7(sK4,sK3))
    | sK3 = k6_mcart_1(sK0,sK1,sK2,sK4)
    | ~ spl11_7
    | ~ spl11_15 ),
    inference(resolution,[],[f193,f97])).

fof(f97,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | sK4 = k3_mcart_1(sK5(sK4,X0),sK6(sK4,X0),sK7(sK4,X0))
        | k6_mcart_1(sK0,sK1,sK2,sK4) = X0 )
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f96])).

fof(f218,plain,
    ( spl11_17
    | ~ spl11_16 ),
    inference(avatar_split_clause,[],[f206,f196,f215])).

fof(f196,plain,
    ( spl11_16
  <=> sK4 = k3_mcart_1(sK8(sK0,sK1,sK2,sK4),sK3,sK10(sK0,sK1,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f206,plain,
    ( ! [X10,X11,X9] :
        ( sK4 != k3_mcart_1(X9,X10,X11)
        | sK3 = X10 )
    | ~ spl11_16 ),
    inference(superposition,[],[f35,f198])).

fof(f198,plain,
    ( sK4 = k3_mcart_1(sK8(sK0,sK1,sK2,sK4),sK3,sK10(sK0,sK1,sK2,sK4))
    | ~ spl11_16 ),
    inference(avatar_component_clause,[],[f196])).

fof(f35,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5)
      | X1 = X4 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5)
     => ( X2 = X5
        & X1 = X4
        & X0 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_mcart_1)).

fof(f199,plain,
    ( spl11_16
    | ~ spl11_6
    | ~ spl11_14 ),
    inference(avatar_split_clause,[],[f184,f154,f82,f196])).

fof(f82,plain,
    ( spl11_6
  <=> sK4 = k3_mcart_1(sK8(sK0,sK1,sK2,sK4),sK9(sK0,sK1,sK2,sK4),sK10(sK0,sK1,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f154,plain,
    ( spl11_14
  <=> sK3 = sK9(sK0,sK1,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f184,plain,
    ( sK4 = k3_mcart_1(sK8(sK0,sK1,sK2,sK4),sK3,sK10(sK0,sK1,sK2,sK4))
    | ~ spl11_6
    | ~ spl11_14 ),
    inference(backward_demodulation,[],[f84,f156])).

fof(f156,plain,
    ( sK3 = sK9(sK0,sK1,sK2,sK4)
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f154])).

fof(f84,plain,
    ( sK4 = k3_mcart_1(sK8(sK0,sK1,sK2,sK4),sK9(sK0,sK1,sK2,sK4),sK10(sK0,sK1,sK2,sK4))
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f82])).

fof(f194,plain,
    ( spl11_15
    | ~ spl11_12
    | ~ spl11_14 ),
    inference(avatar_split_clause,[],[f183,f154,f146,f191])).

fof(f146,plain,
    ( spl11_12
  <=> m1_subset_1(sK9(sK0,sK1,sK2,sK4),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f183,plain,
    ( m1_subset_1(sK3,sK1)
    | ~ spl11_12
    | ~ spl11_14 ),
    inference(backward_demodulation,[],[f147,f156])).

fof(f147,plain,
    ( m1_subset_1(sK9(sK0,sK1,sK2,sK4),sK1)
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f146])).

fof(f182,plain,
    ( spl11_1
    | spl11_2
    | spl11_3
    | ~ spl11_4
    | spl11_13 ),
    inference(avatar_contradiction_clause,[],[f181])).

fof(f181,plain,
    ( $false
    | spl11_1
    | spl11_2
    | spl11_3
    | ~ spl11_4
    | spl11_13 ),
    inference(subsumption_resolution,[],[f180,f42])).

fof(f180,plain,
    ( k1_xboole_0 = sK0
    | spl11_2
    | spl11_3
    | ~ spl11_4
    | spl11_13 ),
    inference(subsumption_resolution,[],[f179,f47])).

fof(f179,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl11_3
    | ~ spl11_4
    | spl11_13 ),
    inference(subsumption_resolution,[],[f178,f52])).

fof(f178,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl11_4
    | spl11_13 ),
    inference(subsumption_resolution,[],[f176,f57])).

fof(f176,plain,
    ( ~ m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl11_13 ),
    inference(resolution,[],[f152,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK10(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k3_mcart_1(sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3),sK10(X0,X1,X2,X3)) = X3
            & m1_subset_1(sK10(X0,X1,X2,X3),X2)
            & m1_subset_1(sK9(X0,X1,X2,X3),X1)
            & m1_subset_1(sK8(X0,X1,X2,X3),X0) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f9,f19,f18,f17])).

fof(f17,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( k3_mcart_1(X4,X5,X6) = X3
                  & m1_subset_1(X6,X2) )
              & m1_subset_1(X5,X1) )
          & m1_subset_1(X4,X0) )
     => ( ? [X5] :
            ( ? [X6] :
                ( k3_mcart_1(sK8(X0,X1,X2,X3),X5,X6) = X3
                & m1_subset_1(X6,X2) )
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK8(X0,X1,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( k3_mcart_1(sK8(X0,X1,X2,X3),X5,X6) = X3
              & m1_subset_1(X6,X2) )
          & m1_subset_1(X5,X1) )
     => ( ? [X6] :
            ( k3_mcart_1(sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3),X6) = X3
            & m1_subset_1(X6,X2) )
        & m1_subset_1(sK9(X0,X1,X2,X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6] :
          ( k3_mcart_1(sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3),X6) = X3
          & m1_subset_1(X6,X2) )
     => ( k3_mcart_1(sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3),sK10(X0,X1,X2,X3)) = X3
        & m1_subset_1(sK10(X0,X1,X2,X3),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( k3_mcart_1(X4,X5,X6) = X3
                      & m1_subset_1(X6,X2) )
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,X0) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ~ ( ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,X0)
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ! [X6] :
                        ( m1_subset_1(X6,X2)
                       => k3_mcart_1(X4,X5,X6) != X3 ) ) )
            & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_mcart_1)).

fof(f152,plain,
    ( ~ m1_subset_1(sK10(sK0,sK1,sK2,sK4),sK2)
    | spl11_13 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl11_13
  <=> m1_subset_1(sK10(sK0,sK1,sK2,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f173,plain,
    ( spl11_1
    | spl11_2
    | spl11_3
    | ~ spl11_4
    | spl11_12 ),
    inference(avatar_contradiction_clause,[],[f172])).

fof(f172,plain,
    ( $false
    | spl11_1
    | spl11_2
    | spl11_3
    | ~ spl11_4
    | spl11_12 ),
    inference(subsumption_resolution,[],[f171,f42])).

fof(f171,plain,
    ( k1_xboole_0 = sK0
    | spl11_2
    | spl11_3
    | ~ spl11_4
    | spl11_12 ),
    inference(subsumption_resolution,[],[f170,f47])).

fof(f170,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl11_3
    | ~ spl11_4
    | spl11_12 ),
    inference(subsumption_resolution,[],[f169,f52])).

fof(f169,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl11_4
    | spl11_12 ),
    inference(subsumption_resolution,[],[f167,f57])).

fof(f167,plain,
    ( ~ m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl11_12 ),
    inference(resolution,[],[f148,f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK9(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f148,plain,
    ( ~ m1_subset_1(sK9(sK0,sK1,sK2,sK4),sK1)
    | spl11_12 ),
    inference(avatar_component_clause,[],[f146])).

fof(f165,plain,
    ( spl11_1
    | spl11_2
    | spl11_3
    | ~ spl11_4
    | spl11_11 ),
    inference(avatar_contradiction_clause,[],[f164])).

fof(f164,plain,
    ( $false
    | spl11_1
    | spl11_2
    | spl11_3
    | ~ spl11_4
    | spl11_11 ),
    inference(subsumption_resolution,[],[f163,f42])).

fof(f163,plain,
    ( k1_xboole_0 = sK0
    | spl11_2
    | spl11_3
    | ~ spl11_4
    | spl11_11 ),
    inference(subsumption_resolution,[],[f162,f47])).

fof(f162,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl11_3
    | ~ spl11_4
    | spl11_11 ),
    inference(subsumption_resolution,[],[f161,f52])).

fof(f161,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl11_4
    | spl11_11 ),
    inference(subsumption_resolution,[],[f159,f57])).

fof(f159,plain,
    ( ~ m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl11_11 ),
    inference(resolution,[],[f144,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK8(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f144,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1,sK2,sK4),sK0)
    | spl11_11 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl11_11
  <=> m1_subset_1(sK8(sK0,sK1,sK2,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f157,plain,
    ( ~ spl11_11
    | ~ spl11_12
    | ~ spl11_13
    | spl11_14
    | ~ spl11_6 ),
    inference(avatar_split_clause,[],[f94,f82,f154,f150,f146,f142])).

fof(f94,plain,
    ( sK3 = sK9(sK0,sK1,sK2,sK4)
    | ~ m1_subset_1(sK10(sK0,sK1,sK2,sK4),sK2)
    | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK4),sK1)
    | ~ m1_subset_1(sK8(sK0,sK1,sK2,sK4),sK0)
    | ~ spl11_6 ),
    inference(trivial_inequality_removal,[],[f86])).

fof(f86,plain,
    ( sK4 != sK4
    | sK3 = sK9(sK0,sK1,sK2,sK4)
    | ~ m1_subset_1(sK10(sK0,sK1,sK2,sK4),sK2)
    | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK4),sK1)
    | ~ m1_subset_1(sK8(sK0,sK1,sK2,sK4),sK0)
    | ~ spl11_6 ),
    inference(superposition,[],[f22,f84])).

fof(f22,plain,(
    ! [X6,X7,X5] :
      ( k3_mcart_1(X5,X6,X7) != sK4
      | sK3 = X6
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( sK3 != k6_mcart_1(sK0,sK1,sK2,sK4)
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK3 = X6
                | k3_mcart_1(X5,X6,X7) != sK4
                | ~ m1_subset_1(X7,sK2) )
            | ~ m1_subset_1(X6,sK1) )
        | ~ m1_subset_1(X5,sK0) )
    & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f7,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k6_mcart_1(X0,X1,X2,X4) != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X5] :
            ( ! [X6] :
                ( ! [X7] :
                    ( X3 = X6
                    | k3_mcart_1(X5,X6,X7) != X4
                    | ~ m1_subset_1(X7,X2) )
                | ~ m1_subset_1(X6,X1) )
            | ~ m1_subset_1(X5,X0) )
        & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) )
   => ( sK3 != k6_mcart_1(sK0,sK1,sK2,sK4)
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK3 = X6
                  | k3_mcart_1(X5,X6,X7) != sK4
                  | ~ m1_subset_1(X7,sK2) )
              | ~ m1_subset_1(X6,sK1) )
          | ~ m1_subset_1(X5,sK0) )
      & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k6_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X6
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k6_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X6
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X6 ) ) ) )
         => ( k6_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X6 ) ) ) )
       => ( k6_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_mcart_1)).

fof(f98,plain,
    ( spl11_7
    | spl11_1
    | spl11_2
    | spl11_3
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f80,f55,f50,f45,f40,f96])).

fof(f80,plain,
    ( ! [X0] :
        ( sK4 = k3_mcart_1(sK5(sK4,X0),sK6(sK4,X0),sK7(sK4,X0))
        | ~ m1_subset_1(X0,sK1)
        | k6_mcart_1(sK0,sK1,sK2,sK4) = X0 )
    | spl11_1
    | spl11_2
    | spl11_3
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f79,f42])).

fof(f79,plain,
    ( ! [X0] :
        ( sK4 = k3_mcart_1(sK5(sK4,X0),sK6(sK4,X0),sK7(sK4,X0))
        | ~ m1_subset_1(X0,sK1)
        | k6_mcart_1(sK0,sK1,sK2,sK4) = X0
        | k1_xboole_0 = sK0 )
    | spl11_2
    | spl11_3
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f78,f47])).

fof(f78,plain,
    ( ! [X0] :
        ( sK4 = k3_mcart_1(sK5(sK4,X0),sK6(sK4,X0),sK7(sK4,X0))
        | ~ m1_subset_1(X0,sK1)
        | k6_mcart_1(sK0,sK1,sK2,sK4) = X0
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0 )
    | spl11_3
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f74,f52])).

fof(f74,plain,
    ( ! [X0] :
        ( sK4 = k3_mcart_1(sK5(sK4,X0),sK6(sK4,X0),sK7(sK4,X0))
        | ~ m1_subset_1(X0,sK1)
        | k6_mcart_1(sK0,sK1,sK2,sK4) = X0
        | k1_xboole_0 = sK2
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0 )
    | ~ spl11_4 ),
    inference(resolution,[],[f28,f57])).

fof(f28,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k3_mcart_1(sK5(X3,X4),sK6(X3,X4),sK7(X3,X4)) = X3
      | ~ m1_subset_1(X4,X1)
      | k6_mcart_1(X0,X1,X2,X3) = X4
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f85,plain,
    ( spl11_6
    | spl11_1
    | spl11_2
    | spl11_3
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f73,f55,f50,f45,f40,f82])).

fof(f73,plain,
    ( sK4 = k3_mcart_1(sK8(sK0,sK1,sK2,sK4),sK9(sK0,sK1,sK2,sK4),sK10(sK0,sK1,sK2,sK4))
    | spl11_1
    | spl11_2
    | spl11_3
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f72,f42])).

fof(f72,plain,
    ( sK4 = k3_mcart_1(sK8(sK0,sK1,sK2,sK4),sK9(sK0,sK1,sK2,sK4),sK10(sK0,sK1,sK2,sK4))
    | k1_xboole_0 = sK0
    | spl11_2
    | spl11_3
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f71,f47])).

fof(f71,plain,
    ( sK4 = k3_mcart_1(sK8(sK0,sK1,sK2,sK4),sK9(sK0,sK1,sK2,sK4),sK10(sK0,sK1,sK2,sK4))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl11_3
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f67,f52])).

fof(f67,plain,
    ( sK4 = k3_mcart_1(sK8(sK0,sK1,sK2,sK4),sK9(sK0,sK1,sK2,sK4),sK10(sK0,sK1,sK2,sK4))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl11_4 ),
    inference(resolution,[],[f33,f57])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k3_mcart_1(sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3),sK10(X0,X1,X2,X3)) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f63,plain,(
    ~ spl11_5 ),
    inference(avatar_split_clause,[],[f26,f60])).

fof(f26,plain,(
    sK3 != k6_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f12])).

fof(f58,plain,(
    spl11_4 ),
    inference(avatar_split_clause,[],[f21,f55])).

fof(f21,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f53,plain,(
    ~ spl11_3 ),
    inference(avatar_split_clause,[],[f25,f50])).

fof(f25,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f12])).

fof(f48,plain,(
    ~ spl11_2 ),
    inference(avatar_split_clause,[],[f24,f45])).

fof(f24,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f12])).

fof(f43,plain,(
    ~ spl11_1 ),
    inference(avatar_split_clause,[],[f23,f40])).

fof(f23,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:43:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.49  % (15585)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.49  % (15578)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.50  % (15581)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (15578)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f261,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f43,f48,f53,f58,f63,f85,f98,f157,f165,f173,f182,f194,f199,f218,f224,f250,f260])).
% 0.22/0.51  fof(f260,plain,(
% 0.22/0.51    spl11_1 | spl11_2 | spl11_3 | ~spl11_4 | spl11_5 | ~spl11_15 | ~spl11_20),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f257])).
% 0.22/0.51  fof(f257,plain,(
% 0.22/0.51    $false | (spl11_1 | spl11_2 | spl11_3 | ~spl11_4 | spl11_5 | ~spl11_15 | ~spl11_20)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f42,f47,f52,f193,f57,f62,f249,f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X3,X1] : (sK6(X3,X4) != X4 | k6_mcart_1(X0,X1,X2,X3) = X4 | ~m1_subset_1(X4,X1) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (! [X3] : (! [X4] : (((k6_mcart_1(X0,X1,X2,X3) = X4 | (sK6(X3,X4) != X4 & k3_mcart_1(sK5(X3,X4),sK6(X3,X4),sK7(X3,X4)) = X3)) & (! [X8,X9,X10] : (X4 = X9 | k3_mcart_1(X8,X9,X10) != X3) | k6_mcart_1(X0,X1,X2,X3) != X4)) | ~m1_subset_1(X4,X1)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f14,f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X4,X3] : (? [X5,X6,X7] : (X4 != X6 & k3_mcart_1(X5,X6,X7) = X3) => (sK6(X3,X4) != X4 & k3_mcart_1(sK5(X3,X4),sK6(X3,X4),sK7(X3,X4)) = X3))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (! [X3] : (! [X4] : (((k6_mcart_1(X0,X1,X2,X3) = X4 | ? [X5,X6,X7] : (X4 != X6 & k3_mcart_1(X5,X6,X7) = X3)) & (! [X8,X9,X10] : (X4 = X9 | k3_mcart_1(X8,X9,X10) != X3) | k6_mcart_1(X0,X1,X2,X3) != X4)) | ~m1_subset_1(X4,X1)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.51    inference(rectify,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (! [X3] : (! [X4] : (((k6_mcart_1(X0,X1,X2,X3) = X4 | ? [X5,X6,X7] : (X4 != X6 & k3_mcart_1(X5,X6,X7) = X3)) & (! [X5,X6,X7] : (X4 = X6 | k3_mcart_1(X5,X6,X7) != X3) | k6_mcart_1(X0,X1,X2,X3) != X4)) | ~m1_subset_1(X4,X1)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.51    inference(nnf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (! [X3] : (! [X4] : ((k6_mcart_1(X0,X1,X2,X3) = X4 <=> ! [X5,X6,X7] : (X4 = X6 | k3_mcart_1(X5,X6,X7) != X3)) | ~m1_subset_1(X4,X1)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.51    inference(ennf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => ! [X4] : (m1_subset_1(X4,X1) => (k6_mcart_1(X0,X1,X2,X3) = X4 <=> ! [X5,X6,X7] : (k3_mcart_1(X5,X6,X7) = X3 => X4 = X6)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_mcart_1)).
% 0.22/0.51  fof(f249,plain,(
% 0.22/0.51    sK3 = sK6(sK4,sK3) | ~spl11_20),
% 0.22/0.51    inference(avatar_component_clause,[],[f247])).
% 0.22/0.51  fof(f247,plain,(
% 0.22/0.51    spl11_20 <=> sK3 = sK6(sK4,sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    sK3 != k6_mcart_1(sK0,sK1,sK2,sK4) | spl11_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f60])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    spl11_5 <=> sK3 = k6_mcart_1(sK0,sK1,sK2,sK4)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) | ~spl11_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f55])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    spl11_4 <=> m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 0.22/0.51  fof(f193,plain,(
% 0.22/0.51    m1_subset_1(sK3,sK1) | ~spl11_15),
% 0.22/0.51    inference(avatar_component_clause,[],[f191])).
% 0.22/0.51  fof(f191,plain,(
% 0.22/0.51    spl11_15 <=> m1_subset_1(sK3,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    k1_xboole_0 != sK2 | spl11_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f50])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    spl11_3 <=> k1_xboole_0 = sK2),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    k1_xboole_0 != sK1 | spl11_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f45])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    spl11_2 <=> k1_xboole_0 = sK1),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    k1_xboole_0 != sK0 | spl11_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    spl11_1 <=> k1_xboole_0 = sK0),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 0.22/0.51  fof(f250,plain,(
% 0.22/0.51    spl11_20 | ~spl11_17 | ~spl11_18),
% 0.22/0.51    inference(avatar_split_clause,[],[f240,f221,f215,f247])).
% 0.22/0.51  fof(f215,plain,(
% 0.22/0.51    spl11_17 <=> ! [X7,X8,X6] : (sK4 != k3_mcart_1(X6,X7,X8) | sK3 = X7)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).
% 0.22/0.51  fof(f221,plain,(
% 0.22/0.51    spl11_18 <=> sK4 = k3_mcart_1(sK5(sK4,sK3),sK6(sK4,sK3),sK7(sK4,sK3))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).
% 0.22/0.51  fof(f240,plain,(
% 0.22/0.51    sK3 = sK6(sK4,sK3) | (~spl11_17 | ~spl11_18)),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f239])).
% 0.22/0.51  fof(f239,plain,(
% 0.22/0.51    sK4 != sK4 | sK3 = sK6(sK4,sK3) | (~spl11_17 | ~spl11_18)),
% 0.22/0.51    inference(superposition,[],[f216,f223])).
% 0.22/0.51  fof(f223,plain,(
% 0.22/0.51    sK4 = k3_mcart_1(sK5(sK4,sK3),sK6(sK4,sK3),sK7(sK4,sK3)) | ~spl11_18),
% 0.22/0.51    inference(avatar_component_clause,[],[f221])).
% 0.22/0.51  fof(f216,plain,(
% 0.22/0.51    ( ! [X6,X8,X7] : (sK4 != k3_mcart_1(X6,X7,X8) | sK3 = X7) ) | ~spl11_17),
% 0.22/0.51    inference(avatar_component_clause,[],[f215])).
% 0.22/0.51  fof(f224,plain,(
% 0.22/0.51    spl11_18 | spl11_5 | ~spl11_7 | ~spl11_15),
% 0.22/0.51    inference(avatar_split_clause,[],[f201,f191,f96,f60,f221])).
% 0.22/0.51  fof(f96,plain,(
% 0.22/0.51    spl11_7 <=> ! [X0] : (sK4 = k3_mcart_1(sK5(sK4,X0),sK6(sK4,X0),sK7(sK4,X0)) | ~m1_subset_1(X0,sK1) | k6_mcart_1(sK0,sK1,sK2,sK4) = X0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).
% 0.22/0.51  fof(f201,plain,(
% 0.22/0.51    sK4 = k3_mcart_1(sK5(sK4,sK3),sK6(sK4,sK3),sK7(sK4,sK3)) | (spl11_5 | ~spl11_7 | ~spl11_15)),
% 0.22/0.51    inference(subsumption_resolution,[],[f200,f62])).
% 0.22/0.51  fof(f200,plain,(
% 0.22/0.51    sK4 = k3_mcart_1(sK5(sK4,sK3),sK6(sK4,sK3),sK7(sK4,sK3)) | sK3 = k6_mcart_1(sK0,sK1,sK2,sK4) | (~spl11_7 | ~spl11_15)),
% 0.22/0.51    inference(resolution,[],[f193,f97])).
% 0.22/0.51  fof(f97,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(X0,sK1) | sK4 = k3_mcart_1(sK5(sK4,X0),sK6(sK4,X0),sK7(sK4,X0)) | k6_mcart_1(sK0,sK1,sK2,sK4) = X0) ) | ~spl11_7),
% 0.22/0.51    inference(avatar_component_clause,[],[f96])).
% 0.22/0.51  fof(f218,plain,(
% 0.22/0.51    spl11_17 | ~spl11_16),
% 0.22/0.51    inference(avatar_split_clause,[],[f206,f196,f215])).
% 0.22/0.51  fof(f196,plain,(
% 0.22/0.51    spl11_16 <=> sK4 = k3_mcart_1(sK8(sK0,sK1,sK2,sK4),sK3,sK10(sK0,sK1,sK2,sK4))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).
% 0.22/0.51  fof(f206,plain,(
% 0.22/0.51    ( ! [X10,X11,X9] : (sK4 != k3_mcart_1(X9,X10,X11) | sK3 = X10) ) | ~spl11_16),
% 0.22/0.51    inference(superposition,[],[f35,f198])).
% 0.22/0.51  fof(f198,plain,(
% 0.22/0.51    sK4 = k3_mcart_1(sK8(sK0,sK1,sK2,sK4),sK3,sK10(sK0,sK1,sK2,sK4)) | ~spl11_16),
% 0.22/0.51    inference(avatar_component_clause,[],[f196])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5) | X1 = X4) )),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3,X4,X5] : ((X2 = X5 & X1 = X4 & X0 = X3) | k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3,X4,X5] : (k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5) => (X2 = X5 & X1 = X4 & X0 = X3))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_mcart_1)).
% 0.22/0.51  fof(f199,plain,(
% 0.22/0.51    spl11_16 | ~spl11_6 | ~spl11_14),
% 0.22/0.51    inference(avatar_split_clause,[],[f184,f154,f82,f196])).
% 0.22/0.51  fof(f82,plain,(
% 0.22/0.51    spl11_6 <=> sK4 = k3_mcart_1(sK8(sK0,sK1,sK2,sK4),sK9(sK0,sK1,sK2,sK4),sK10(sK0,sK1,sK2,sK4))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).
% 0.22/0.51  fof(f154,plain,(
% 0.22/0.51    spl11_14 <=> sK3 = sK9(sK0,sK1,sK2,sK4)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).
% 0.22/0.51  fof(f184,plain,(
% 0.22/0.51    sK4 = k3_mcart_1(sK8(sK0,sK1,sK2,sK4),sK3,sK10(sK0,sK1,sK2,sK4)) | (~spl11_6 | ~spl11_14)),
% 0.22/0.51    inference(backward_demodulation,[],[f84,f156])).
% 0.22/0.51  fof(f156,plain,(
% 0.22/0.51    sK3 = sK9(sK0,sK1,sK2,sK4) | ~spl11_14),
% 0.22/0.51    inference(avatar_component_clause,[],[f154])).
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    sK4 = k3_mcart_1(sK8(sK0,sK1,sK2,sK4),sK9(sK0,sK1,sK2,sK4),sK10(sK0,sK1,sK2,sK4)) | ~spl11_6),
% 0.22/0.51    inference(avatar_component_clause,[],[f82])).
% 0.22/0.51  fof(f194,plain,(
% 0.22/0.51    spl11_15 | ~spl11_12 | ~spl11_14),
% 0.22/0.51    inference(avatar_split_clause,[],[f183,f154,f146,f191])).
% 0.22/0.51  fof(f146,plain,(
% 0.22/0.51    spl11_12 <=> m1_subset_1(sK9(sK0,sK1,sK2,sK4),sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).
% 0.22/0.51  fof(f183,plain,(
% 0.22/0.51    m1_subset_1(sK3,sK1) | (~spl11_12 | ~spl11_14)),
% 0.22/0.51    inference(backward_demodulation,[],[f147,f156])).
% 0.22/0.51  fof(f147,plain,(
% 0.22/0.51    m1_subset_1(sK9(sK0,sK1,sK2,sK4),sK1) | ~spl11_12),
% 0.22/0.51    inference(avatar_component_clause,[],[f146])).
% 0.22/0.51  fof(f182,plain,(
% 0.22/0.51    spl11_1 | spl11_2 | spl11_3 | ~spl11_4 | spl11_13),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f181])).
% 0.22/0.51  fof(f181,plain,(
% 0.22/0.51    $false | (spl11_1 | spl11_2 | spl11_3 | ~spl11_4 | spl11_13)),
% 0.22/0.51    inference(subsumption_resolution,[],[f180,f42])).
% 0.22/0.51  fof(f180,plain,(
% 0.22/0.51    k1_xboole_0 = sK0 | (spl11_2 | spl11_3 | ~spl11_4 | spl11_13)),
% 0.22/0.51    inference(subsumption_resolution,[],[f179,f47])).
% 0.22/0.51  fof(f179,plain,(
% 0.22/0.51    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (spl11_3 | ~spl11_4 | spl11_13)),
% 0.22/0.51    inference(subsumption_resolution,[],[f178,f52])).
% 0.22/0.51  fof(f178,plain,(
% 0.22/0.51    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl11_4 | spl11_13)),
% 0.22/0.51    inference(subsumption_resolution,[],[f176,f57])).
% 0.22/0.51  fof(f176,plain,(
% 0.22/0.51    ~m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl11_13),
% 0.22/0.51    inference(resolution,[],[f152,f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK10(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (! [X3] : ((((k3_mcart_1(sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3),sK10(X0,X1,X2,X3)) = X3 & m1_subset_1(sK10(X0,X1,X2,X3),X2)) & m1_subset_1(sK9(X0,X1,X2,X3),X1)) & m1_subset_1(sK8(X0,X1,X2,X3),X0)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f9,f19,f18,f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X3,X2,X1,X0] : (? [X4] : (? [X5] : (? [X6] : (k3_mcart_1(X4,X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0)) => (? [X5] : (? [X6] : (k3_mcart_1(sK8(X0,X1,X2,X3),X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) & m1_subset_1(sK8(X0,X1,X2,X3),X0)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X3,X2,X1,X0] : (? [X5] : (? [X6] : (k3_mcart_1(sK8(X0,X1,X2,X3),X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) => (? [X6] : (k3_mcart_1(sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3),X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(sK9(X0,X1,X2,X3),X1)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X3,X2,X1,X0] : (? [X6] : (k3_mcart_1(sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3),X6) = X3 & m1_subset_1(X6,X2)) => (k3_mcart_1(sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3),sK10(X0,X1,X2,X3)) = X3 & m1_subset_1(sK10(X0,X1,X2,X3),X2)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f9,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (! [X3] : (? [X4] : (? [X5] : (? [X6] : (k3_mcart_1(X4,X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ~(? [X3] : (! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X1) => ! [X6] : (m1_subset_1(X6,X2) => k3_mcart_1(X4,X5,X6) != X3))) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_mcart_1)).
% 0.22/0.51  fof(f152,plain,(
% 0.22/0.51    ~m1_subset_1(sK10(sK0,sK1,sK2,sK4),sK2) | spl11_13),
% 0.22/0.51    inference(avatar_component_clause,[],[f150])).
% 0.22/0.51  fof(f150,plain,(
% 0.22/0.51    spl11_13 <=> m1_subset_1(sK10(sK0,sK1,sK2,sK4),sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).
% 0.22/0.51  fof(f173,plain,(
% 0.22/0.51    spl11_1 | spl11_2 | spl11_3 | ~spl11_4 | spl11_12),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f172])).
% 0.22/0.51  fof(f172,plain,(
% 0.22/0.51    $false | (spl11_1 | spl11_2 | spl11_3 | ~spl11_4 | spl11_12)),
% 0.22/0.51    inference(subsumption_resolution,[],[f171,f42])).
% 0.22/0.51  fof(f171,plain,(
% 0.22/0.51    k1_xboole_0 = sK0 | (spl11_2 | spl11_3 | ~spl11_4 | spl11_12)),
% 0.22/0.51    inference(subsumption_resolution,[],[f170,f47])).
% 0.22/0.51  fof(f170,plain,(
% 0.22/0.51    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (spl11_3 | ~spl11_4 | spl11_12)),
% 0.22/0.51    inference(subsumption_resolution,[],[f169,f52])).
% 0.22/0.51  fof(f169,plain,(
% 0.22/0.51    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl11_4 | spl11_12)),
% 0.22/0.51    inference(subsumption_resolution,[],[f167,f57])).
% 0.22/0.51  fof(f167,plain,(
% 0.22/0.51    ~m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl11_12),
% 0.22/0.51    inference(resolution,[],[f148,f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK9(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f148,plain,(
% 0.22/0.51    ~m1_subset_1(sK9(sK0,sK1,sK2,sK4),sK1) | spl11_12),
% 0.22/0.51    inference(avatar_component_clause,[],[f146])).
% 0.22/0.51  fof(f165,plain,(
% 0.22/0.51    spl11_1 | spl11_2 | spl11_3 | ~spl11_4 | spl11_11),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f164])).
% 0.22/0.51  fof(f164,plain,(
% 0.22/0.51    $false | (spl11_1 | spl11_2 | spl11_3 | ~spl11_4 | spl11_11)),
% 0.22/0.51    inference(subsumption_resolution,[],[f163,f42])).
% 0.22/0.51  fof(f163,plain,(
% 0.22/0.51    k1_xboole_0 = sK0 | (spl11_2 | spl11_3 | ~spl11_4 | spl11_11)),
% 0.22/0.51    inference(subsumption_resolution,[],[f162,f47])).
% 0.22/0.51  fof(f162,plain,(
% 0.22/0.51    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (spl11_3 | ~spl11_4 | spl11_11)),
% 0.22/0.51    inference(subsumption_resolution,[],[f161,f52])).
% 0.22/0.51  fof(f161,plain,(
% 0.22/0.51    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl11_4 | spl11_11)),
% 0.22/0.51    inference(subsumption_resolution,[],[f159,f57])).
% 0.22/0.51  fof(f159,plain,(
% 0.22/0.51    ~m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl11_11),
% 0.22/0.51    inference(resolution,[],[f144,f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK8(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f144,plain,(
% 0.22/0.51    ~m1_subset_1(sK8(sK0,sK1,sK2,sK4),sK0) | spl11_11),
% 0.22/0.51    inference(avatar_component_clause,[],[f142])).
% 0.22/0.51  fof(f142,plain,(
% 0.22/0.51    spl11_11 <=> m1_subset_1(sK8(sK0,sK1,sK2,sK4),sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).
% 0.22/0.51  fof(f157,plain,(
% 0.22/0.51    ~spl11_11 | ~spl11_12 | ~spl11_13 | spl11_14 | ~spl11_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f94,f82,f154,f150,f146,f142])).
% 0.22/0.51  fof(f94,plain,(
% 0.22/0.51    sK3 = sK9(sK0,sK1,sK2,sK4) | ~m1_subset_1(sK10(sK0,sK1,sK2,sK4),sK2) | ~m1_subset_1(sK9(sK0,sK1,sK2,sK4),sK1) | ~m1_subset_1(sK8(sK0,sK1,sK2,sK4),sK0) | ~spl11_6),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f86])).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    sK4 != sK4 | sK3 = sK9(sK0,sK1,sK2,sK4) | ~m1_subset_1(sK10(sK0,sK1,sK2,sK4),sK2) | ~m1_subset_1(sK9(sK0,sK1,sK2,sK4),sK1) | ~m1_subset_1(sK8(sK0,sK1,sK2,sK4),sK0) | ~spl11_6),
% 0.22/0.51    inference(superposition,[],[f22,f84])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ( ! [X6,X7,X5] : (k3_mcart_1(X5,X6,X7) != sK4 | sK3 = X6 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    sK3 != k6_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X6 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f7,f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ? [X0,X1,X2,X3,X4] : (k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X6 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (sK3 != k6_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X6 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f7,plain,(
% 0.22/0.51    ? [X0,X1,X2,X3,X4] : (k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X6 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.22/0.51    inference(flattening,[],[f6])).
% 0.22/0.51  fof(f6,plain,(
% 0.22/0.51    ? [X0,X1,X2,X3,X4] : (((k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X6 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X6)))) => (k6_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.22/0.51    inference(negated_conjecture,[],[f4])).
% 0.22/0.51  fof(f4,conjecture,(
% 0.22/0.51    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X6)))) => (k6_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_mcart_1)).
% 0.22/0.51  fof(f98,plain,(
% 0.22/0.51    spl11_7 | spl11_1 | spl11_2 | spl11_3 | ~spl11_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f80,f55,f50,f45,f40,f96])).
% 0.22/0.51  fof(f80,plain,(
% 0.22/0.51    ( ! [X0] : (sK4 = k3_mcart_1(sK5(sK4,X0),sK6(sK4,X0),sK7(sK4,X0)) | ~m1_subset_1(X0,sK1) | k6_mcart_1(sK0,sK1,sK2,sK4) = X0) ) | (spl11_1 | spl11_2 | spl11_3 | ~spl11_4)),
% 0.22/0.51    inference(subsumption_resolution,[],[f79,f42])).
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    ( ! [X0] : (sK4 = k3_mcart_1(sK5(sK4,X0),sK6(sK4,X0),sK7(sK4,X0)) | ~m1_subset_1(X0,sK1) | k6_mcart_1(sK0,sK1,sK2,sK4) = X0 | k1_xboole_0 = sK0) ) | (spl11_2 | spl11_3 | ~spl11_4)),
% 0.22/0.51    inference(subsumption_resolution,[],[f78,f47])).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    ( ! [X0] : (sK4 = k3_mcart_1(sK5(sK4,X0),sK6(sK4,X0),sK7(sK4,X0)) | ~m1_subset_1(X0,sK1) | k6_mcart_1(sK0,sK1,sK2,sK4) = X0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) ) | (spl11_3 | ~spl11_4)),
% 0.22/0.51    inference(subsumption_resolution,[],[f74,f52])).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    ( ! [X0] : (sK4 = k3_mcart_1(sK5(sK4,X0),sK6(sK4,X0),sK7(sK4,X0)) | ~m1_subset_1(X0,sK1) | k6_mcart_1(sK0,sK1,sK2,sK4) = X0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) ) | ~spl11_4),
% 0.22/0.51    inference(resolution,[],[f28,f57])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k3_mcart_1(sK5(X3,X4),sK6(X3,X4),sK7(X3,X4)) = X3 | ~m1_subset_1(X4,X1) | k6_mcart_1(X0,X1,X2,X3) = X4 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    spl11_6 | spl11_1 | spl11_2 | spl11_3 | ~spl11_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f73,f55,f50,f45,f40,f82])).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    sK4 = k3_mcart_1(sK8(sK0,sK1,sK2,sK4),sK9(sK0,sK1,sK2,sK4),sK10(sK0,sK1,sK2,sK4)) | (spl11_1 | spl11_2 | spl11_3 | ~spl11_4)),
% 0.22/0.51    inference(subsumption_resolution,[],[f72,f42])).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    sK4 = k3_mcart_1(sK8(sK0,sK1,sK2,sK4),sK9(sK0,sK1,sK2,sK4),sK10(sK0,sK1,sK2,sK4)) | k1_xboole_0 = sK0 | (spl11_2 | spl11_3 | ~spl11_4)),
% 0.22/0.51    inference(subsumption_resolution,[],[f71,f47])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    sK4 = k3_mcart_1(sK8(sK0,sK1,sK2,sK4),sK9(sK0,sK1,sK2,sK4),sK10(sK0,sK1,sK2,sK4)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (spl11_3 | ~spl11_4)),
% 0.22/0.51    inference(subsumption_resolution,[],[f67,f52])).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    sK4 = k3_mcart_1(sK8(sK0,sK1,sK2,sK4),sK9(sK0,sK1,sK2,sK4),sK10(sK0,sK1,sK2,sK4)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl11_4),
% 0.22/0.51    inference(resolution,[],[f33,f57])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k3_mcart_1(sK8(X0,X1,X2,X3),sK9(X0,X1,X2,X3),sK10(X0,X1,X2,X3)) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    ~spl11_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f26,f60])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    sK3 != k6_mcart_1(sK0,sK1,sK2,sK4)),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    spl11_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f21,f55])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    ~spl11_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f25,f50])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    k1_xboole_0 != sK2),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    ~spl11_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f24,f45])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    k1_xboole_0 != sK1),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ~spl11_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f23,f40])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    k1_xboole_0 != sK0),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (15578)------------------------------
% 0.22/0.51  % (15578)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (15578)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (15578)Memory used [KB]: 6396
% 0.22/0.51  % (15578)Time elapsed: 0.091 s
% 0.22/0.51  % (15578)------------------------------
% 0.22/0.51  % (15578)------------------------------
% 0.22/0.52  % (15575)Success in time 0.158 s
%------------------------------------------------------------------------------
