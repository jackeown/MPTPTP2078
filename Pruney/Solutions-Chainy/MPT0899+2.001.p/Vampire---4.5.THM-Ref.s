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
% DateTime   : Thu Dec  3 12:59:17 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 242 expanded)
%              Number of leaves         :   30 ( 102 expanded)
%              Depth                    :   11
%              Number of atoms          :  791 (1445 expanded)
%              Number of equality atoms :  503 (1028 expanded)
%              Maximal formula depth    :   19 (  10 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f295,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f80,f85,f90,f95,f100,f117,f195,f200,f205,f212,f237,f239,f264,f294])).

fof(f294,plain,
    ( spl25_1
    | spl25_2
    | spl25_3
    | spl25_4
    | ~ spl25_5
    | spl25_8
    | ~ spl25_20 ),
    inference(avatar_contradiction_clause,[],[f293])).

fof(f293,plain,
    ( $false
    | spl25_1
    | spl25_2
    | spl25_3
    | spl25_4
    | ~ spl25_5
    | spl25_8
    | ~ spl25_20 ),
    inference(subsumption_resolution,[],[f292,f74])).

fof(f74,plain,
    ( k1_xboole_0 != sK0
    | spl25_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl25_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_1])])).

fof(f292,plain,
    ( k1_xboole_0 = sK0
    | spl25_2
    | spl25_3
    | spl25_4
    | ~ spl25_5
    | spl25_8
    | ~ spl25_20 ),
    inference(subsumption_resolution,[],[f291,f79])).

fof(f79,plain,
    ( k1_xboole_0 != sK1
    | spl25_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl25_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_2])])).

fof(f291,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl25_3
    | spl25_4
    | ~ spl25_5
    | spl25_8
    | ~ spl25_20 ),
    inference(subsumption_resolution,[],[f290,f84])).

fof(f84,plain,
    ( k1_xboole_0 != sK2
    | spl25_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl25_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_3])])).

fof(f290,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl25_4
    | ~ spl25_5
    | spl25_8
    | ~ spl25_20 ),
    inference(subsumption_resolution,[],[f289,f89])).

fof(f89,plain,
    ( k1_xboole_0 != sK3
    | spl25_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl25_4
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_4])])).

fof(f289,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl25_5
    | spl25_8
    | ~ spl25_20 ),
    inference(subsumption_resolution,[],[f287,f108])).

fof(f108,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK6
    | spl25_8 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl25_8
  <=> k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_8])])).

fof(f287,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK6
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl25_5
    | ~ spl25_20 ),
    inference(resolution,[],[f236,f94])).

fof(f94,plain,
    ( m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | ~ spl25_5 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl25_5
  <=> m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_5])])).

fof(f236,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3))
        | sK6 = k9_mcart_1(X0,X1,X2,X3,sK4)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | ~ spl25_20 ),
    inference(avatar_component_clause,[],[f235])).

fof(f235,plain,
    ( spl25_20
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3))
        | sK6 = k9_mcart_1(X0,X1,X2,X3,sK4)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_20])])).

fof(f264,plain,
    ( spl25_1
    | spl25_2
    | spl25_3
    | spl25_4
    | ~ spl25_5
    | spl25_7
    | ~ spl25_17 ),
    inference(avatar_contradiction_clause,[],[f263])).

fof(f263,plain,
    ( $false
    | spl25_1
    | spl25_2
    | spl25_3
    | spl25_4
    | ~ spl25_5
    | spl25_7
    | ~ spl25_17 ),
    inference(subsumption_resolution,[],[f262,f74])).

fof(f262,plain,
    ( k1_xboole_0 = sK0
    | spl25_2
    | spl25_3
    | spl25_4
    | ~ spl25_5
    | spl25_7
    | ~ spl25_17 ),
    inference(subsumption_resolution,[],[f261,f79])).

fof(f261,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl25_3
    | spl25_4
    | ~ spl25_5
    | spl25_7
    | ~ spl25_17 ),
    inference(subsumption_resolution,[],[f260,f84])).

fof(f260,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl25_4
    | ~ spl25_5
    | spl25_7
    | ~ spl25_17 ),
    inference(subsumption_resolution,[],[f259,f89])).

fof(f259,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl25_5
    | spl25_7
    | ~ spl25_17 ),
    inference(subsumption_resolution,[],[f257,f104])).

fof(f104,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK5
    | spl25_7 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl25_7
  <=> k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_7])])).

fof(f257,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK5
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl25_5
    | ~ spl25_17 ),
    inference(resolution,[],[f204,f94])).

fof(f204,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3))
        | sK5 = k8_mcart_1(X0,X1,X2,X3,sK4)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | ~ spl25_17 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl25_17
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3))
        | sK5 = k8_mcart_1(X0,X1,X2,X3,sK4)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_17])])).

fof(f239,plain,
    ( spl25_10
    | spl25_1
    | spl25_2
    | spl25_3
    | spl25_4
    | ~ spl25_5
    | ~ spl25_16 ),
    inference(avatar_split_clause,[],[f233,f198,f92,f87,f82,f77,f72,f114])).

fof(f114,plain,
    ( spl25_10
  <=> k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK8 ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_10])])).

fof(f198,plain,
    ( spl25_16
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3))
        | sK8 = k11_mcart_1(X0,X1,X2,X3,sK4)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_16])])).

fof(f233,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK8
    | spl25_1
    | spl25_2
    | spl25_3
    | spl25_4
    | ~ spl25_5
    | ~ spl25_16 ),
    inference(subsumption_resolution,[],[f232,f74])).

fof(f232,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK8
    | k1_xboole_0 = sK0
    | spl25_2
    | spl25_3
    | spl25_4
    | ~ spl25_5
    | ~ spl25_16 ),
    inference(subsumption_resolution,[],[f231,f79])).

fof(f231,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK8
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl25_3
    | spl25_4
    | ~ spl25_5
    | ~ spl25_16 ),
    inference(subsumption_resolution,[],[f230,f84])).

fof(f230,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK8
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl25_4
    | ~ spl25_5
    | ~ spl25_16 ),
    inference(subsumption_resolution,[],[f229,f89])).

fof(f229,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK8
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl25_5
    | ~ spl25_16 ),
    inference(resolution,[],[f199,f94])).

fof(f199,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3))
        | sK8 = k11_mcart_1(X0,X1,X2,X3,sK4)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | ~ spl25_16 ),
    inference(avatar_component_clause,[],[f198])).

fof(f237,plain,
    ( spl25_20
    | ~ spl25_6 ),
    inference(avatar_split_clause,[],[f201,f97,f235])).

fof(f97,plain,
    ( spl25_6
  <=> sK4 = k4_mcart_1(sK5,sK6,sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_6])])).

fof(f201,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3))
        | sK6 = k9_mcart_1(X0,X1,X2,X3,sK4)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | ~ spl25_6 ),
    inference(superposition,[],[f196,f99])).

fof(f99,plain,
    ( sK4 = k4_mcart_1(sK5,sK6,sK7,sK8)
    | ~ spl25_6 ),
    inference(avatar_component_clause,[],[f97])).

fof(f196,plain,(
    ! [X2,X0,X12,X10,X3,X1,X13,X11] :
      ( ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) = X11
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f70,f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_mcart_1)).

fof(f70,plain,(
    ! [X2,X0,X12,X10,X3,X1,X13,X11] :
      ( k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) = X11
      | ~ m1_subset_1(k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)),X1)
      | ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X12,X10,X5,X3,X1,X13,X11] :
      ( X5 = X11
      | k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) != X5
      | ~ m1_subset_1(X5,X1)
      | ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X12,X10,X5,X3,X1,X13,X11] :
      ( X5 = X11
      | k4_mcart_1(X10,X11,X12,X13) != X4
      | k9_mcart_1(X0,X1,X2,X3,X4) != X5
      | ~ m1_subset_1(X5,X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k9_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ( sK22(X4,X5) != X5
                    & k4_mcart_1(sK21(X4,X5),sK22(X4,X5),sK23(X4,X5),sK24(X4,X5)) = X4 ) )
                & ( ! [X10,X11,X12,X13] :
                      ( X5 = X11
                      | k4_mcart_1(X10,X11,X12,X13) != X4 )
                  | k9_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X1) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK21,sK22,sK23,sK24])],[f37,f38])).

fof(f38,plain,(
    ! [X5,X4] :
      ( ? [X6,X7,X8,X9] :
          ( X5 != X7
          & k4_mcart_1(X6,X7,X8,X9) = X4 )
     => ( sK22(X4,X5) != X5
        & k4_mcart_1(sK21(X4,X5),sK22(X4,X5),sK23(X4,X5),sK24(X4,X5)) = X4 ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k9_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ? [X6,X7,X8,X9] :
                      ( X5 != X7
                      & k4_mcart_1(X6,X7,X8,X9) = X4 ) )
                & ( ! [X10,X11,X12,X13] :
                      ( X5 = X11
                      | k4_mcart_1(X10,X11,X12,X13) != X4 )
                  | k9_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X1) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k9_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ? [X6,X7,X8,X9] :
                      ( X5 != X7
                      & k4_mcart_1(X6,X7,X8,X9) = X4 ) )
                & ( ! [X6,X7,X8,X9] :
                      ( X5 = X7
                      | k4_mcart_1(X6,X7,X8,X9) != X4 )
                  | k9_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X1) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( k9_mcart_1(X0,X1,X2,X3,X4) = X5
              <=> ! [X6,X7,X8,X9] :
                    ( X5 = X7
                    | k4_mcart_1(X6,X7,X8,X9) != X4 ) )
              | ~ m1_subset_1(X5,X1) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( k9_mcart_1(X0,X1,X2,X3,X4) = X5
                  <=> ! [X6,X7,X8,X9] :
                        ( k4_mcart_1(X6,X7,X8,X9) = X4
                       => X5 = X7 ) ) ) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_mcart_1)).

fof(f212,plain,
    ( spl25_9
    | spl25_1
    | spl25_2
    | spl25_3
    | spl25_4
    | ~ spl25_5
    | ~ spl25_15 ),
    inference(avatar_split_clause,[],[f210,f193,f92,f87,f82,f77,f72,f110])).

fof(f110,plain,
    ( spl25_9
  <=> k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_9])])).

fof(f193,plain,
    ( spl25_15
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3))
        | sK7 = k10_mcart_1(X0,X1,X2,X3,sK4)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_15])])).

fof(f210,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK7
    | spl25_1
    | spl25_2
    | spl25_3
    | spl25_4
    | ~ spl25_5
    | ~ spl25_15 ),
    inference(subsumption_resolution,[],[f209,f74])).

fof(f209,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK7
    | k1_xboole_0 = sK0
    | spl25_2
    | spl25_3
    | spl25_4
    | ~ spl25_5
    | ~ spl25_15 ),
    inference(subsumption_resolution,[],[f208,f79])).

fof(f208,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK7
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl25_3
    | spl25_4
    | ~ spl25_5
    | ~ spl25_15 ),
    inference(subsumption_resolution,[],[f207,f84])).

fof(f207,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK7
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl25_4
    | ~ spl25_5
    | ~ spl25_15 ),
    inference(subsumption_resolution,[],[f206,f89])).

fof(f206,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK7
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl25_5
    | ~ spl25_15 ),
    inference(resolution,[],[f194,f94])).

fof(f194,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3))
        | sK7 = k10_mcart_1(X0,X1,X2,X3,sK4)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | ~ spl25_15 ),
    inference(avatar_component_clause,[],[f193])).

fof(f205,plain,
    ( spl25_17
    | ~ spl25_6 ),
    inference(avatar_split_clause,[],[f191,f97,f203])).

fof(f191,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3))
        | sK5 = k8_mcart_1(X0,X1,X2,X3,sK4)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | ~ spl25_6 ),
    inference(superposition,[],[f186,f99])).

fof(f186,plain,(
    ! [X2,X0,X12,X10,X3,X1,X13,X11] :
      ( ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) = X10
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f68,f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_mcart_1)).

fof(f68,plain,(
    ! [X2,X0,X12,X10,X3,X1,X13,X11] :
      ( k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) = X10
      | ~ m1_subset_1(k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)),X0)
      | ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X12,X10,X5,X3,X1,X13,X11] :
      ( X5 = X10
      | k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) != X5
      | ~ m1_subset_1(X5,X0)
      | ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X12,X10,X5,X3,X1,X13,X11] :
      ( X5 = X10
      | k4_mcart_1(X10,X11,X12,X13) != X4
      | k8_mcart_1(X0,X1,X2,X3,X4) != X5
      | ~ m1_subset_1(X5,X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ( sK17(X4,X5) != X5
                    & k4_mcart_1(sK17(X4,X5),sK18(X4,X5),sK19(X4,X5),sK20(X4,X5)) = X4 ) )
                & ( ! [X10,X11,X12,X13] :
                      ( X5 = X10
                      | k4_mcart_1(X10,X11,X12,X13) != X4 )
                  | k8_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X0) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17,sK18,sK19,sK20])],[f33,f34])).

fof(f34,plain,(
    ! [X5,X4] :
      ( ? [X6,X7,X8,X9] :
          ( X5 != X6
          & k4_mcart_1(X6,X7,X8,X9) = X4 )
     => ( sK17(X4,X5) != X5
        & k4_mcart_1(sK17(X4,X5),sK18(X4,X5),sK19(X4,X5),sK20(X4,X5)) = X4 ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ? [X6,X7,X8,X9] :
                      ( X5 != X6
                      & k4_mcart_1(X6,X7,X8,X9) = X4 ) )
                & ( ! [X10,X11,X12,X13] :
                      ( X5 = X10
                      | k4_mcart_1(X10,X11,X12,X13) != X4 )
                  | k8_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X0) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ? [X6,X7,X8,X9] :
                      ( X5 != X6
                      & k4_mcart_1(X6,X7,X8,X9) = X4 ) )
                & ( ! [X6,X7,X8,X9] :
                      ( X5 = X6
                      | k4_mcart_1(X6,X7,X8,X9) != X4 )
                  | k8_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X0) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
              <=> ! [X6,X7,X8,X9] :
                    ( X5 = X6
                    | k4_mcart_1(X6,X7,X8,X9) != X4 ) )
              | ~ m1_subset_1(X5,X0) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
                  <=> ! [X6,X7,X8,X9] :
                        ( k4_mcart_1(X6,X7,X8,X9) = X4
                       => X5 = X6 ) ) ) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_mcart_1)).

fof(f200,plain,
    ( spl25_16
    | ~ spl25_6 ),
    inference(avatar_split_clause,[],[f181,f97,f198])).

fof(f181,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3))
        | sK8 = k11_mcart_1(X0,X1,X2,X3,sK4)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | ~ spl25_6 ),
    inference(superposition,[],[f176,f99])).

fof(f176,plain,(
    ! [X2,X0,X12,X10,X3,X1,X13,X11] :
      ( ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) = X13
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f66,f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_mcart_1)).

fof(f66,plain,(
    ! [X2,X0,X12,X10,X3,X1,X13,X11] :
      ( k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) = X13
      | ~ m1_subset_1(k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)),X3)
      | ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X12,X10,X5,X3,X1,X13,X11] :
      ( X5 = X13
      | k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) != X5
      | ~ m1_subset_1(X5,X3)
      | ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X12,X10,X5,X3,X1,X13,X11] :
      ( X5 = X13
      | k4_mcart_1(X10,X11,X12,X13) != X4
      | k11_mcart_1(X0,X1,X2,X3,X4) != X5
      | ~ m1_subset_1(X5,X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k11_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ( sK16(X4,X5) != X5
                    & k4_mcart_1(sK13(X4,X5),sK14(X4,X5),sK15(X4,X5),sK16(X4,X5)) = X4 ) )
                & ( ! [X10,X11,X12,X13] :
                      ( X5 = X13
                      | k4_mcart_1(X10,X11,X12,X13) != X4 )
                  | k11_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X3) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14,sK15,sK16])],[f29,f30])).

fof(f30,plain,(
    ! [X5,X4] :
      ( ? [X6,X7,X8,X9] :
          ( X5 != X9
          & k4_mcart_1(X6,X7,X8,X9) = X4 )
     => ( sK16(X4,X5) != X5
        & k4_mcart_1(sK13(X4,X5),sK14(X4,X5),sK15(X4,X5),sK16(X4,X5)) = X4 ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k11_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ? [X6,X7,X8,X9] :
                      ( X5 != X9
                      & k4_mcart_1(X6,X7,X8,X9) = X4 ) )
                & ( ! [X10,X11,X12,X13] :
                      ( X5 = X13
                      | k4_mcart_1(X10,X11,X12,X13) != X4 )
                  | k11_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X3) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k11_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ? [X6,X7,X8,X9] :
                      ( X5 != X9
                      & k4_mcart_1(X6,X7,X8,X9) = X4 ) )
                & ( ! [X6,X7,X8,X9] :
                      ( X5 = X9
                      | k4_mcart_1(X6,X7,X8,X9) != X4 )
                  | k11_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X3) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( k11_mcart_1(X0,X1,X2,X3,X4) = X5
              <=> ! [X6,X7,X8,X9] :
                    ( X5 = X9
                    | k4_mcart_1(X6,X7,X8,X9) != X4 ) )
              | ~ m1_subset_1(X5,X3) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => ! [X5] :
                  ( m1_subset_1(X5,X3)
                 => ( k11_mcart_1(X0,X1,X2,X3,X4) = X5
                  <=> ! [X6,X7,X8,X9] :
                        ( k4_mcart_1(X6,X7,X8,X9) = X4
                       => X5 = X9 ) ) ) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_mcart_1)).

fof(f195,plain,
    ( spl25_15
    | ~ spl25_6 ),
    inference(avatar_split_clause,[],[f171,f97,f193])).

fof(f171,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3))
        | sK7 = k10_mcart_1(X0,X1,X2,X3,sK4)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | ~ spl25_6 ),
    inference(superposition,[],[f166,f99])).

fof(f166,plain,(
    ! [X2,X0,X12,X10,X3,X1,X13,X11] :
      ( ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) = X12
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f64,f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_mcart_1)).

fof(f64,plain,(
    ! [X2,X0,X12,X10,X3,X1,X13,X11] :
      ( k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) = X12
      | ~ m1_subset_1(k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)),X2)
      | ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X12,X10,X5,X3,X1,X13,X11] :
      ( X5 = X12
      | k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) != X5
      | ~ m1_subset_1(X5,X2)
      | ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X12,X10,X5,X3,X1,X13,X11] :
      ( X5 = X12
      | k4_mcart_1(X10,X11,X12,X13) != X4
      | k10_mcart_1(X0,X1,X2,X3,X4) != X5
      | ~ m1_subset_1(X5,X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k10_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ( sK11(X4,X5) != X5
                    & k4_mcart_1(sK9(X4,X5),sK10(X4,X5),sK11(X4,X5),sK12(X4,X5)) = X4 ) )
                & ( ! [X10,X11,X12,X13] :
                      ( X5 = X12
                      | k4_mcart_1(X10,X11,X12,X13) != X4 )
                  | k10_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X2) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11,sK12])],[f25,f26])).

fof(f26,plain,(
    ! [X5,X4] :
      ( ? [X6,X7,X8,X9] :
          ( X5 != X8
          & k4_mcart_1(X6,X7,X8,X9) = X4 )
     => ( sK11(X4,X5) != X5
        & k4_mcart_1(sK9(X4,X5),sK10(X4,X5),sK11(X4,X5),sK12(X4,X5)) = X4 ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k10_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ? [X6,X7,X8,X9] :
                      ( X5 != X8
                      & k4_mcart_1(X6,X7,X8,X9) = X4 ) )
                & ( ! [X10,X11,X12,X13] :
                      ( X5 = X12
                      | k4_mcart_1(X10,X11,X12,X13) != X4 )
                  | k10_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X2) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k10_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ? [X6,X7,X8,X9] :
                      ( X5 != X8
                      & k4_mcart_1(X6,X7,X8,X9) = X4 ) )
                & ( ! [X6,X7,X8,X9] :
                      ( X5 = X8
                      | k4_mcart_1(X6,X7,X8,X9) != X4 )
                  | k10_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X2) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( k10_mcart_1(X0,X1,X2,X3,X4) = X5
              <=> ! [X6,X7,X8,X9] :
                    ( X5 = X8
                    | k4_mcart_1(X6,X7,X8,X9) != X4 ) )
              | ~ m1_subset_1(X5,X2) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => ! [X5] :
                  ( m1_subset_1(X5,X2)
                 => ( k10_mcart_1(X0,X1,X2,X3,X4) = X5
                  <=> ! [X6,X7,X8,X9] :
                        ( k4_mcart_1(X6,X7,X8,X9) = X4
                       => X5 = X8 ) ) ) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_mcart_1)).

fof(f117,plain,
    ( ~ spl25_7
    | ~ spl25_8
    | ~ spl25_9
    | ~ spl25_10 ),
    inference(avatar_split_clause,[],[f46,f114,f110,f106,f102])).

fof(f46,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK8
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK7
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK6
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK5 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK8
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK7
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK6
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK5 )
    & sK4 = k4_mcart_1(sK5,sK6,sK7,sK8)
    & m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f11,f22,f21,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ? [X5,X6,X7,X8] :
                ( ( k11_mcart_1(X0,X1,X2,X3,X4) != X8
                  | k10_mcart_1(X0,X1,X2,X3,X4) != X7
                  | k9_mcart_1(X0,X1,X2,X3,X4) != X6
                  | k8_mcart_1(X0,X1,X2,X3,X4) != X5 )
                & k4_mcart_1(X5,X6,X7,X8) = X4 )
            & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ? [X4] :
          ( ? [X8,X7,X6,X5] :
              ( ( k11_mcart_1(sK0,sK1,sK2,sK3,X4) != X8
                | k10_mcart_1(sK0,sK1,sK2,sK3,X4) != X7
                | k9_mcart_1(sK0,sK1,sK2,sK3,X4) != X6
                | k8_mcart_1(sK0,sK1,sK2,sK3,X4) != X5 )
              & k4_mcart_1(X5,X6,X7,X8) = X4 )
          & m1_subset_1(X4,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X4] :
        ( ? [X8,X7,X6,X5] :
            ( ( k11_mcart_1(sK0,sK1,sK2,sK3,X4) != X8
              | k10_mcart_1(sK0,sK1,sK2,sK3,X4) != X7
              | k9_mcart_1(sK0,sK1,sK2,sK3,X4) != X6
              | k8_mcart_1(sK0,sK1,sK2,sK3,X4) != X5 )
            & k4_mcart_1(X5,X6,X7,X8) = X4 )
        & m1_subset_1(X4,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
   => ( ? [X8,X7,X6,X5] :
          ( ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != X8
            | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != X7
            | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != X6
            | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != X5 )
          & k4_mcart_1(X5,X6,X7,X8) = sK4 )
      & m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X8,X7,X6,X5] :
        ( ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != X8
          | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != X7
          | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != X6
          | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != X5 )
        & k4_mcart_1(X5,X6,X7,X8) = sK4 )
   => ( ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK8
        | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK7
        | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK6
        | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK5 )
      & sK4 = k4_mcart_1(sK5,sK6,sK7,sK8) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ? [X5,X6,X7,X8] :
              ( ( k11_mcart_1(X0,X1,X2,X3,X4) != X8
                | k10_mcart_1(X0,X1,X2,X3,X4) != X7
                | k9_mcart_1(X0,X1,X2,X3,X4) != X6
                | k8_mcart_1(X0,X1,X2,X3,X4) != X5 )
              & k4_mcart_1(X5,X6,X7,X8) = X4 )
          & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( ? [X4] :
              ( ? [X5,X6,X7,X8] :
                  ( ~ ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
                      & k10_mcart_1(X0,X1,X2,X3,X4) = X7
                      & k9_mcart_1(X0,X1,X2,X3,X4) = X6
                      & k8_mcart_1(X0,X1,X2,X3,X4) = X5 )
                  & k4_mcart_1(X5,X6,X7,X8) = X4 )
              & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
          & k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( ? [X4] :
            ( ? [X5,X6,X7,X8] :
                ( ~ ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
                    & k10_mcart_1(X0,X1,X2,X3,X4) = X7
                    & k9_mcart_1(X0,X1,X2,X3,X4) = X6
                    & k8_mcart_1(X0,X1,X2,X3,X4) = X5 )
                & k4_mcart_1(X5,X6,X7,X8) = X4 )
            & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_mcart_1)).

fof(f100,plain,(
    spl25_6 ),
    inference(avatar_split_clause,[],[f45,f97])).

fof(f45,plain,(
    sK4 = k4_mcart_1(sK5,sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f23])).

fof(f95,plain,(
    spl25_5 ),
    inference(avatar_split_clause,[],[f44,f92])).

fof(f44,plain,(
    m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f23])).

fof(f90,plain,(
    ~ spl25_4 ),
    inference(avatar_split_clause,[],[f43,f87])).

fof(f43,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f23])).

fof(f85,plain,(
    ~ spl25_3 ),
    inference(avatar_split_clause,[],[f42,f82])).

fof(f42,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f23])).

fof(f80,plain,(
    ~ spl25_2 ),
    inference(avatar_split_clause,[],[f41,f77])).

fof(f41,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f23])).

fof(f75,plain,(
    ~ spl25_1 ),
    inference(avatar_split_clause,[],[f40,f72])).

fof(f40,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n003.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:32:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (10813)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.49  % (10813)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f295,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f75,f80,f85,f90,f95,f100,f117,f195,f200,f205,f212,f237,f239,f264,f294])).
% 0.22/0.49  fof(f294,plain,(
% 0.22/0.49    spl25_1 | spl25_2 | spl25_3 | spl25_4 | ~spl25_5 | spl25_8 | ~spl25_20),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f293])).
% 0.22/0.49  fof(f293,plain,(
% 0.22/0.49    $false | (spl25_1 | spl25_2 | spl25_3 | spl25_4 | ~spl25_5 | spl25_8 | ~spl25_20)),
% 0.22/0.49    inference(subsumption_resolution,[],[f292,f74])).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    k1_xboole_0 != sK0 | spl25_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f72])).
% 0.22/0.49  fof(f72,plain,(
% 0.22/0.49    spl25_1 <=> k1_xboole_0 = sK0),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl25_1])])).
% 0.22/0.49  fof(f292,plain,(
% 0.22/0.49    k1_xboole_0 = sK0 | (spl25_2 | spl25_3 | spl25_4 | ~spl25_5 | spl25_8 | ~spl25_20)),
% 0.22/0.49    inference(subsumption_resolution,[],[f291,f79])).
% 0.22/0.49  fof(f79,plain,(
% 0.22/0.49    k1_xboole_0 != sK1 | spl25_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f77])).
% 0.22/0.49  fof(f77,plain,(
% 0.22/0.49    spl25_2 <=> k1_xboole_0 = sK1),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl25_2])])).
% 0.22/0.49  fof(f291,plain,(
% 0.22/0.49    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (spl25_3 | spl25_4 | ~spl25_5 | spl25_8 | ~spl25_20)),
% 0.22/0.49    inference(subsumption_resolution,[],[f290,f84])).
% 0.22/0.49  fof(f84,plain,(
% 0.22/0.49    k1_xboole_0 != sK2 | spl25_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f82])).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    spl25_3 <=> k1_xboole_0 = sK2),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl25_3])])).
% 0.22/0.49  fof(f290,plain,(
% 0.22/0.49    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (spl25_4 | ~spl25_5 | spl25_8 | ~spl25_20)),
% 0.22/0.49    inference(subsumption_resolution,[],[f289,f89])).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    k1_xboole_0 != sK3 | spl25_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f87])).
% 0.22/0.49  fof(f87,plain,(
% 0.22/0.49    spl25_4 <=> k1_xboole_0 = sK3),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl25_4])])).
% 0.22/0.49  fof(f289,plain,(
% 0.22/0.49    k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl25_5 | spl25_8 | ~spl25_20)),
% 0.22/0.49    inference(subsumption_resolution,[],[f287,f108])).
% 0.22/0.49  fof(f108,plain,(
% 0.22/0.49    k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK6 | spl25_8),
% 0.22/0.49    inference(avatar_component_clause,[],[f106])).
% 0.22/0.49  fof(f106,plain,(
% 0.22/0.49    spl25_8 <=> k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK6),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl25_8])])).
% 0.22/0.49  fof(f287,plain,(
% 0.22/0.49    k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK6 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl25_5 | ~spl25_20)),
% 0.22/0.49    inference(resolution,[],[f236,f94])).
% 0.22/0.49  fof(f94,plain,(
% 0.22/0.49    m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | ~spl25_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f92])).
% 0.22/0.49  fof(f92,plain,(
% 0.22/0.49    spl25_5 <=> m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl25_5])])).
% 0.22/0.49  fof(f236,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3)) | sK6 = k9_mcart_1(X0,X1,X2,X3,sK4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) ) | ~spl25_20),
% 0.22/0.49    inference(avatar_component_clause,[],[f235])).
% 0.22/0.49  fof(f235,plain,(
% 0.22/0.49    spl25_20 <=> ! [X1,X3,X0,X2] : (~m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3)) | sK6 = k9_mcart_1(X0,X1,X2,X3,sK4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl25_20])])).
% 0.22/0.49  fof(f264,plain,(
% 0.22/0.49    spl25_1 | spl25_2 | spl25_3 | spl25_4 | ~spl25_5 | spl25_7 | ~spl25_17),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f263])).
% 0.22/0.49  fof(f263,plain,(
% 0.22/0.49    $false | (spl25_1 | spl25_2 | spl25_3 | spl25_4 | ~spl25_5 | spl25_7 | ~spl25_17)),
% 0.22/0.49    inference(subsumption_resolution,[],[f262,f74])).
% 0.22/0.49  fof(f262,plain,(
% 0.22/0.49    k1_xboole_0 = sK0 | (spl25_2 | spl25_3 | spl25_4 | ~spl25_5 | spl25_7 | ~spl25_17)),
% 0.22/0.49    inference(subsumption_resolution,[],[f261,f79])).
% 0.22/0.49  fof(f261,plain,(
% 0.22/0.49    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (spl25_3 | spl25_4 | ~spl25_5 | spl25_7 | ~spl25_17)),
% 0.22/0.49    inference(subsumption_resolution,[],[f260,f84])).
% 0.22/0.49  fof(f260,plain,(
% 0.22/0.49    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (spl25_4 | ~spl25_5 | spl25_7 | ~spl25_17)),
% 0.22/0.49    inference(subsumption_resolution,[],[f259,f89])).
% 0.22/0.49  fof(f259,plain,(
% 0.22/0.49    k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl25_5 | spl25_7 | ~spl25_17)),
% 0.22/0.49    inference(subsumption_resolution,[],[f257,f104])).
% 0.22/0.49  fof(f104,plain,(
% 0.22/0.49    k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK5 | spl25_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f102])).
% 0.22/0.49  fof(f102,plain,(
% 0.22/0.49    spl25_7 <=> k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK5),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl25_7])])).
% 0.22/0.49  fof(f257,plain,(
% 0.22/0.49    k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK5 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl25_5 | ~spl25_17)),
% 0.22/0.49    inference(resolution,[],[f204,f94])).
% 0.22/0.49  fof(f204,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3)) | sK5 = k8_mcart_1(X0,X1,X2,X3,sK4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) ) | ~spl25_17),
% 0.22/0.49    inference(avatar_component_clause,[],[f203])).
% 0.22/0.49  fof(f203,plain,(
% 0.22/0.49    spl25_17 <=> ! [X1,X3,X0,X2] : (~m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3)) | sK5 = k8_mcart_1(X0,X1,X2,X3,sK4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl25_17])])).
% 0.22/0.49  fof(f239,plain,(
% 0.22/0.49    spl25_10 | spl25_1 | spl25_2 | spl25_3 | spl25_4 | ~spl25_5 | ~spl25_16),
% 0.22/0.49    inference(avatar_split_clause,[],[f233,f198,f92,f87,f82,f77,f72,f114])).
% 0.22/0.49  fof(f114,plain,(
% 0.22/0.49    spl25_10 <=> k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK8),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl25_10])])).
% 0.22/0.49  fof(f198,plain,(
% 0.22/0.49    spl25_16 <=> ! [X1,X3,X0,X2] : (~m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3)) | sK8 = k11_mcart_1(X0,X1,X2,X3,sK4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl25_16])])).
% 0.22/0.49  fof(f233,plain,(
% 0.22/0.49    k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK8 | (spl25_1 | spl25_2 | spl25_3 | spl25_4 | ~spl25_5 | ~spl25_16)),
% 0.22/0.49    inference(subsumption_resolution,[],[f232,f74])).
% 0.22/0.49  fof(f232,plain,(
% 0.22/0.49    k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK8 | k1_xboole_0 = sK0 | (spl25_2 | spl25_3 | spl25_4 | ~spl25_5 | ~spl25_16)),
% 0.22/0.49    inference(subsumption_resolution,[],[f231,f79])).
% 0.22/0.49  fof(f231,plain,(
% 0.22/0.49    k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK8 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (spl25_3 | spl25_4 | ~spl25_5 | ~spl25_16)),
% 0.22/0.49    inference(subsumption_resolution,[],[f230,f84])).
% 0.22/0.49  fof(f230,plain,(
% 0.22/0.49    k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK8 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (spl25_4 | ~spl25_5 | ~spl25_16)),
% 0.22/0.49    inference(subsumption_resolution,[],[f229,f89])).
% 0.22/0.49  fof(f229,plain,(
% 0.22/0.49    k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK8 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl25_5 | ~spl25_16)),
% 0.22/0.49    inference(resolution,[],[f199,f94])).
% 0.22/0.49  fof(f199,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3)) | sK8 = k11_mcart_1(X0,X1,X2,X3,sK4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) ) | ~spl25_16),
% 0.22/0.49    inference(avatar_component_clause,[],[f198])).
% 0.22/0.49  fof(f237,plain,(
% 0.22/0.49    spl25_20 | ~spl25_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f201,f97,f235])).
% 0.22/0.49  fof(f97,plain,(
% 0.22/0.49    spl25_6 <=> sK4 = k4_mcart_1(sK5,sK6,sK7,sK8)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl25_6])])).
% 0.22/0.49  fof(f201,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3)) | sK6 = k9_mcart_1(X0,X1,X2,X3,sK4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) ) | ~spl25_6),
% 0.22/0.49    inference(superposition,[],[f196,f99])).
% 0.22/0.49  fof(f99,plain,(
% 0.22/0.49    sK4 = k4_mcart_1(sK5,sK6,sK7,sK8) | ~spl25_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f97])).
% 0.22/0.49  fof(f196,plain,(
% 0.22/0.49    ( ! [X2,X0,X12,X10,X3,X1,X13,X11] : (~m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3)) | k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) = X11 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f70,f61])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3,X4] : (m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_mcart_1)).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    ( ! [X2,X0,X12,X10,X3,X1,X13,X11] : (k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) = X11 | ~m1_subset_1(k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)),X1) | ~m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.49    inference(equality_resolution,[],[f69])).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    ( ! [X2,X0,X12,X10,X5,X3,X1,X13,X11] : (X5 = X11 | k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) != X5 | ~m1_subset_1(X5,X1) | ~m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.49    inference(equality_resolution,[],[f56])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X12,X10,X5,X3,X1,X13,X11] : (X5 = X11 | k4_mcart_1(X10,X11,X12,X13) != X4 | k9_mcart_1(X0,X1,X2,X3,X4) != X5 | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f39])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (! [X4] : (! [X5] : (((k9_mcart_1(X0,X1,X2,X3,X4) = X5 | (sK22(X4,X5) != X5 & k4_mcart_1(sK21(X4,X5),sK22(X4,X5),sK23(X4,X5),sK24(X4,X5)) = X4)) & (! [X10,X11,X12,X13] : (X5 = X11 | k4_mcart_1(X10,X11,X12,X13) != X4) | k9_mcart_1(X0,X1,X2,X3,X4) != X5)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK21,sK22,sK23,sK24])],[f37,f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ! [X5,X4] : (? [X6,X7,X8,X9] : (X5 != X7 & k4_mcart_1(X6,X7,X8,X9) = X4) => (sK22(X4,X5) != X5 & k4_mcart_1(sK21(X4,X5),sK22(X4,X5),sK23(X4,X5),sK24(X4,X5)) = X4))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (! [X4] : (! [X5] : (((k9_mcart_1(X0,X1,X2,X3,X4) = X5 | ? [X6,X7,X8,X9] : (X5 != X7 & k4_mcart_1(X6,X7,X8,X9) = X4)) & (! [X10,X11,X12,X13] : (X5 = X11 | k4_mcart_1(X10,X11,X12,X13) != X4) | k9_mcart_1(X0,X1,X2,X3,X4) != X5)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.49    inference(rectify,[],[f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (! [X4] : (! [X5] : (((k9_mcart_1(X0,X1,X2,X3,X4) = X5 | ? [X6,X7,X8,X9] : (X5 != X7 & k4_mcart_1(X6,X7,X8,X9) = X4)) & (! [X6,X7,X8,X9] : (X5 = X7 | k4_mcart_1(X6,X7,X8,X9) != X4) | k9_mcart_1(X0,X1,X2,X3,X4) != X5)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.49    inference(nnf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (! [X4] : (! [X5] : ((k9_mcart_1(X0,X1,X2,X3,X4) = X5 <=> ! [X6,X7,X8,X9] : (X5 = X7 | k4_mcart_1(X6,X7,X8,X9) != X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => ! [X5] : (m1_subset_1(X5,X1) => (k9_mcart_1(X0,X1,X2,X3,X4) = X5 <=> ! [X6,X7,X8,X9] : (k4_mcart_1(X6,X7,X8,X9) = X4 => X5 = X7)))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_mcart_1)).
% 0.22/0.49  fof(f212,plain,(
% 0.22/0.49    spl25_9 | spl25_1 | spl25_2 | spl25_3 | spl25_4 | ~spl25_5 | ~spl25_15),
% 0.22/0.49    inference(avatar_split_clause,[],[f210,f193,f92,f87,f82,f77,f72,f110])).
% 0.22/0.49  fof(f110,plain,(
% 0.22/0.49    spl25_9 <=> k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK7),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl25_9])])).
% 0.22/0.49  fof(f193,plain,(
% 0.22/0.49    spl25_15 <=> ! [X1,X3,X0,X2] : (~m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3)) | sK7 = k10_mcart_1(X0,X1,X2,X3,sK4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl25_15])])).
% 0.22/0.49  fof(f210,plain,(
% 0.22/0.49    k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK7 | (spl25_1 | spl25_2 | spl25_3 | spl25_4 | ~spl25_5 | ~spl25_15)),
% 0.22/0.49    inference(subsumption_resolution,[],[f209,f74])).
% 0.22/0.49  fof(f209,plain,(
% 0.22/0.49    k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK7 | k1_xboole_0 = sK0 | (spl25_2 | spl25_3 | spl25_4 | ~spl25_5 | ~spl25_15)),
% 0.22/0.49    inference(subsumption_resolution,[],[f208,f79])).
% 0.22/0.49  fof(f208,plain,(
% 0.22/0.49    k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK7 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (spl25_3 | spl25_4 | ~spl25_5 | ~spl25_15)),
% 0.22/0.49    inference(subsumption_resolution,[],[f207,f84])).
% 0.22/0.49  fof(f207,plain,(
% 0.22/0.49    k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK7 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (spl25_4 | ~spl25_5 | ~spl25_15)),
% 0.22/0.49    inference(subsumption_resolution,[],[f206,f89])).
% 0.22/0.49  fof(f206,plain,(
% 0.22/0.49    k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK7 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl25_5 | ~spl25_15)),
% 0.22/0.49    inference(resolution,[],[f194,f94])).
% 0.22/0.49  fof(f194,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3)) | sK7 = k10_mcart_1(X0,X1,X2,X3,sK4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) ) | ~spl25_15),
% 0.22/0.49    inference(avatar_component_clause,[],[f193])).
% 0.22/0.49  fof(f205,plain,(
% 0.22/0.49    spl25_17 | ~spl25_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f191,f97,f203])).
% 0.22/0.50  fof(f191,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3)) | sK5 = k8_mcart_1(X0,X1,X2,X3,sK4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) ) | ~spl25_6),
% 0.22/0.50    inference(superposition,[],[f186,f99])).
% 0.22/0.50  fof(f186,plain,(
% 0.22/0.50    ( ! [X2,X0,X12,X10,X3,X1,X13,X11] : (~m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3)) | k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) = X10 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f68,f60])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3,X4] : (m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_mcart_1)).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    ( ! [X2,X0,X12,X10,X3,X1,X13,X11] : (k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) = X10 | ~m1_subset_1(k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)),X0) | ~m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.50    inference(equality_resolution,[],[f67])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    ( ! [X2,X0,X12,X10,X5,X3,X1,X13,X11] : (X5 = X10 | k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) != X5 | ~m1_subset_1(X5,X0) | ~m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.50    inference(equality_resolution,[],[f53])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X12,X10,X5,X3,X1,X13,X11] : (X5 = X10 | k4_mcart_1(X10,X11,X12,X13) != X4 | k8_mcart_1(X0,X1,X2,X3,X4) != X5 | ~m1_subset_1(X5,X0) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (! [X4] : (! [X5] : (((k8_mcart_1(X0,X1,X2,X3,X4) = X5 | (sK17(X4,X5) != X5 & k4_mcart_1(sK17(X4,X5),sK18(X4,X5),sK19(X4,X5),sK20(X4,X5)) = X4)) & (! [X10,X11,X12,X13] : (X5 = X10 | k4_mcart_1(X10,X11,X12,X13) != X4) | k8_mcart_1(X0,X1,X2,X3,X4) != X5)) | ~m1_subset_1(X5,X0)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17,sK18,sK19,sK20])],[f33,f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ! [X5,X4] : (? [X6,X7,X8,X9] : (X5 != X6 & k4_mcart_1(X6,X7,X8,X9) = X4) => (sK17(X4,X5) != X5 & k4_mcart_1(sK17(X4,X5),sK18(X4,X5),sK19(X4,X5),sK20(X4,X5)) = X4))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (! [X4] : (! [X5] : (((k8_mcart_1(X0,X1,X2,X3,X4) = X5 | ? [X6,X7,X8,X9] : (X5 != X6 & k4_mcart_1(X6,X7,X8,X9) = X4)) & (! [X10,X11,X12,X13] : (X5 = X10 | k4_mcart_1(X10,X11,X12,X13) != X4) | k8_mcart_1(X0,X1,X2,X3,X4) != X5)) | ~m1_subset_1(X5,X0)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.50    inference(rectify,[],[f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (! [X4] : (! [X5] : (((k8_mcart_1(X0,X1,X2,X3,X4) = X5 | ? [X6,X7,X8,X9] : (X5 != X6 & k4_mcart_1(X6,X7,X8,X9) = X4)) & (! [X6,X7,X8,X9] : (X5 = X6 | k4_mcart_1(X6,X7,X8,X9) != X4) | k8_mcart_1(X0,X1,X2,X3,X4) != X5)) | ~m1_subset_1(X5,X0)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.50    inference(nnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (! [X4] : (! [X5] : ((k8_mcart_1(X0,X1,X2,X3,X4) = X5 <=> ! [X6,X7,X8,X9] : (X5 = X6 | k4_mcart_1(X6,X7,X8,X9) != X4)) | ~m1_subset_1(X5,X0)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => ! [X5] : (m1_subset_1(X5,X0) => (k8_mcart_1(X0,X1,X2,X3,X4) = X5 <=> ! [X6,X7,X8,X9] : (k4_mcart_1(X6,X7,X8,X9) = X4 => X5 = X6)))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_mcart_1)).
% 0.22/0.50  fof(f200,plain,(
% 0.22/0.50    spl25_16 | ~spl25_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f181,f97,f198])).
% 0.22/0.50  fof(f181,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3)) | sK8 = k11_mcart_1(X0,X1,X2,X3,sK4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) ) | ~spl25_6),
% 0.22/0.50    inference(superposition,[],[f176,f99])).
% 0.22/0.50  fof(f176,plain,(
% 0.22/0.50    ( ! [X2,X0,X12,X10,X3,X1,X13,X11] : (~m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3)) | k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) = X13 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f66,f62])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3,X4] : (m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_mcart_1)).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    ( ! [X2,X0,X12,X10,X3,X1,X13,X11] : (k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) = X13 | ~m1_subset_1(k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)),X3) | ~m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.50    inference(equality_resolution,[],[f65])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    ( ! [X2,X0,X12,X10,X5,X3,X1,X13,X11] : (X5 = X13 | k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) != X5 | ~m1_subset_1(X5,X3) | ~m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.50    inference(equality_resolution,[],[f50])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X12,X10,X5,X3,X1,X13,X11] : (X5 = X13 | k4_mcart_1(X10,X11,X12,X13) != X4 | k11_mcart_1(X0,X1,X2,X3,X4) != X5 | ~m1_subset_1(X5,X3) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (! [X4] : (! [X5] : (((k11_mcart_1(X0,X1,X2,X3,X4) = X5 | (sK16(X4,X5) != X5 & k4_mcart_1(sK13(X4,X5),sK14(X4,X5),sK15(X4,X5),sK16(X4,X5)) = X4)) & (! [X10,X11,X12,X13] : (X5 = X13 | k4_mcart_1(X10,X11,X12,X13) != X4) | k11_mcart_1(X0,X1,X2,X3,X4) != X5)) | ~m1_subset_1(X5,X3)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14,sK15,sK16])],[f29,f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ! [X5,X4] : (? [X6,X7,X8,X9] : (X5 != X9 & k4_mcart_1(X6,X7,X8,X9) = X4) => (sK16(X4,X5) != X5 & k4_mcart_1(sK13(X4,X5),sK14(X4,X5),sK15(X4,X5),sK16(X4,X5)) = X4))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (! [X4] : (! [X5] : (((k11_mcart_1(X0,X1,X2,X3,X4) = X5 | ? [X6,X7,X8,X9] : (X5 != X9 & k4_mcart_1(X6,X7,X8,X9) = X4)) & (! [X10,X11,X12,X13] : (X5 = X13 | k4_mcart_1(X10,X11,X12,X13) != X4) | k11_mcart_1(X0,X1,X2,X3,X4) != X5)) | ~m1_subset_1(X5,X3)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.50    inference(rectify,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (! [X4] : (! [X5] : (((k11_mcart_1(X0,X1,X2,X3,X4) = X5 | ? [X6,X7,X8,X9] : (X5 != X9 & k4_mcart_1(X6,X7,X8,X9) = X4)) & (! [X6,X7,X8,X9] : (X5 = X9 | k4_mcart_1(X6,X7,X8,X9) != X4) | k11_mcart_1(X0,X1,X2,X3,X4) != X5)) | ~m1_subset_1(X5,X3)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.50    inference(nnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (! [X4] : (! [X5] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X5 <=> ! [X6,X7,X8,X9] : (X5 = X9 | k4_mcart_1(X6,X7,X8,X9) != X4)) | ~m1_subset_1(X5,X3)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => ! [X5] : (m1_subset_1(X5,X3) => (k11_mcart_1(X0,X1,X2,X3,X4) = X5 <=> ! [X6,X7,X8,X9] : (k4_mcart_1(X6,X7,X8,X9) = X4 => X5 = X9)))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_mcart_1)).
% 0.22/0.50  fof(f195,plain,(
% 0.22/0.50    spl25_15 | ~spl25_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f171,f97,f193])).
% 0.22/0.50  fof(f171,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3)) | sK7 = k10_mcart_1(X0,X1,X2,X3,sK4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) ) | ~spl25_6),
% 0.22/0.50    inference(superposition,[],[f166,f99])).
% 0.22/0.50  fof(f166,plain,(
% 0.22/0.50    ( ! [X2,X0,X12,X10,X3,X1,X13,X11] : (~m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3)) | k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) = X12 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f64,f59])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3,X4] : (m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_mcart_1)).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    ( ! [X2,X0,X12,X10,X3,X1,X13,X11] : (k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) = X12 | ~m1_subset_1(k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)),X2) | ~m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.50    inference(equality_resolution,[],[f63])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    ( ! [X2,X0,X12,X10,X5,X3,X1,X13,X11] : (X5 = X12 | k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) != X5 | ~m1_subset_1(X5,X2) | ~m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.50    inference(equality_resolution,[],[f47])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X12,X10,X5,X3,X1,X13,X11] : (X5 = X12 | k4_mcart_1(X10,X11,X12,X13) != X4 | k10_mcart_1(X0,X1,X2,X3,X4) != X5 | ~m1_subset_1(X5,X2) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (! [X4] : (! [X5] : (((k10_mcart_1(X0,X1,X2,X3,X4) = X5 | (sK11(X4,X5) != X5 & k4_mcart_1(sK9(X4,X5),sK10(X4,X5),sK11(X4,X5),sK12(X4,X5)) = X4)) & (! [X10,X11,X12,X13] : (X5 = X12 | k4_mcart_1(X10,X11,X12,X13) != X4) | k10_mcart_1(X0,X1,X2,X3,X4) != X5)) | ~m1_subset_1(X5,X2)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11,sK12])],[f25,f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X5,X4] : (? [X6,X7,X8,X9] : (X5 != X8 & k4_mcart_1(X6,X7,X8,X9) = X4) => (sK11(X4,X5) != X5 & k4_mcart_1(sK9(X4,X5),sK10(X4,X5),sK11(X4,X5),sK12(X4,X5)) = X4))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (! [X4] : (! [X5] : (((k10_mcart_1(X0,X1,X2,X3,X4) = X5 | ? [X6,X7,X8,X9] : (X5 != X8 & k4_mcart_1(X6,X7,X8,X9) = X4)) & (! [X10,X11,X12,X13] : (X5 = X12 | k4_mcart_1(X10,X11,X12,X13) != X4) | k10_mcart_1(X0,X1,X2,X3,X4) != X5)) | ~m1_subset_1(X5,X2)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.50    inference(rectify,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (! [X4] : (! [X5] : (((k10_mcart_1(X0,X1,X2,X3,X4) = X5 | ? [X6,X7,X8,X9] : (X5 != X8 & k4_mcart_1(X6,X7,X8,X9) = X4)) & (! [X6,X7,X8,X9] : (X5 = X8 | k4_mcart_1(X6,X7,X8,X9) != X4) | k10_mcart_1(X0,X1,X2,X3,X4) != X5)) | ~m1_subset_1(X5,X2)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.50    inference(nnf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (! [X4] : (! [X5] : ((k10_mcart_1(X0,X1,X2,X3,X4) = X5 <=> ! [X6,X7,X8,X9] : (X5 = X8 | k4_mcart_1(X6,X7,X8,X9) != X4)) | ~m1_subset_1(X5,X2)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.50    inference(ennf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => ! [X5] : (m1_subset_1(X5,X2) => (k10_mcart_1(X0,X1,X2,X3,X4) = X5 <=> ! [X6,X7,X8,X9] : (k4_mcart_1(X6,X7,X8,X9) = X4 => X5 = X8)))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_mcart_1)).
% 0.22/0.50  fof(f117,plain,(
% 0.22/0.50    ~spl25_7 | ~spl25_8 | ~spl25_9 | ~spl25_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f46,f114,f110,f106,f102])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK8 | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK7 | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK6 | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK5),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    (((k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK8 | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK7 | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK6 | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK5) & sK4 = k4_mcart_1(sK5,sK6,sK7,sK8)) & m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f11,f22,f21,f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ? [X0,X1,X2,X3] : (? [X4] : (? [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) != X8 | k10_mcart_1(X0,X1,X2,X3,X4) != X7 | k9_mcart_1(X0,X1,X2,X3,X4) != X6 | k8_mcart_1(X0,X1,X2,X3,X4) != X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X4] : (? [X8,X7,X6,X5] : ((k11_mcart_1(sK0,sK1,sK2,sK3,X4) != X8 | k10_mcart_1(sK0,sK1,sK2,sK3,X4) != X7 | k9_mcart_1(sK0,sK1,sK2,sK3,X4) != X6 | k8_mcart_1(sK0,sK1,sK2,sK3,X4) != X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & m1_subset_1(X4,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0)),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ? [X4] : (? [X8,X7,X6,X5] : ((k11_mcart_1(sK0,sK1,sK2,sK3,X4) != X8 | k10_mcart_1(sK0,sK1,sK2,sK3,X4) != X7 | k9_mcart_1(sK0,sK1,sK2,sK3,X4) != X6 | k8_mcart_1(sK0,sK1,sK2,sK3,X4) != X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & m1_subset_1(X4,k4_zfmisc_1(sK0,sK1,sK2,sK3))) => (? [X8,X7,X6,X5] : ((k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != X8 | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != X7 | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != X6 | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != X5) & k4_mcart_1(X5,X6,X7,X8) = sK4) & m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ? [X8,X7,X6,X5] : ((k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != X8 | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != X7 | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != X6 | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != X5) & k4_mcart_1(X5,X6,X7,X8) = sK4) => ((k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK8 | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK7 | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK6 | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK5) & sK4 = k4_mcart_1(sK5,sK6,sK7,sK8))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ? [X0,X1,X2,X3] : (? [X4] : (? [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) != X8 | k10_mcart_1(X0,X1,X2,X3,X4) != X7 | k9_mcart_1(X0,X1,X2,X3,X4) != X6 | k8_mcart_1(X0,X1,X2,X3,X4) != X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1,X2,X3] : ~(? [X4] : (? [X5,X6,X7,X8] : (~(k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.50    inference(negated_conjecture,[],[f9])).
% 0.22/0.50  fof(f9,conjecture,(
% 0.22/0.50    ! [X0,X1,X2,X3] : ~(? [X4] : (? [X5,X6,X7,X8] : (~(k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_mcart_1)).
% 0.22/0.50  fof(f100,plain,(
% 0.22/0.50    spl25_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f45,f97])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    sK4 = k4_mcart_1(sK5,sK6,sK7,sK8)),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    spl25_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f44,f92])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    ~spl25_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f43,f87])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    k1_xboole_0 != sK3),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    ~spl25_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f42,f82])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    k1_xboole_0 != sK2),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    ~spl25_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f41,f77])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    k1_xboole_0 != sK1),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    ~spl25_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f40,f72])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    k1_xboole_0 != sK0),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (10813)------------------------------
% 0.22/0.50  % (10813)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (10813)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (10813)Memory used [KB]: 6396
% 0.22/0.50  % (10813)Time elapsed: 0.054 s
% 0.22/0.50  % (10813)------------------------------
% 0.22/0.50  % (10813)------------------------------
% 0.22/0.50  % (10810)Success in time 0.136 s
%------------------------------------------------------------------------------
