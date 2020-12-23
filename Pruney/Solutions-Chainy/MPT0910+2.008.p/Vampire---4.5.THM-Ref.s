%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:26 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 279 expanded)
%              Number of leaves         :   35 ( 122 expanded)
%              Depth                    :    9
%              Number of atoms          :  449 (1043 expanded)
%              Number of equality atoms :  184 ( 507 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1518,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f73,f78,f83,f88,f164,f210,f215,f220,f224,f228,f232,f247,f898,f958,f1195,f1215,f1338,f1510,f1511,f1517])).

fof(f1517,plain,
    ( spl5_136
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f1515,f240,f955])).

fof(f955,plain,
    ( spl5_136
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_136])])).

fof(f240,plain,
    ( spl5_25
  <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f1515,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl5_25 ),
    inference(resolution,[],[f242,f37])).

fof(f37,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f242,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f240])).

fof(f1511,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK4) != k2_mcart_1(sK4)
    | k5_mcart_1(sK0,sK1,sK2,sK4) != k1_mcart_1(k1_mcart_1(sK4))
    | k6_mcart_1(sK0,sK1,sK2,sK4) != k2_mcart_1(k1_mcart_1(sK4))
    | k1_mcart_1(sK4) != k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)))
    | sK4 != k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))
    | sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK4),k6_mcart_1(sK0,sK1,sK2,sK4)),k7_mcart_1(sK0,sK1,sK2,sK4)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1510,plain,
    ( spl5_214
    | spl5_3
    | spl5_4
    | ~ spl5_187 ),
    inference(avatar_split_clause,[],[f1509,f1335,f80,f75,f1504])).

fof(f1504,plain,
    ( spl5_214
  <=> k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_214])])).

fof(f75,plain,
    ( spl5_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f80,plain,
    ( spl5_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f1335,plain,
    ( spl5_187
  <=> m1_subset_1(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_187])])).

fof(f1509,plain,
    ( k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)))
    | spl5_3
    | spl5_4
    | ~ spl5_187 ),
    inference(subsumption_resolution,[],[f1508,f82])).

fof(f82,plain,
    ( k1_xboole_0 != sK0
    | spl5_4 ),
    inference(avatar_component_clause,[],[f80])).

fof(f1508,plain,
    ( k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)))
    | k1_xboole_0 = sK0
    | spl5_3
    | ~ spl5_187 ),
    inference(subsumption_resolution,[],[f1501,f77])).

fof(f77,plain,
    ( k1_xboole_0 != sK1
    | spl5_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f1501,plain,
    ( k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl5_187 ),
    inference(resolution,[],[f1337,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2
      | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2
          | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( ~ ! [X2] :
              ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
             => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_mcart_1)).

fof(f1337,plain,
    ( m1_subset_1(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1))
    | ~ spl5_187 ),
    inference(avatar_component_clause,[],[f1335])).

fof(f1338,plain,
    ( spl5_187
    | ~ spl5_176 ),
    inference(avatar_split_clause,[],[f1330,f1211,f1335])).

fof(f1211,plain,
    ( spl5_176
  <=> r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_176])])).

fof(f1330,plain,
    ( m1_subset_1(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1))
    | ~ spl5_176 ),
    inference(unit_resulting_resolution,[],[f1213,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f1213,plain,
    ( r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1))
    | ~ spl5_176 ),
    inference(avatar_component_clause,[],[f1211])).

fof(f1215,plain,
    ( spl5_176
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f1202,f244,f1211])).

fof(f244,plain,
    ( spl5_26
  <=> r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f1202,plain,
    ( r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1))
    | ~ spl5_26 ),
    inference(resolution,[],[f246,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f246,plain,
    ( r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f244])).

fof(f1195,plain,
    ( ~ spl5_174
    | spl5_1
    | ~ spl5_21
    | ~ spl5_22
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f1182,f217,f212,f207,f65,f1192])).

fof(f1192,plain,
    ( spl5_174
  <=> sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK4),k6_mcart_1(sK0,sK1,sK2,sK4)),k7_mcart_1(sK0,sK1,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_174])])).

fof(f65,plain,
    ( spl5_1
  <=> sK3 = k6_mcart_1(sK0,sK1,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f207,plain,
    ( spl5_21
  <=> m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f212,plain,
    ( spl5_22
  <=> m1_subset_1(k7_mcart_1(sK0,sK1,sK2,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f217,plain,
    ( spl5_23
  <=> m1_subset_1(k6_mcart_1(sK0,sK1,sK2,sK4),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f1182,plain,
    ( sK4 != k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK4),k6_mcart_1(sK0,sK1,sK2,sK4)),k7_mcart_1(sK0,sK1,sK2,sK4))
    | spl5_1
    | ~ spl5_21
    | ~ spl5_22
    | ~ spl5_23 ),
    inference(unit_resulting_resolution,[],[f209,f214,f67,f219,f54])).

fof(f54,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X7,sK2)
      | sK4 != k4_tarski(k4_tarski(X5,X6),X7)
      | sK3 = X6
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(definition_unfolding,[],[f32,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f32,plain,(
    ! [X6,X7,X5] :
      ( sK3 = X6
      | k3_mcart_1(X5,X6,X7) != sK4
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f16,f27])).

fof(f27,plain,
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

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_mcart_1)).

fof(f219,plain,
    ( m1_subset_1(k6_mcart_1(sK0,sK1,sK2,sK4),sK1)
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f217])).

fof(f67,plain,
    ( sK3 != k6_mcart_1(sK0,sK1,sK2,sK4)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f214,plain,
    ( m1_subset_1(k7_mcart_1(sK0,sK1,sK2,sK4),sK2)
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f212])).

fof(f209,plain,
    ( m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0)
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f207])).

fof(f958,plain,
    ( ~ spl5_136
    | spl5_2
    | spl5_15 ),
    inference(avatar_split_clause,[],[f883,f161,f70,f955])).

fof(f70,plain,
    ( spl5_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f161,plain,
    ( spl5_15
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f883,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | spl5_2
    | spl5_15 ),
    inference(unit_resulting_resolution,[],[f72,f163,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f163,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | spl5_15 ),
    inference(avatar_component_clause,[],[f161])).

fof(f72,plain,
    ( k1_xboole_0 != sK2
    | spl5_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f898,plain,
    ( spl5_24
    | spl5_2
    | ~ spl5_5
    | spl5_15 ),
    inference(avatar_split_clause,[],[f897,f161,f85,f70,f235])).

fof(f235,plain,
    ( spl5_24
  <=> sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f85,plain,
    ( spl5_5
  <=> m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f897,plain,
    ( sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))
    | spl5_2
    | ~ spl5_5
    | spl5_15 ),
    inference(unit_resulting_resolution,[],[f72,f87,f163,f43])).

fof(f87,plain,
    ( m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f85])).

fof(f247,plain,
    ( spl5_25
    | spl5_26
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f190,f85,f244,f240])).

fof(f190,plain,
    ( r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl5_5 ),
    inference(resolution,[],[f87,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f232,plain,
    ( spl5_18
    | spl5_2
    | spl5_3
    | spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f231,f85,f80,f75,f70,f192])).

fof(f192,plain,
    ( spl5_18
  <=> k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f231,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)
    | spl5_2
    | spl5_3
    | spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f230,f82])).

fof(f230,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)
    | k1_xboole_0 = sK0
    | spl5_2
    | spl5_3
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f229,f77])).

fof(f229,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f188,f72])).

fof(f188,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl5_5 ),
    inference(resolution,[],[f87,f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f50,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f228,plain,
    ( spl5_19
    | spl5_2
    | spl5_3
    | spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f227,f85,f80,f75,f70,f197])).

fof(f197,plain,
    ( spl5_19
  <=> k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f227,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | spl5_2
    | spl5_3
    | spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f226,f82])).

fof(f226,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK0
    | spl5_2
    | spl5_3
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f225,f77])).

fof(f225,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f187,f72])).

fof(f187,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl5_5 ),
    inference(resolution,[],[f87,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f49,f45])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f224,plain,
    ( spl5_20
    | spl5_2
    | spl5_3
    | spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f223,f85,f80,f75,f70,f202])).

fof(f202,plain,
    ( spl5_20
  <=> k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f223,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4))
    | spl5_2
    | spl5_3
    | spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f222,f82])).

fof(f222,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK0
    | spl5_2
    | spl5_3
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f221,f77])).

fof(f221,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f186,f72])).

fof(f186,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl5_5 ),
    inference(resolution,[],[f87,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f48,f45])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f220,plain,
    ( spl5_23
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f177,f85,f217])).

fof(f177,plain,
    ( m1_subset_1(k6_mcart_1(sK0,sK1,sK2,sK4),sK1)
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f87,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f53,f45])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_mcart_1)).

fof(f215,plain,
    ( spl5_22
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f178,f85,f212])).

fof(f178,plain,
    ( m1_subset_1(k7_mcart_1(sK0,sK1,sK2,sK4),sK2)
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f87,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f52,f45])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_mcart_1)).

fof(f210,plain,
    ( spl5_21
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f179,f85,f207])).

fof(f179,plain,
    ( m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0)
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f87,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f51,f45])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_mcart_1)).

fof(f164,plain,
    ( ~ spl5_15
    | spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f137,f80,f75,f161])).

fof(f137,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | spl5_3
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f77,f82,f40])).

fof(f88,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f55,f85])).

fof(f55,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f31,f45])).

fof(f31,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f28])).

fof(f83,plain,(
    ~ spl5_4 ),
    inference(avatar_split_clause,[],[f33,f80])).

fof(f33,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f28])).

fof(f78,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f34,f75])).

fof(f34,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f28])).

fof(f73,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f35,f70])).

fof(f35,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f28])).

fof(f68,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f36,f65])).

fof(f36,plain,(
    sK3 != k6_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:43:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (29768)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % (29777)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.52  % (29776)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.53  % (29786)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.53  % (29761)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (29761)Refutation not found, incomplete strategy% (29761)------------------------------
% 0.22/0.53  % (29761)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (29761)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (29761)Memory used [KB]: 10746
% 0.22/0.53  % (29761)Time elapsed: 0.096 s
% 0.22/0.53  % (29761)------------------------------
% 0.22/0.53  % (29761)------------------------------
% 0.22/0.53  % (29785)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.53  % (29777)Refutation not found, incomplete strategy% (29777)------------------------------
% 0.22/0.53  % (29777)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (29777)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (29777)Memory used [KB]: 10618
% 0.22/0.53  % (29777)Time elapsed: 0.111 s
% 0.22/0.53  % (29777)------------------------------
% 0.22/0.53  % (29777)------------------------------
% 0.22/0.54  % (29759)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (29773)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.55  % (29760)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.55  % (29782)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.55  % (29763)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.56  % (29766)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.56  % (29765)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.56  % (29785)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f1518,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(avatar_sat_refutation,[],[f68,f73,f78,f83,f88,f164,f210,f215,f220,f224,f228,f232,f247,f898,f958,f1195,f1215,f1338,f1510,f1511,f1517])).
% 0.22/0.56  fof(f1517,plain,(
% 0.22/0.56    spl5_136 | ~spl5_25),
% 0.22/0.56    inference(avatar_split_clause,[],[f1515,f240,f955])).
% 0.22/0.56  fof(f955,plain,(
% 0.22/0.56    spl5_136 <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_136])])).
% 0.22/0.56  fof(f240,plain,(
% 0.22/0.56    spl5_25 <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.22/0.56  fof(f1515,plain,(
% 0.22/0.56    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl5_25),
% 0.22/0.56    inference(resolution,[],[f242,f37])).
% 0.22/0.56  fof(f37,plain,(
% 0.22/0.56    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f17])).
% 0.22/0.56  fof(f17,plain,(
% 0.22/0.56    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f1])).
% 0.22/0.56  fof(f1,axiom,(
% 0.22/0.56    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.56  fof(f242,plain,(
% 0.22/0.56    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl5_25),
% 0.22/0.56    inference(avatar_component_clause,[],[f240])).
% 0.22/0.56  fof(f1511,plain,(
% 0.22/0.56    k7_mcart_1(sK0,sK1,sK2,sK4) != k2_mcart_1(sK4) | k5_mcart_1(sK0,sK1,sK2,sK4) != k1_mcart_1(k1_mcart_1(sK4)) | k6_mcart_1(sK0,sK1,sK2,sK4) != k2_mcart_1(k1_mcart_1(sK4)) | k1_mcart_1(sK4) != k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) | sK4 != k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) | sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK4),k6_mcart_1(sK0,sK1,sK2,sK4)),k7_mcart_1(sK0,sK1,sK2,sK4))),
% 0.22/0.56    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.56  fof(f1510,plain,(
% 0.22/0.56    spl5_214 | spl5_3 | spl5_4 | ~spl5_187),
% 0.22/0.56    inference(avatar_split_clause,[],[f1509,f1335,f80,f75,f1504])).
% 0.22/0.56  fof(f1504,plain,(
% 0.22/0.56    spl5_214 <=> k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_214])])).
% 0.22/0.56  fof(f75,plain,(
% 0.22/0.56    spl5_3 <=> k1_xboole_0 = sK1),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.56  fof(f80,plain,(
% 0.22/0.56    spl5_4 <=> k1_xboole_0 = sK0),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.56  fof(f1335,plain,(
% 0.22/0.56    spl5_187 <=> m1_subset_1(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_187])])).
% 0.22/0.56  fof(f1509,plain,(
% 0.22/0.56    k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) | (spl5_3 | spl5_4 | ~spl5_187)),
% 0.22/0.56    inference(subsumption_resolution,[],[f1508,f82])).
% 0.22/0.56  fof(f82,plain,(
% 0.22/0.56    k1_xboole_0 != sK0 | spl5_4),
% 0.22/0.56    inference(avatar_component_clause,[],[f80])).
% 0.22/0.56  fof(f1508,plain,(
% 0.22/0.56    k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) | k1_xboole_0 = sK0 | (spl5_3 | ~spl5_187)),
% 0.22/0.56    inference(subsumption_resolution,[],[f1501,f77])).
% 0.22/0.56  fof(f77,plain,(
% 0.22/0.56    k1_xboole_0 != sK1 | spl5_3),
% 0.22/0.56    inference(avatar_component_clause,[],[f75])).
% 0.22/0.56  fof(f1501,plain,(
% 0.22/0.56    k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl5_187),
% 0.22/0.56    inference(resolution,[],[f1337,f43])).
% 0.22/0.56  fof(f43,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 | ~m1_subset_1(X2,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.56    inference(cnf_transformation,[],[f21])).
% 0.22/0.56  fof(f21,plain,(
% 0.22/0.56    ! [X0,X1] : (! [X2] : (k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 | ~m1_subset_1(X2,k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.56    inference(ennf_transformation,[],[f11])).
% 0.22/0.56  fof(f11,axiom,(
% 0.22/0.56    ! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_mcart_1)).
% 0.22/0.56  fof(f1337,plain,(
% 0.22/0.56    m1_subset_1(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1)) | ~spl5_187),
% 0.22/0.56    inference(avatar_component_clause,[],[f1335])).
% 0.22/0.56  fof(f1338,plain,(
% 0.22/0.56    spl5_187 | ~spl5_176),
% 0.22/0.56    inference(avatar_split_clause,[],[f1330,f1211,f1335])).
% 0.22/0.56  fof(f1211,plain,(
% 0.22/0.56    spl5_176 <=> r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_176])])).
% 0.22/0.56  fof(f1330,plain,(
% 0.22/0.56    m1_subset_1(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1)) | ~spl5_176),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f1213,f38])).
% 0.22/0.56  fof(f38,plain,(
% 0.22/0.56    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f18])).
% 0.22/0.56  fof(f18,plain,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.22/0.56    inference(ennf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.22/0.56  fof(f1213,plain,(
% 0.22/0.56    r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1)) | ~spl5_176),
% 0.22/0.56    inference(avatar_component_clause,[],[f1211])).
% 0.22/0.56  fof(f1215,plain,(
% 0.22/0.56    spl5_176 | ~spl5_26),
% 0.22/0.56    inference(avatar_split_clause,[],[f1202,f244,f1211])).
% 0.22/0.56  fof(f244,plain,(
% 0.22/0.56    spl5_26 <=> r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.22/0.56  fof(f1202,plain,(
% 0.22/0.56    r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1)) | ~spl5_26),
% 0.22/0.56    inference(resolution,[],[f246,f46])).
% 0.22/0.56  fof(f46,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f22])).
% 0.22/0.56  fof(f22,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.22/0.56    inference(ennf_transformation,[],[f10])).
% 0.22/0.56  fof(f10,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.22/0.56  fof(f246,plain,(
% 0.22/0.56    r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl5_26),
% 0.22/0.56    inference(avatar_component_clause,[],[f244])).
% 0.22/0.56  fof(f1195,plain,(
% 0.22/0.56    ~spl5_174 | spl5_1 | ~spl5_21 | ~spl5_22 | ~spl5_23),
% 0.22/0.56    inference(avatar_split_clause,[],[f1182,f217,f212,f207,f65,f1192])).
% 0.22/0.56  fof(f1192,plain,(
% 0.22/0.56    spl5_174 <=> sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK4),k6_mcart_1(sK0,sK1,sK2,sK4)),k7_mcart_1(sK0,sK1,sK2,sK4))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_174])])).
% 0.22/0.56  fof(f65,plain,(
% 0.22/0.56    spl5_1 <=> sK3 = k6_mcart_1(sK0,sK1,sK2,sK4)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.56  fof(f207,plain,(
% 0.22/0.56    spl5_21 <=> m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.22/0.56  fof(f212,plain,(
% 0.22/0.56    spl5_22 <=> m1_subset_1(k7_mcart_1(sK0,sK1,sK2,sK4),sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.22/0.56  fof(f217,plain,(
% 0.22/0.56    spl5_23 <=> m1_subset_1(k6_mcart_1(sK0,sK1,sK2,sK4),sK1)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.22/0.56  fof(f1182,plain,(
% 0.22/0.56    sK4 != k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK4),k6_mcart_1(sK0,sK1,sK2,sK4)),k7_mcart_1(sK0,sK1,sK2,sK4)) | (spl5_1 | ~spl5_21 | ~spl5_22 | ~spl5_23)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f209,f214,f67,f219,f54])).
% 0.22/0.56  fof(f54,plain,(
% 0.22/0.56    ( ! [X6,X7,X5] : (~m1_subset_1(X7,sK2) | sK4 != k4_tarski(k4_tarski(X5,X6),X7) | sK3 = X6 | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 0.22/0.56    inference(definition_unfolding,[],[f32,f44])).
% 0.22/0.56  fof(f44,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f5])).
% 0.22/0.56  fof(f5,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.22/0.56  fof(f32,plain,(
% 0.22/0.56    ( ! [X6,X7,X5] : (sK3 = X6 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f28])).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    sK3 != k6_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X6 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f16,f27])).
% 0.22/0.56  fof(f27,plain,(
% 0.22/0.56    ? [X0,X1,X2,X3,X4] : (k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X6 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (sK3 != k6_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X6 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f16,plain,(
% 0.22/0.56    ? [X0,X1,X2,X3,X4] : (k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X6 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.22/0.56    inference(flattening,[],[f15])).
% 0.22/0.56  fof(f15,plain,(
% 0.22/0.56    ? [X0,X1,X2,X3,X4] : (((k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X6 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.22/0.56    inference(ennf_transformation,[],[f14])).
% 0.22/0.56  fof(f14,negated_conjecture,(
% 0.22/0.56    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X6)))) => (k6_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.22/0.56    inference(negated_conjecture,[],[f13])).
% 0.22/0.56  fof(f13,conjecture,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X6)))) => (k6_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_mcart_1)).
% 0.22/0.56  fof(f219,plain,(
% 0.22/0.56    m1_subset_1(k6_mcart_1(sK0,sK1,sK2,sK4),sK1) | ~spl5_23),
% 0.22/0.56    inference(avatar_component_clause,[],[f217])).
% 0.22/0.56  fof(f67,plain,(
% 0.22/0.56    sK3 != k6_mcart_1(sK0,sK1,sK2,sK4) | spl5_1),
% 0.22/0.56    inference(avatar_component_clause,[],[f65])).
% 0.22/0.56  fof(f214,plain,(
% 0.22/0.56    m1_subset_1(k7_mcart_1(sK0,sK1,sK2,sK4),sK2) | ~spl5_22),
% 0.22/0.56    inference(avatar_component_clause,[],[f212])).
% 0.22/0.56  fof(f209,plain,(
% 0.22/0.56    m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0) | ~spl5_21),
% 0.22/0.56    inference(avatar_component_clause,[],[f207])).
% 0.22/0.56  fof(f958,plain,(
% 0.22/0.56    ~spl5_136 | spl5_2 | spl5_15),
% 0.22/0.56    inference(avatar_split_clause,[],[f883,f161,f70,f955])).
% 0.22/0.56  fof(f70,plain,(
% 0.22/0.56    spl5_2 <=> k1_xboole_0 = sK2),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.56  fof(f161,plain,(
% 0.22/0.56    spl5_15 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.22/0.56  fof(f883,plain,(
% 0.22/0.56    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | (spl5_2 | spl5_15)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f72,f163,f40])).
% 0.22/0.56  fof(f40,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f30])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.56    inference(flattening,[],[f29])).
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.56    inference(nnf_transformation,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.56  fof(f163,plain,(
% 0.22/0.56    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) | spl5_15),
% 0.22/0.56    inference(avatar_component_clause,[],[f161])).
% 0.22/0.56  fof(f72,plain,(
% 0.22/0.56    k1_xboole_0 != sK2 | spl5_2),
% 0.22/0.56    inference(avatar_component_clause,[],[f70])).
% 0.22/0.56  fof(f898,plain,(
% 0.22/0.56    spl5_24 | spl5_2 | ~spl5_5 | spl5_15),
% 0.22/0.56    inference(avatar_split_clause,[],[f897,f161,f85,f70,f235])).
% 0.22/0.56  fof(f235,plain,(
% 0.22/0.56    spl5_24 <=> sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.22/0.56  fof(f85,plain,(
% 0.22/0.56    spl5_5 <=> m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.56  fof(f897,plain,(
% 0.22/0.56    sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) | (spl5_2 | ~spl5_5 | spl5_15)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f72,f87,f163,f43])).
% 0.22/0.56  fof(f87,plain,(
% 0.22/0.56    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl5_5),
% 0.22/0.56    inference(avatar_component_clause,[],[f85])).
% 0.22/0.56  fof(f247,plain,(
% 0.22/0.56    spl5_25 | spl5_26 | ~spl5_5),
% 0.22/0.56    inference(avatar_split_clause,[],[f190,f85,f244,f240])).
% 0.22/0.56  fof(f190,plain,(
% 0.22/0.56    r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl5_5),
% 0.22/0.56    inference(resolution,[],[f87,f39])).
% 0.22/0.56  fof(f39,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f20])).
% 0.22/0.56  fof(f20,plain,(
% 0.22/0.56    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.56    inference(flattening,[],[f19])).
% 0.22/0.56  fof(f19,plain,(
% 0.22/0.56    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.56    inference(ennf_transformation,[],[f4])).
% 0.22/0.56  fof(f4,axiom,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.56  fof(f232,plain,(
% 0.22/0.56    spl5_18 | spl5_2 | spl5_3 | spl5_4 | ~spl5_5),
% 0.22/0.56    inference(avatar_split_clause,[],[f231,f85,f80,f75,f70,f192])).
% 0.22/0.56  fof(f192,plain,(
% 0.22/0.56    spl5_18 <=> k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.22/0.56  fof(f231,plain,(
% 0.22/0.56    k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) | (spl5_2 | spl5_3 | spl5_4 | ~spl5_5)),
% 0.22/0.56    inference(subsumption_resolution,[],[f230,f82])).
% 0.22/0.56  fof(f230,plain,(
% 0.22/0.56    k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) | k1_xboole_0 = sK0 | (spl5_2 | spl5_3 | ~spl5_5)),
% 0.22/0.56    inference(subsumption_resolution,[],[f229,f77])).
% 0.22/0.56  fof(f229,plain,(
% 0.22/0.56    k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (spl5_2 | ~spl5_5)),
% 0.22/0.56    inference(subsumption_resolution,[],[f188,f72])).
% 0.22/0.56  fof(f188,plain,(
% 0.22/0.56    k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl5_5),
% 0.22/0.56    inference(resolution,[],[f87,f56])).
% 0.22/0.56  fof(f56,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.56    inference(definition_unfolding,[],[f50,f45])).
% 0.22/0.56  fof(f45,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f6])).
% 0.22/0.56  fof(f6,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.22/0.56  fof(f50,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.56    inference(cnf_transformation,[],[f23])).
% 0.22/0.56  fof(f23,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.56    inference(ennf_transformation,[],[f12])).
% 0.22/0.56  fof(f12,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).
% 0.22/0.56  fof(f228,plain,(
% 0.22/0.56    spl5_19 | spl5_2 | spl5_3 | spl5_4 | ~spl5_5),
% 0.22/0.56    inference(avatar_split_clause,[],[f227,f85,f80,f75,f70,f197])).
% 0.22/0.56  fof(f197,plain,(
% 0.22/0.56    spl5_19 <=> k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.22/0.56  fof(f227,plain,(
% 0.22/0.56    k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4)) | (spl5_2 | spl5_3 | spl5_4 | ~spl5_5)),
% 0.22/0.56    inference(subsumption_resolution,[],[f226,f82])).
% 0.22/0.56  fof(f226,plain,(
% 0.22/0.56    k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK0 | (spl5_2 | spl5_3 | ~spl5_5)),
% 0.22/0.56    inference(subsumption_resolution,[],[f225,f77])).
% 0.22/0.56  fof(f225,plain,(
% 0.22/0.56    k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (spl5_2 | ~spl5_5)),
% 0.22/0.56    inference(subsumption_resolution,[],[f187,f72])).
% 0.22/0.56  fof(f187,plain,(
% 0.22/0.56    k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl5_5),
% 0.22/0.56    inference(resolution,[],[f87,f57])).
% 0.22/0.56  fof(f57,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.56    inference(definition_unfolding,[],[f49,f45])).
% 0.22/0.56  fof(f49,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.56    inference(cnf_transformation,[],[f23])).
% 0.22/0.56  fof(f224,plain,(
% 0.22/0.56    spl5_20 | spl5_2 | spl5_3 | spl5_4 | ~spl5_5),
% 0.22/0.56    inference(avatar_split_clause,[],[f223,f85,f80,f75,f70,f202])).
% 0.22/0.56  fof(f202,plain,(
% 0.22/0.56    spl5_20 <=> k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.22/0.56  fof(f223,plain,(
% 0.22/0.56    k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4)) | (spl5_2 | spl5_3 | spl5_4 | ~spl5_5)),
% 0.22/0.56    inference(subsumption_resolution,[],[f222,f82])).
% 0.22/0.56  fof(f222,plain,(
% 0.22/0.56    k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK0 | (spl5_2 | spl5_3 | ~spl5_5)),
% 0.22/0.56    inference(subsumption_resolution,[],[f221,f77])).
% 0.22/0.56  fof(f221,plain,(
% 0.22/0.56    k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (spl5_2 | ~spl5_5)),
% 0.22/0.56    inference(subsumption_resolution,[],[f186,f72])).
% 0.22/0.56  fof(f186,plain,(
% 0.22/0.56    k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl5_5),
% 0.22/0.56    inference(resolution,[],[f87,f58])).
% 0.22/0.56  fof(f58,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.56    inference(definition_unfolding,[],[f48,f45])).
% 0.22/0.56  fof(f48,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.56    inference(cnf_transformation,[],[f23])).
% 0.22/0.56  fof(f220,plain,(
% 0.22/0.56    spl5_23 | ~spl5_5),
% 0.22/0.56    inference(avatar_split_clause,[],[f177,f85,f217])).
% 0.22/0.56  fof(f177,plain,(
% 0.22/0.56    m1_subset_1(k6_mcart_1(sK0,sK1,sK2,sK4),sK1) | ~spl5_5),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f87,f61])).
% 0.22/0.56  fof(f61,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 0.22/0.56    inference(definition_unfolding,[],[f53,f45])).
% 0.22/0.56  fof(f53,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f26])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3] : (m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 0.22/0.56    inference(ennf_transformation,[],[f8])).
% 0.22/0.56  fof(f8,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_mcart_1)).
% 0.22/0.56  fof(f215,plain,(
% 0.22/0.56    spl5_22 | ~spl5_5),
% 0.22/0.56    inference(avatar_split_clause,[],[f178,f85,f212])).
% 0.22/0.56  fof(f178,plain,(
% 0.22/0.56    m1_subset_1(k7_mcart_1(sK0,sK1,sK2,sK4),sK2) | ~spl5_5),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f87,f60])).
% 0.22/0.56  fof(f60,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 0.22/0.56    inference(definition_unfolding,[],[f52,f45])).
% 0.22/0.56  fof(f52,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f25])).
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 0.22/0.56    inference(ennf_transformation,[],[f9])).
% 0.22/0.56  fof(f9,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_mcart_1)).
% 0.22/0.56  fof(f210,plain,(
% 0.22/0.56    spl5_21 | ~spl5_5),
% 0.22/0.56    inference(avatar_split_clause,[],[f179,f85,f207])).
% 0.22/0.56  fof(f179,plain,(
% 0.22/0.56    m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0) | ~spl5_5),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f87,f59])).
% 0.22/0.56  fof(f59,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 0.22/0.56    inference(definition_unfolding,[],[f51,f45])).
% 0.22/0.56  fof(f51,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f24])).
% 0.22/0.56  fof(f24,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 0.22/0.56    inference(ennf_transformation,[],[f7])).
% 0.22/0.56  fof(f7,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_mcart_1)).
% 0.22/0.56  fof(f164,plain,(
% 0.22/0.56    ~spl5_15 | spl5_3 | spl5_4),
% 0.22/0.56    inference(avatar_split_clause,[],[f137,f80,f75,f161])).
% 0.22/0.56  fof(f137,plain,(
% 0.22/0.56    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) | (spl5_3 | spl5_4)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f77,f82,f40])).
% 0.22/0.56  fof(f88,plain,(
% 0.22/0.56    spl5_5),
% 0.22/0.56    inference(avatar_split_clause,[],[f55,f85])).
% 0.22/0.56  fof(f55,plain,(
% 0.22/0.56    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.22/0.56    inference(definition_unfolding,[],[f31,f45])).
% 0.22/0.56  fof(f31,plain,(
% 0.22/0.56    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.22/0.56    inference(cnf_transformation,[],[f28])).
% 0.22/0.56  fof(f83,plain,(
% 0.22/0.56    ~spl5_4),
% 0.22/0.56    inference(avatar_split_clause,[],[f33,f80])).
% 0.22/0.56  fof(f33,plain,(
% 0.22/0.56    k1_xboole_0 != sK0),
% 0.22/0.56    inference(cnf_transformation,[],[f28])).
% 0.22/0.56  fof(f78,plain,(
% 0.22/0.56    ~spl5_3),
% 0.22/0.56    inference(avatar_split_clause,[],[f34,f75])).
% 0.22/0.56  fof(f34,plain,(
% 0.22/0.56    k1_xboole_0 != sK1),
% 0.22/0.56    inference(cnf_transformation,[],[f28])).
% 0.22/0.56  fof(f73,plain,(
% 0.22/0.56    ~spl5_2),
% 0.22/0.56    inference(avatar_split_clause,[],[f35,f70])).
% 0.22/0.56  fof(f35,plain,(
% 0.22/0.56    k1_xboole_0 != sK2),
% 0.22/0.56    inference(cnf_transformation,[],[f28])).
% 0.22/0.56  fof(f68,plain,(
% 0.22/0.56    ~spl5_1),
% 0.22/0.56    inference(avatar_split_clause,[],[f36,f65])).
% 0.22/0.56  fof(f36,plain,(
% 0.22/0.56    sK3 != k6_mcart_1(sK0,sK1,sK2,sK4)),
% 0.22/0.56    inference(cnf_transformation,[],[f28])).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (29785)------------------------------
% 0.22/0.56  % (29785)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (29785)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (29785)Memory used [KB]: 7419
% 0.22/0.56  % (29785)Time elapsed: 0.127 s
% 0.22/0.56  % (29785)------------------------------
% 0.22/0.56  % (29785)------------------------------
% 0.22/0.56  % (29754)Success in time 0.195 s
%------------------------------------------------------------------------------
