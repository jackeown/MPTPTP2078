%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:32 EST 2020

% Result     : Theorem 1.70s
% Output     : Refutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :  186 ( 405 expanded)
%              Number of leaves         :   44 ( 170 expanded)
%              Depth                    :   12
%              Number of atoms          :  495 (1075 expanded)
%              Number of equality atoms :  189 ( 520 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1509,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f84,f89,f94,f99,f150,f293,f700,f712,f741,f749,f808,f844,f848,f850,f860,f867,f877,f891,f899,f919,f925,f986,f1003,f1008,f1033,f1051,f1098,f1103,f1120,f1137,f1503])).

fof(f1503,plain,
    ( spl8_48
    | ~ spl8_68
    | ~ spl8_32
    | ~ spl8_49
    | ~ spl8_52
    | ~ spl8_76 ),
    inference(avatar_split_clause,[],[f1498,f1134,f896,f857,f507,f1048,f746])).

fof(f746,plain,
    ( spl8_48
  <=> sK3 = k2_mcart_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).

fof(f1048,plain,
    ( spl8_68
  <=> sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_68])])).

fof(f507,plain,
    ( spl8_32
  <=> m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f857,plain,
    ( spl8_49
  <=> m1_subset_1(k2_mcart_1(sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).

fof(f896,plain,
    ( spl8_52
  <=> m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).

fof(f1134,plain,
    ( spl8_76
  <=> k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_76])])).

fof(f1498,plain,
    ( sK4 != k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))
    | sK3 = k2_mcart_1(sK4)
    | ~ spl8_32
    | ~ spl8_49
    | ~ spl8_52
    | ~ spl8_76 ),
    inference(resolution,[],[f1490,f859])).

fof(f859,plain,
    ( m1_subset_1(k2_mcart_1(sK4),sK2)
    | ~ spl8_49 ),
    inference(avatar_component_clause,[],[f857])).

fof(f1490,plain,
    ( ! [X8] :
        ( ~ m1_subset_1(X8,sK2)
        | sK4 != k4_tarski(k1_mcart_1(sK4),X8)
        | sK3 = X8 )
    | ~ spl8_32
    | ~ spl8_52
    | ~ spl8_76 ),
    inference(forward_demodulation,[],[f1485,f1136])).

fof(f1136,plain,
    ( k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)))
    | ~ spl8_76 ),
    inference(avatar_component_clause,[],[f1134])).

fof(f1485,plain,
    ( ! [X8] :
        ( ~ m1_subset_1(X8,sK2)
        | sK4 != k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))),X8)
        | sK3 = X8 )
    | ~ spl8_32
    | ~ spl8_52 ),
    inference(resolution,[],[f632,f898])).

fof(f898,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | ~ spl8_52 ),
    inference(avatar_component_clause,[],[f896])).

fof(f632,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,sK1)
        | ~ m1_subset_1(X1,sK2)
        | sK4 != k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),X0),X1)
        | sK3 = X1 )
    | ~ spl8_32 ),
    inference(resolution,[],[f509,f60])).

fof(f60,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X5,sK0)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X7,sK2)
      | sK4 != k4_tarski(k4_tarski(X5,X6),X7)
      | sK3 = X7 ) ),
    inference(definition_unfolding,[],[f28,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f28,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X5,sK0)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X7,sK2)
      | k3_mcart_1(X5,X6,X7) != sK4
      | sK3 = X7 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X7 ) ) ) )
         => ( k7_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X7 ) ) ) )
       => ( k7_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).

fof(f509,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f507])).

fof(f1137,plain,
    ( spl8_76
    | ~ spl8_70
    | ~ spl8_73 ),
    inference(avatar_split_clause,[],[f1132,f1117,f1100,f1134])).

fof(f1100,plain,
    ( spl8_70
  <=> k1_mcart_1(k1_mcart_1(sK4)) = sK6(k1_mcart_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_70])])).

fof(f1117,plain,
    ( spl8_73
  <=> k1_mcart_1(sK4) = k4_tarski(sK6(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_73])])).

fof(f1132,plain,
    ( k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)))
    | ~ spl8_70
    | ~ spl8_73 ),
    inference(forward_demodulation,[],[f1119,f1102])).

fof(f1102,plain,
    ( k1_mcart_1(k1_mcart_1(sK4)) = sK6(k1_mcart_1(sK4))
    | ~ spl8_70 ),
    inference(avatar_component_clause,[],[f1100])).

fof(f1119,plain,
    ( k1_mcart_1(sK4) = k4_tarski(sK6(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)))
    | ~ spl8_73 ),
    inference(avatar_component_clause,[],[f1117])).

fof(f1120,plain,
    ( spl8_73
    | ~ spl8_54
    | ~ spl8_69 ),
    inference(avatar_split_clause,[],[f1114,f1095,f916,f1117])).

fof(f916,plain,
    ( spl8_54
  <=> k1_mcart_1(sK4) = k4_tarski(sK6(k1_mcart_1(sK4)),sK7(k1_mcart_1(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_54])])).

fof(f1095,plain,
    ( spl8_69
  <=> k2_mcart_1(k1_mcart_1(sK4)) = sK7(k1_mcart_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_69])])).

fof(f1114,plain,
    ( k1_mcart_1(sK4) = k4_tarski(sK6(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)))
    | ~ spl8_54
    | ~ spl8_69 ),
    inference(backward_demodulation,[],[f918,f1097])).

fof(f1097,plain,
    ( k2_mcart_1(k1_mcart_1(sK4)) = sK7(k1_mcart_1(sK4))
    | ~ spl8_69 ),
    inference(avatar_component_clause,[],[f1095])).

fof(f918,plain,
    ( k1_mcart_1(sK4) = k4_tarski(sK6(k1_mcart_1(sK4)),sK7(k1_mcart_1(sK4)))
    | ~ spl8_54 ),
    inference(avatar_component_clause,[],[f916])).

fof(f1103,plain,
    ( spl8_70
    | ~ spl8_54 ),
    inference(avatar_split_clause,[],[f1091,f916,f1100])).

fof(f1091,plain,
    ( k1_mcart_1(k1_mcart_1(sK4)) = sK6(k1_mcart_1(sK4))
    | ~ spl8_54 ),
    inference(superposition,[],[f40,f918])).

fof(f40,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f1098,plain,
    ( spl8_69
    | ~ spl8_54 ),
    inference(avatar_split_clause,[],[f1090,f916,f1095])).

fof(f1090,plain,
    ( k2_mcart_1(k1_mcart_1(sK4)) = sK7(k1_mcart_1(sK4))
    | ~ spl8_54 ),
    inference(superposition,[],[f41,f918])).

fof(f41,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f13])).

fof(f1051,plain,
    ( spl8_68
    | ~ spl8_62
    | ~ spl8_65 ),
    inference(avatar_split_clause,[],[f1046,f1030,f1005,f1048])).

fof(f1005,plain,
    ( spl8_62
  <=> k1_mcart_1(sK4) = sK6(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_62])])).

fof(f1030,plain,
    ( spl8_65
  <=> sK4 = k4_tarski(sK6(sK4),k2_mcart_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_65])])).

fof(f1046,plain,
    ( sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))
    | ~ spl8_62
    | ~ spl8_65 ),
    inference(forward_demodulation,[],[f1032,f1007])).

fof(f1007,plain,
    ( k1_mcart_1(sK4) = sK6(sK4)
    | ~ spl8_62 ),
    inference(avatar_component_clause,[],[f1005])).

fof(f1032,plain,
    ( sK4 = k4_tarski(sK6(sK4),k2_mcart_1(sK4))
    | ~ spl8_65 ),
    inference(avatar_component_clause,[],[f1030])).

fof(f1033,plain,
    ( spl8_65
    | ~ spl8_41
    | ~ spl8_61 ),
    inference(avatar_split_clause,[],[f1027,f1000,f642,f1030])).

fof(f642,plain,
    ( spl8_41
  <=> sK4 = k4_tarski(sK6(sK4),sK7(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).

fof(f1000,plain,
    ( spl8_61
  <=> k2_mcart_1(sK4) = sK7(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_61])])).

fof(f1027,plain,
    ( sK4 = k4_tarski(sK6(sK4),k2_mcart_1(sK4))
    | ~ spl8_41
    | ~ spl8_61 ),
    inference(backward_demodulation,[],[f644,f1002])).

fof(f1002,plain,
    ( k2_mcart_1(sK4) = sK7(sK4)
    | ~ spl8_61 ),
    inference(avatar_component_clause,[],[f1000])).

fof(f644,plain,
    ( sK4 = k4_tarski(sK6(sK4),sK7(sK4))
    | ~ spl8_41 ),
    inference(avatar_component_clause,[],[f642])).

fof(f1008,plain,
    ( spl8_62
    | ~ spl8_41 ),
    inference(avatar_split_clause,[],[f996,f642,f1005])).

fof(f996,plain,
    ( k1_mcart_1(sK4) = sK6(sK4)
    | ~ spl8_41 ),
    inference(superposition,[],[f40,f644])).

fof(f1003,plain,
    ( spl8_61
    | ~ spl8_41 ),
    inference(avatar_split_clause,[],[f995,f642,f1000])).

fof(f995,plain,
    ( k2_mcart_1(sK4) = sK7(sK4)
    | ~ spl8_41 ),
    inference(superposition,[],[f41,f644])).

fof(f986,plain,
    ( spl8_34
    | spl8_4
    | spl8_2
    | spl8_3
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f980,f96,f86,f81,f91,f524])).

fof(f524,plain,
    ( spl8_34
  <=> k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f91,plain,
    ( spl8_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f81,plain,
    ( spl8_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f86,plain,
    ( spl8_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f96,plain,
    ( spl8_5
  <=> m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f980,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)
    | ~ spl8_5 ),
    inference(resolution,[],[f61,f98])).

fof(f98,plain,
    ( m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f96])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) ) ),
    inference(definition_unfolding,[],[f50,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f925,plain,
    ( spl8_41
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f920,f104,f642])).

fof(f104,plain,
    ( spl8_6
  <=> r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f920,plain,
    ( sK4 = k4_tarski(sK6(sK4),sK7(sK4))
    | ~ spl8_6 ),
    inference(resolution,[],[f106,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | k4_tarski(sK6(X0),sK7(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X0
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(f106,plain,
    ( r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f104])).

fof(f919,plain,
    ( spl8_54
    | ~ spl8_23 ),
    inference(avatar_split_clause,[],[f911,f340,f916])).

fof(f340,plain,
    ( spl8_23
  <=> r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f911,plain,
    ( k1_mcart_1(sK4) = k4_tarski(sK6(k1_mcart_1(sK4)),sK7(k1_mcart_1(sK4)))
    | ~ spl8_23 ),
    inference(resolution,[],[f51,f342])).

fof(f342,plain,
    ( r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1))
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f340])).

fof(f899,plain,
    ( spl8_52
    | ~ spl8_51 ),
    inference(avatar_split_clause,[],[f893,f888,f896])).

fof(f888,plain,
    ( spl8_51
  <=> r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_51])])).

fof(f893,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | ~ spl8_51 ),
    inference(resolution,[],[f890,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f890,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | ~ spl8_51 ),
    inference(avatar_component_clause,[],[f888])).

fof(f891,plain,
    ( spl8_51
    | ~ spl8_23 ),
    inference(avatar_split_clause,[],[f883,f340,f888])).

fof(f883,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | ~ spl8_23 ),
    inference(resolution,[],[f342,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f877,plain,
    ( spl8_32
    | ~ spl8_24 ),
    inference(avatar_split_clause,[],[f875,f348,f507])).

fof(f348,plain,
    ( spl8_24
  <=> r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f875,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)
    | ~ spl8_24 ),
    inference(resolution,[],[f350,f43])).

fof(f350,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0)
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f348])).

fof(f867,plain,
    ( spl8_6
    | spl8_7
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f866,f96,f108,f104])).

fof(f108,plain,
    ( spl8_7
  <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f866,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl8_5 ),
    inference(resolution,[],[f98,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f860,plain,
    ( spl8_49
    | ~ spl8_42 ),
    inference(avatar_split_clause,[],[f854,f647,f857])).

fof(f647,plain,
    ( spl8_42
  <=> r2_hidden(k2_mcart_1(sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f854,plain,
    ( m1_subset_1(k2_mcart_1(sK4),sK2)
    | ~ spl8_42 ),
    inference(resolution,[],[f649,f43])).

fof(f649,plain,
    ( r2_hidden(k2_mcart_1(sK4),sK2)
    | ~ spl8_42 ),
    inference(avatar_component_clause,[],[f647])).

fof(f850,plain,
    ( spl8_23
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f336,f104,f340])).

fof(f336,plain,
    ( r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1))
    | ~ spl8_6 ),
    inference(resolution,[],[f46,f106])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f848,plain,
    ( spl8_42
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f635,f104,f647])).

fof(f635,plain,
    ( r2_hidden(k2_mcart_1(sK4),sK2)
    | ~ spl8_6 ),
    inference(resolution,[],[f106,f47])).

fof(f844,plain,
    ( spl8_24
    | ~ spl8_23 ),
    inference(avatar_split_clause,[],[f344,f340,f348])).

fof(f344,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0)
    | ~ spl8_23 ),
    inference(resolution,[],[f342,f46])).

fof(f808,plain,
    ( spl8_4
    | ~ spl8_11
    | ~ spl8_14 ),
    inference(avatar_contradiction_clause,[],[f807])).

fof(f807,plain,
    ( $false
    | spl8_4
    | ~ spl8_11
    | ~ spl8_14 ),
    inference(trivial_inequality_removal,[],[f800])).

fof(f800,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl8_4
    | ~ spl8_11
    | ~ spl8_14 ),
    inference(superposition,[],[f93,f755])).

fof(f755,plain,
    ( ! [X0] : k1_xboole_0 = X0
    | ~ spl8_11
    | ~ spl8_14 ),
    inference(trivial_inequality_removal,[],[f754])).

fof(f754,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | k1_xboole_0 = X0 )
    | ~ spl8_11
    | ~ spl8_14 ),
    inference(superposition,[],[f244,f172])).

fof(f172,plain,
    ( ! [X4] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X4)
    | ~ spl8_11 ),
    inference(forward_demodulation,[],[f160,f148])).

fof(f148,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl8_11
  <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f160,plain,(
    ! [X4] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),X4) ),
    inference(superposition,[],[f72,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 != X3 ) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f52,f45])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0
      | k1_xboole_0 != X3 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

fof(f72,plain,(
    ! [X0,X3,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 != X2 ) ),
    inference(definition_unfolding,[],[f56,f58])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0
      | k1_xboole_0 != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f244,plain,
    ( ! [X1] :
        ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X1)
        | k1_xboole_0 = X1 )
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl8_14
  <=> ! [X1] :
        ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X1)
        | k1_xboole_0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f93,plain,
    ( k1_xboole_0 != sK0
    | spl8_4 ),
    inference(avatar_component_clause,[],[f91])).

fof(f749,plain,
    ( ~ spl8_48
    | spl8_1
    | ~ spl8_34 ),
    inference(avatar_split_clause,[],[f744,f524,f76,f746])).

fof(f76,plain,
    ( spl8_1
  <=> sK3 = k7_mcart_1(sK0,sK1,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f744,plain,
    ( sK3 != k2_mcart_1(sK4)
    | spl8_1
    | ~ spl8_34 ),
    inference(superposition,[],[f78,f526])).

fof(f526,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)
    | ~ spl8_34 ),
    inference(avatar_component_clause,[],[f524])).

fof(f78,plain,
    ( sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f741,plain,
    ( spl8_12
    | spl8_2
    | spl8_13
    | spl8_14
    | ~ spl8_8
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f740,f146,f114,f243,f239,f81,f236])).

fof(f236,plain,
    ( spl8_12
  <=> ! [X0] : k1_xboole_0 = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f239,plain,
    ( spl8_13
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f114,plain,
    ( spl8_8
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f740,plain,
    ( ! [X14,X13] :
        ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X14)
        | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
        | k1_xboole_0 = sK2
        | k1_xboole_0 = X13
        | k1_xboole_0 = X14 )
    | ~ spl8_8
    | ~ spl8_11 ),
    inference(forward_demodulation,[],[f727,f172])).

fof(f727,plain,
    ( ! [X14,X13] :
        ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X13),X14)
        | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
        | k1_xboole_0 = sK2
        | k1_xboole_0 = X13
        | k1_xboole_0 = X14 )
    | ~ spl8_8 ),
    inference(superposition,[],[f68,f116])).

fof(f116,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f114])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3 ) ),
    inference(definition_unfolding,[],[f53,f58])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f712,plain,
    ( spl8_8
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f711,f108,f114])).

fof(f711,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl8_7 ),
    inference(resolution,[],[f110,f101])).

fof(f101,plain,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f39,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).

fof(f110,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f108])).

fof(f700,plain,
    ( spl8_12
    | spl8_3
    | spl8_4
    | spl8_14
    | ~ spl8_11
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f699,f239,f146,f243,f91,f86,f236])).

fof(f699,plain,
    ( ! [X10,X9] :
        ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X10)
        | k1_xboole_0 = sK0
        | k1_xboole_0 = sK1
        | k1_xboole_0 = X9
        | k1_xboole_0 = X10 )
    | ~ spl8_11
    | ~ spl8_13 ),
    inference(forward_demodulation,[],[f679,f172])).

fof(f679,plain,
    ( ! [X10,X9] :
        ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X9),X10)
        | k1_xboole_0 = sK0
        | k1_xboole_0 = sK1
        | k1_xboole_0 = X9
        | k1_xboole_0 = X10 )
    | ~ spl8_13 ),
    inference(superposition,[],[f68,f241])).

fof(f241,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f239])).

fof(f293,plain,
    ( spl8_4
    | ~ spl8_12 ),
    inference(avatar_contradiction_clause,[],[f292])).

fof(f292,plain,
    ( $false
    | spl8_4
    | ~ spl8_12 ),
    inference(trivial_inequality_removal,[],[f285])).

fof(f285,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl8_4
    | ~ spl8_12 ),
    inference(superposition,[],[f93,f237])).

fof(f237,plain,
    ( ! [X0] : k1_xboole_0 = X0
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f236])).

fof(f150,plain,(
    spl8_11 ),
    inference(avatar_split_clause,[],[f142,f146])).

fof(f142,plain,(
    k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f71,f71])).

fof(f99,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f59,f96])).

fof(f59,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f29,f45])).

fof(f29,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f94,plain,(
    ~ spl8_4 ),
    inference(avatar_split_clause,[],[f30,f91])).

fof(f30,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f18])).

fof(f89,plain,(
    ~ spl8_3 ),
    inference(avatar_split_clause,[],[f31,f86])).

fof(f31,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f18])).

fof(f84,plain,(
    ~ spl8_2 ),
    inference(avatar_split_clause,[],[f32,f81])).

fof(f32,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f18])).

fof(f79,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f33,f76])).

fof(f33,plain,(
    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:20:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (8447)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.50  % (8438)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (8438)Refutation not found, incomplete strategy% (8438)------------------------------
% 0.20/0.50  % (8438)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (8438)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (8438)Memory used [KB]: 10746
% 0.20/0.50  % (8438)Time elapsed: 0.104 s
% 0.20/0.50  % (8438)------------------------------
% 0.20/0.50  % (8438)------------------------------
% 0.20/0.50  % (8454)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.50  % (8435)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.50  % (8462)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.51  % (8435)Refutation not found, incomplete strategy% (8435)------------------------------
% 0.20/0.51  % (8435)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (8435)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (8435)Memory used [KB]: 1663
% 0.20/0.51  % (8435)Time elapsed: 0.097 s
% 0.20/0.51  % (8435)------------------------------
% 0.20/0.51  % (8435)------------------------------
% 0.20/0.51  % (8441)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (8460)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.51  % (8436)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (8448)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (8446)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.51  % (8446)Refutation not found, incomplete strategy% (8446)------------------------------
% 0.20/0.51  % (8446)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (8446)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (8446)Memory used [KB]: 10618
% 0.20/0.51  % (8446)Time elapsed: 0.106 s
% 0.20/0.51  % (8446)------------------------------
% 0.20/0.51  % (8446)------------------------------
% 0.20/0.51  % (8452)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.52  % (8463)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.52  % (8457)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.52  % (8445)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.52  % (8464)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.52  % (8445)Refutation not found, incomplete strategy% (8445)------------------------------
% 0.20/0.52  % (8445)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (8445)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (8445)Memory used [KB]: 10618
% 0.20/0.52  % (8445)Time elapsed: 0.126 s
% 0.20/0.52  % (8445)------------------------------
% 0.20/0.52  % (8445)------------------------------
% 0.20/0.52  % (8444)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (8455)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.53  % (8443)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.53  % (8453)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.53  % (8451)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (8439)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (8449)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (8465)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (8440)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (8441)Refutation not found, incomplete strategy% (8441)------------------------------
% 0.20/0.53  % (8441)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (8441)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (8441)Memory used [KB]: 6396
% 0.20/0.53  % (8441)Time elapsed: 0.129 s
% 0.20/0.53  % (8441)------------------------------
% 0.20/0.53  % (8441)------------------------------
% 0.20/0.53  % (8456)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % (8461)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (8456)Refutation not found, incomplete strategy% (8456)------------------------------
% 0.20/0.54  % (8456)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (8456)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (8456)Memory used [KB]: 10746
% 0.20/0.54  % (8456)Time elapsed: 0.132 s
% 0.20/0.54  % (8456)------------------------------
% 0.20/0.54  % (8456)------------------------------
% 0.20/0.54  % (8459)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.54  % (8459)Refutation not found, incomplete strategy% (8459)------------------------------
% 0.20/0.54  % (8459)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (8444)Refutation not found, incomplete strategy% (8444)------------------------------
% 0.20/0.54  % (8444)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (8459)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (8459)Memory used [KB]: 1791
% 0.20/0.54  % (8459)Time elapsed: 0.143 s
% 0.20/0.54  % (8459)------------------------------
% 0.20/0.54  % (8459)------------------------------
% 0.20/0.54  % (8453)Refutation not found, incomplete strategy% (8453)------------------------------
% 0.20/0.54  % (8453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (8453)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (8453)Memory used [KB]: 10618
% 0.20/0.54  % (8453)Time elapsed: 0.142 s
% 0.20/0.54  % (8453)------------------------------
% 0.20/0.54  % (8453)------------------------------
% 0.20/0.54  % (8444)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (8444)Memory used [KB]: 10746
% 0.20/0.54  % (8444)Time elapsed: 0.144 s
% 0.20/0.54  % (8444)------------------------------
% 0.20/0.54  % (8444)------------------------------
% 0.20/0.55  % (8458)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.56  % (8450)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.56  % (8442)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.57  % (8458)Refutation not found, incomplete strategy% (8458)------------------------------
% 0.20/0.57  % (8458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (8458)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (8458)Memory used [KB]: 10874
% 0.20/0.57  % (8458)Time elapsed: 0.080 s
% 0.20/0.57  % (8458)------------------------------
% 0.20/0.57  % (8458)------------------------------
% 1.70/0.60  % (8452)Refutation found. Thanks to Tanya!
% 1.70/0.60  % SZS status Theorem for theBenchmark
% 1.70/0.60  % SZS output start Proof for theBenchmark
% 1.70/0.60  fof(f1509,plain,(
% 1.70/0.60    $false),
% 1.70/0.60    inference(avatar_sat_refutation,[],[f79,f84,f89,f94,f99,f150,f293,f700,f712,f741,f749,f808,f844,f848,f850,f860,f867,f877,f891,f899,f919,f925,f986,f1003,f1008,f1033,f1051,f1098,f1103,f1120,f1137,f1503])).
% 1.70/0.60  fof(f1503,plain,(
% 1.70/0.60    spl8_48 | ~spl8_68 | ~spl8_32 | ~spl8_49 | ~spl8_52 | ~spl8_76),
% 1.70/0.60    inference(avatar_split_clause,[],[f1498,f1134,f896,f857,f507,f1048,f746])).
% 1.70/0.60  fof(f746,plain,(
% 1.70/0.60    spl8_48 <=> sK3 = k2_mcart_1(sK4)),
% 1.70/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).
% 1.70/0.60  fof(f1048,plain,(
% 1.70/0.60    spl8_68 <=> sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))),
% 1.70/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_68])])).
% 1.70/0.60  fof(f507,plain,(
% 1.70/0.60    spl8_32 <=> m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)),
% 1.70/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).
% 1.70/0.60  fof(f857,plain,(
% 1.70/0.60    spl8_49 <=> m1_subset_1(k2_mcart_1(sK4),sK2)),
% 1.70/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).
% 1.70/0.60  fof(f896,plain,(
% 1.70/0.60    spl8_52 <=> m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)),
% 1.70/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).
% 1.70/0.60  fof(f1134,plain,(
% 1.70/0.60    spl8_76 <=> k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)))),
% 1.70/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_76])])).
% 1.70/0.60  fof(f1498,plain,(
% 1.70/0.60    sK4 != k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) | sK3 = k2_mcart_1(sK4) | (~spl8_32 | ~spl8_49 | ~spl8_52 | ~spl8_76)),
% 1.70/0.60    inference(resolution,[],[f1490,f859])).
% 1.70/0.60  fof(f859,plain,(
% 1.70/0.60    m1_subset_1(k2_mcart_1(sK4),sK2) | ~spl8_49),
% 1.70/0.60    inference(avatar_component_clause,[],[f857])).
% 1.70/0.60  fof(f1490,plain,(
% 1.70/0.60    ( ! [X8] : (~m1_subset_1(X8,sK2) | sK4 != k4_tarski(k1_mcart_1(sK4),X8) | sK3 = X8) ) | (~spl8_32 | ~spl8_52 | ~spl8_76)),
% 1.70/0.60    inference(forward_demodulation,[],[f1485,f1136])).
% 1.70/0.60  fof(f1136,plain,(
% 1.70/0.60    k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) | ~spl8_76),
% 1.70/0.60    inference(avatar_component_clause,[],[f1134])).
% 1.70/0.60  fof(f1485,plain,(
% 1.70/0.60    ( ! [X8] : (~m1_subset_1(X8,sK2) | sK4 != k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))),X8) | sK3 = X8) ) | (~spl8_32 | ~spl8_52)),
% 1.70/0.60    inference(resolution,[],[f632,f898])).
% 1.70/0.60  fof(f898,plain,(
% 1.70/0.60    m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) | ~spl8_52),
% 1.70/0.60    inference(avatar_component_clause,[],[f896])).
% 1.70/0.60  fof(f632,plain,(
% 1.70/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,sK1) | ~m1_subset_1(X1,sK2) | sK4 != k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),X0),X1) | sK3 = X1) ) | ~spl8_32),
% 1.70/0.60    inference(resolution,[],[f509,f60])).
% 1.70/0.60  fof(f60,plain,(
% 1.70/0.60    ( ! [X6,X7,X5] : (~m1_subset_1(X5,sK0) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X7,sK2) | sK4 != k4_tarski(k4_tarski(X5,X6),X7) | sK3 = X7) )),
% 1.70/0.60    inference(definition_unfolding,[],[f28,f44])).
% 1.70/0.60  fof(f44,plain,(
% 1.70/0.60    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 1.70/0.60    inference(cnf_transformation,[],[f5])).
% 1.70/0.60  fof(f5,axiom,(
% 1.70/0.60    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 1.70/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 1.70/0.60  fof(f28,plain,(
% 1.70/0.60    ( ! [X6,X7,X5] : (~m1_subset_1(X5,sK0) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X7,sK2) | k3_mcart_1(X5,X6,X7) != sK4 | sK3 = X7) )),
% 1.70/0.60    inference(cnf_transformation,[],[f18])).
% 1.70/0.60  fof(f18,plain,(
% 1.70/0.60    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 1.70/0.60    inference(flattening,[],[f17])).
% 1.70/0.60  fof(f17,plain,(
% 1.70/0.60    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 1.70/0.60    inference(ennf_transformation,[],[f15])).
% 1.70/0.60  fof(f15,negated_conjecture,(
% 1.70/0.60    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.70/0.60    inference(negated_conjecture,[],[f14])).
% 1.70/0.60  fof(f14,conjecture,(
% 1.70/0.60    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.70/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).
% 1.70/0.60  fof(f509,plain,(
% 1.70/0.60    m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) | ~spl8_32),
% 1.70/0.60    inference(avatar_component_clause,[],[f507])).
% 1.70/0.60  fof(f1137,plain,(
% 1.70/0.60    spl8_76 | ~spl8_70 | ~spl8_73),
% 1.70/0.60    inference(avatar_split_clause,[],[f1132,f1117,f1100,f1134])).
% 1.70/0.60  fof(f1100,plain,(
% 1.70/0.60    spl8_70 <=> k1_mcart_1(k1_mcart_1(sK4)) = sK6(k1_mcart_1(sK4))),
% 1.70/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_70])])).
% 1.70/0.60  fof(f1117,plain,(
% 1.70/0.60    spl8_73 <=> k1_mcart_1(sK4) = k4_tarski(sK6(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)))),
% 1.70/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_73])])).
% 1.70/0.60  fof(f1132,plain,(
% 1.70/0.60    k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) | (~spl8_70 | ~spl8_73)),
% 1.70/0.60    inference(forward_demodulation,[],[f1119,f1102])).
% 1.70/0.60  fof(f1102,plain,(
% 1.70/0.60    k1_mcart_1(k1_mcart_1(sK4)) = sK6(k1_mcart_1(sK4)) | ~spl8_70),
% 1.70/0.60    inference(avatar_component_clause,[],[f1100])).
% 1.70/0.60  fof(f1119,plain,(
% 1.70/0.60    k1_mcart_1(sK4) = k4_tarski(sK6(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) | ~spl8_73),
% 1.70/0.60    inference(avatar_component_clause,[],[f1117])).
% 1.70/0.60  fof(f1120,plain,(
% 1.70/0.60    spl8_73 | ~spl8_54 | ~spl8_69),
% 1.70/0.60    inference(avatar_split_clause,[],[f1114,f1095,f916,f1117])).
% 1.70/0.60  fof(f916,plain,(
% 1.70/0.60    spl8_54 <=> k1_mcart_1(sK4) = k4_tarski(sK6(k1_mcart_1(sK4)),sK7(k1_mcart_1(sK4)))),
% 1.70/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_54])])).
% 1.70/0.60  fof(f1095,plain,(
% 1.70/0.60    spl8_69 <=> k2_mcart_1(k1_mcart_1(sK4)) = sK7(k1_mcart_1(sK4))),
% 1.70/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_69])])).
% 1.70/0.60  fof(f1114,plain,(
% 1.70/0.60    k1_mcart_1(sK4) = k4_tarski(sK6(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) | (~spl8_54 | ~spl8_69)),
% 1.70/0.60    inference(backward_demodulation,[],[f918,f1097])).
% 1.70/0.60  fof(f1097,plain,(
% 1.70/0.60    k2_mcart_1(k1_mcart_1(sK4)) = sK7(k1_mcart_1(sK4)) | ~spl8_69),
% 1.70/0.60    inference(avatar_component_clause,[],[f1095])).
% 1.70/0.60  fof(f918,plain,(
% 1.70/0.60    k1_mcart_1(sK4) = k4_tarski(sK6(k1_mcart_1(sK4)),sK7(k1_mcart_1(sK4))) | ~spl8_54),
% 1.70/0.60    inference(avatar_component_clause,[],[f916])).
% 1.70/0.60  fof(f1103,plain,(
% 1.70/0.60    spl8_70 | ~spl8_54),
% 1.70/0.60    inference(avatar_split_clause,[],[f1091,f916,f1100])).
% 1.70/0.60  fof(f1091,plain,(
% 1.70/0.60    k1_mcart_1(k1_mcart_1(sK4)) = sK6(k1_mcart_1(sK4)) | ~spl8_54),
% 1.70/0.60    inference(superposition,[],[f40,f918])).
% 1.70/0.60  fof(f40,plain,(
% 1.70/0.60    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 1.70/0.60    inference(cnf_transformation,[],[f13])).
% 1.70/0.60  fof(f13,axiom,(
% 1.70/0.60    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 1.70/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 1.70/0.60  fof(f1098,plain,(
% 1.70/0.60    spl8_69 | ~spl8_54),
% 1.70/0.60    inference(avatar_split_clause,[],[f1090,f916,f1095])).
% 1.70/0.60  fof(f1090,plain,(
% 1.70/0.60    k2_mcart_1(k1_mcart_1(sK4)) = sK7(k1_mcart_1(sK4)) | ~spl8_54),
% 1.70/0.60    inference(superposition,[],[f41,f918])).
% 1.70/0.60  fof(f41,plain,(
% 1.70/0.60    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 1.70/0.60    inference(cnf_transformation,[],[f13])).
% 1.70/0.60  fof(f1051,plain,(
% 1.70/0.60    spl8_68 | ~spl8_62 | ~spl8_65),
% 1.70/0.60    inference(avatar_split_clause,[],[f1046,f1030,f1005,f1048])).
% 1.70/0.60  fof(f1005,plain,(
% 1.70/0.60    spl8_62 <=> k1_mcart_1(sK4) = sK6(sK4)),
% 1.70/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_62])])).
% 1.70/0.60  fof(f1030,plain,(
% 1.70/0.60    spl8_65 <=> sK4 = k4_tarski(sK6(sK4),k2_mcart_1(sK4))),
% 1.70/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_65])])).
% 1.70/0.60  fof(f1046,plain,(
% 1.70/0.60    sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) | (~spl8_62 | ~spl8_65)),
% 1.70/0.60    inference(forward_demodulation,[],[f1032,f1007])).
% 1.70/0.60  fof(f1007,plain,(
% 1.70/0.60    k1_mcart_1(sK4) = sK6(sK4) | ~spl8_62),
% 1.70/0.60    inference(avatar_component_clause,[],[f1005])).
% 1.70/0.60  fof(f1032,plain,(
% 1.70/0.60    sK4 = k4_tarski(sK6(sK4),k2_mcart_1(sK4)) | ~spl8_65),
% 1.70/0.60    inference(avatar_component_clause,[],[f1030])).
% 1.70/0.60  fof(f1033,plain,(
% 1.70/0.60    spl8_65 | ~spl8_41 | ~spl8_61),
% 1.70/0.60    inference(avatar_split_clause,[],[f1027,f1000,f642,f1030])).
% 1.70/0.60  fof(f642,plain,(
% 1.70/0.60    spl8_41 <=> sK4 = k4_tarski(sK6(sK4),sK7(sK4))),
% 1.70/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).
% 1.70/0.60  fof(f1000,plain,(
% 1.70/0.60    spl8_61 <=> k2_mcart_1(sK4) = sK7(sK4)),
% 1.70/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_61])])).
% 1.70/0.60  fof(f1027,plain,(
% 1.70/0.60    sK4 = k4_tarski(sK6(sK4),k2_mcart_1(sK4)) | (~spl8_41 | ~spl8_61)),
% 1.70/0.60    inference(backward_demodulation,[],[f644,f1002])).
% 1.70/0.60  fof(f1002,plain,(
% 1.70/0.60    k2_mcart_1(sK4) = sK7(sK4) | ~spl8_61),
% 1.70/0.60    inference(avatar_component_clause,[],[f1000])).
% 1.70/0.60  fof(f644,plain,(
% 1.70/0.60    sK4 = k4_tarski(sK6(sK4),sK7(sK4)) | ~spl8_41),
% 1.70/0.60    inference(avatar_component_clause,[],[f642])).
% 1.70/0.60  fof(f1008,plain,(
% 1.70/0.60    spl8_62 | ~spl8_41),
% 1.70/0.60    inference(avatar_split_clause,[],[f996,f642,f1005])).
% 1.70/0.60  fof(f996,plain,(
% 1.70/0.60    k1_mcart_1(sK4) = sK6(sK4) | ~spl8_41),
% 1.70/0.60    inference(superposition,[],[f40,f644])).
% 1.70/0.60  fof(f1003,plain,(
% 1.70/0.60    spl8_61 | ~spl8_41),
% 1.70/0.60    inference(avatar_split_clause,[],[f995,f642,f1000])).
% 1.70/0.60  fof(f995,plain,(
% 1.70/0.60    k2_mcart_1(sK4) = sK7(sK4) | ~spl8_41),
% 1.70/0.60    inference(superposition,[],[f41,f644])).
% 1.70/0.60  fof(f986,plain,(
% 1.70/0.60    spl8_34 | spl8_4 | spl8_2 | spl8_3 | ~spl8_5),
% 1.70/0.60    inference(avatar_split_clause,[],[f980,f96,f86,f81,f91,f524])).
% 1.70/0.60  fof(f524,plain,(
% 1.70/0.60    spl8_34 <=> k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)),
% 1.70/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).
% 1.70/0.60  fof(f91,plain,(
% 1.70/0.60    spl8_4 <=> k1_xboole_0 = sK0),
% 1.70/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.70/0.60  fof(f81,plain,(
% 1.70/0.60    spl8_2 <=> k1_xboole_0 = sK2),
% 1.70/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.70/0.60  fof(f86,plain,(
% 1.70/0.60    spl8_3 <=> k1_xboole_0 = sK1),
% 1.70/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.70/0.60  fof(f96,plain,(
% 1.70/0.60    spl8_5 <=> m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.70/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.70/0.60  fof(f980,plain,(
% 1.70/0.60    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) | ~spl8_5),
% 1.70/0.60    inference(resolution,[],[f61,f98])).
% 1.70/0.60  fof(f98,plain,(
% 1.70/0.60    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl8_5),
% 1.70/0.60    inference(avatar_component_clause,[],[f96])).
% 1.70/0.60  fof(f61,plain,(
% 1.70/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X0 | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)) )),
% 1.70/0.60    inference(definition_unfolding,[],[f50,f45])).
% 1.70/0.60  fof(f45,plain,(
% 1.70/0.60    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.70/0.60    inference(cnf_transformation,[],[f6])).
% 1.70/0.60  fof(f6,axiom,(
% 1.70/0.60    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.70/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.70/0.60  fof(f50,plain,(
% 1.70/0.60    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)) )),
% 1.70/0.60    inference(cnf_transformation,[],[f26])).
% 1.70/0.60  fof(f26,plain,(
% 1.70/0.60    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.70/0.60    inference(ennf_transformation,[],[f11])).
% 1.70/0.60  fof(f11,axiom,(
% 1.70/0.60    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.70/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).
% 1.70/0.60  fof(f925,plain,(
% 1.70/0.60    spl8_41 | ~spl8_6),
% 1.70/0.60    inference(avatar_split_clause,[],[f920,f104,f642])).
% 1.70/0.60  fof(f104,plain,(
% 1.70/0.60    spl8_6 <=> r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.70/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.70/0.60  fof(f920,plain,(
% 1.70/0.60    sK4 = k4_tarski(sK6(sK4),sK7(sK4)) | ~spl8_6),
% 1.70/0.60    inference(resolution,[],[f106,f51])).
% 1.70/0.60  fof(f51,plain,(
% 1.70/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | k4_tarski(sK6(X0),sK7(X0)) = X0) )),
% 1.70/0.60    inference(cnf_transformation,[],[f27])).
% 1.70/0.60  fof(f27,plain,(
% 1.70/0.60    ! [X0,X1,X2] : (? [X3,X4] : k4_tarski(X3,X4) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.70/0.60    inference(ennf_transformation,[],[f2])).
% 1.70/0.60  fof(f2,axiom,(
% 1.70/0.60    ! [X0,X1,X2] : ~(! [X3,X4] : k4_tarski(X3,X4) != X0 & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.70/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).
% 1.70/0.60  fof(f106,plain,(
% 1.70/0.60    r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl8_6),
% 1.70/0.60    inference(avatar_component_clause,[],[f104])).
% 1.70/0.60  fof(f919,plain,(
% 1.70/0.60    spl8_54 | ~spl8_23),
% 1.70/0.60    inference(avatar_split_clause,[],[f911,f340,f916])).
% 1.70/0.60  fof(f340,plain,(
% 1.70/0.60    spl8_23 <=> r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1))),
% 1.70/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 1.70/0.60  fof(f911,plain,(
% 1.70/0.60    k1_mcart_1(sK4) = k4_tarski(sK6(k1_mcart_1(sK4)),sK7(k1_mcart_1(sK4))) | ~spl8_23),
% 1.70/0.60    inference(resolution,[],[f51,f342])).
% 1.70/0.60  fof(f342,plain,(
% 1.70/0.60    r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1)) | ~spl8_23),
% 1.70/0.60    inference(avatar_component_clause,[],[f340])).
% 1.70/0.60  fof(f899,plain,(
% 1.70/0.60    spl8_52 | ~spl8_51),
% 1.70/0.60    inference(avatar_split_clause,[],[f893,f888,f896])).
% 1.70/0.60  fof(f888,plain,(
% 1.70/0.60    spl8_51 <=> r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1)),
% 1.70/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_51])])).
% 1.70/0.60  fof(f893,plain,(
% 1.70/0.60    m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) | ~spl8_51),
% 1.70/0.60    inference(resolution,[],[f890,f43])).
% 1.70/0.60  fof(f43,plain,(
% 1.70/0.60    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 1.70/0.60    inference(cnf_transformation,[],[f24])).
% 1.70/0.60  fof(f24,plain,(
% 1.70/0.60    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.70/0.60    inference(ennf_transformation,[],[f3])).
% 1.70/0.60  fof(f3,axiom,(
% 1.70/0.60    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.70/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.70/0.60  fof(f890,plain,(
% 1.70/0.60    r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1) | ~spl8_51),
% 1.70/0.60    inference(avatar_component_clause,[],[f888])).
% 1.70/0.60  fof(f891,plain,(
% 1.70/0.60    spl8_51 | ~spl8_23),
% 1.70/0.60    inference(avatar_split_clause,[],[f883,f340,f888])).
% 1.70/0.60  fof(f883,plain,(
% 1.70/0.60    r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1) | ~spl8_23),
% 1.70/0.60    inference(resolution,[],[f342,f47])).
% 1.70/0.60  fof(f47,plain,(
% 1.70/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 1.70/0.60    inference(cnf_transformation,[],[f25])).
% 1.70/0.60  fof(f25,plain,(
% 1.70/0.60    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.70/0.60    inference(ennf_transformation,[],[f8])).
% 1.70/0.60  fof(f8,axiom,(
% 1.70/0.60    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.70/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.70/0.60  fof(f877,plain,(
% 1.70/0.60    spl8_32 | ~spl8_24),
% 1.70/0.60    inference(avatar_split_clause,[],[f875,f348,f507])).
% 1.70/0.60  fof(f348,plain,(
% 1.70/0.60    spl8_24 <=> r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0)),
% 1.70/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 1.70/0.60  fof(f875,plain,(
% 1.70/0.60    m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) | ~spl8_24),
% 1.70/0.60    inference(resolution,[],[f350,f43])).
% 1.70/0.60  fof(f350,plain,(
% 1.70/0.60    r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0) | ~spl8_24),
% 1.70/0.60    inference(avatar_component_clause,[],[f348])).
% 1.70/0.60  fof(f867,plain,(
% 1.70/0.60    spl8_6 | spl8_7 | ~spl8_5),
% 1.70/0.60    inference(avatar_split_clause,[],[f866,f96,f108,f104])).
% 1.70/0.60  fof(f108,plain,(
% 1.70/0.60    spl8_7 <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.70/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 1.70/0.60  fof(f866,plain,(
% 1.70/0.60    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl8_5),
% 1.70/0.60    inference(resolution,[],[f98,f42])).
% 1.70/0.60  fof(f42,plain,(
% 1.70/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.70/0.60    inference(cnf_transformation,[],[f23])).
% 1.70/0.60  fof(f23,plain,(
% 1.70/0.60    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.70/0.60    inference(flattening,[],[f22])).
% 1.70/0.60  fof(f22,plain,(
% 1.70/0.60    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.70/0.60    inference(ennf_transformation,[],[f4])).
% 1.70/0.60  fof(f4,axiom,(
% 1.70/0.60    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.70/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.70/0.60  fof(f860,plain,(
% 1.70/0.60    spl8_49 | ~spl8_42),
% 1.70/0.60    inference(avatar_split_clause,[],[f854,f647,f857])).
% 1.70/0.60  fof(f647,plain,(
% 1.70/0.60    spl8_42 <=> r2_hidden(k2_mcart_1(sK4),sK2)),
% 1.70/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).
% 1.70/0.60  fof(f854,plain,(
% 1.70/0.60    m1_subset_1(k2_mcart_1(sK4),sK2) | ~spl8_42),
% 1.70/0.60    inference(resolution,[],[f649,f43])).
% 1.70/0.60  fof(f649,plain,(
% 1.70/0.60    r2_hidden(k2_mcart_1(sK4),sK2) | ~spl8_42),
% 1.70/0.60    inference(avatar_component_clause,[],[f647])).
% 1.70/0.60  fof(f850,plain,(
% 1.70/0.60    spl8_23 | ~spl8_6),
% 1.70/0.60    inference(avatar_split_clause,[],[f336,f104,f340])).
% 1.70/0.60  fof(f336,plain,(
% 1.70/0.60    r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1)) | ~spl8_6),
% 1.70/0.60    inference(resolution,[],[f46,f106])).
% 1.70/0.60  fof(f46,plain,(
% 1.70/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 1.70/0.60    inference(cnf_transformation,[],[f25])).
% 1.70/0.60  fof(f848,plain,(
% 1.70/0.60    spl8_42 | ~spl8_6),
% 1.70/0.60    inference(avatar_split_clause,[],[f635,f104,f647])).
% 1.70/0.60  fof(f635,plain,(
% 1.70/0.60    r2_hidden(k2_mcart_1(sK4),sK2) | ~spl8_6),
% 1.70/0.60    inference(resolution,[],[f106,f47])).
% 1.70/0.60  fof(f844,plain,(
% 1.70/0.60    spl8_24 | ~spl8_23),
% 1.70/0.60    inference(avatar_split_clause,[],[f344,f340,f348])).
% 1.70/0.60  fof(f344,plain,(
% 1.70/0.60    r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0) | ~spl8_23),
% 1.70/0.60    inference(resolution,[],[f342,f46])).
% 1.70/0.60  fof(f808,plain,(
% 1.70/0.60    spl8_4 | ~spl8_11 | ~spl8_14),
% 1.70/0.60    inference(avatar_contradiction_clause,[],[f807])).
% 1.70/0.60  fof(f807,plain,(
% 1.70/0.60    $false | (spl8_4 | ~spl8_11 | ~spl8_14)),
% 1.70/0.60    inference(trivial_inequality_removal,[],[f800])).
% 1.70/0.60  fof(f800,plain,(
% 1.70/0.60    k1_xboole_0 != k1_xboole_0 | (spl8_4 | ~spl8_11 | ~spl8_14)),
% 1.70/0.60    inference(superposition,[],[f93,f755])).
% 1.70/0.60  fof(f755,plain,(
% 1.70/0.60    ( ! [X0] : (k1_xboole_0 = X0) ) | (~spl8_11 | ~spl8_14)),
% 1.70/0.60    inference(trivial_inequality_removal,[],[f754])).
% 1.70/0.60  fof(f754,plain,(
% 1.70/0.60    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = X0) ) | (~spl8_11 | ~spl8_14)),
% 1.70/0.60    inference(superposition,[],[f244,f172])).
% 1.70/0.60  fof(f172,plain,(
% 1.70/0.60    ( ! [X4] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X4)) ) | ~spl8_11),
% 1.70/0.60    inference(forward_demodulation,[],[f160,f148])).
% 1.70/0.60  fof(f148,plain,(
% 1.70/0.60    k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) | ~spl8_11),
% 1.70/0.60    inference(avatar_component_clause,[],[f146])).
% 1.70/0.60  fof(f146,plain,(
% 1.70/0.60    spl8_11 <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),
% 1.70/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 1.70/0.60  fof(f160,plain,(
% 1.70/0.60    ( ! [X4] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),X4)) )),
% 1.70/0.60    inference(superposition,[],[f72,f71])).
% 1.70/0.60  fof(f71,plain,(
% 1.70/0.60    ( ! [X2,X0,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0)) )),
% 1.70/0.60    inference(equality_resolution,[],[f64])).
% 1.70/0.60  fof(f64,plain,(
% 1.70/0.60    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 != X3) )),
% 1.70/0.60    inference(definition_unfolding,[],[f57,f58])).
% 1.70/0.60  fof(f58,plain,(
% 1.70/0.60    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 1.70/0.60    inference(definition_unfolding,[],[f52,f45])).
% 1.70/0.60  fof(f52,plain,(
% 1.70/0.60    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 1.70/0.60    inference(cnf_transformation,[],[f7])).
% 1.70/0.60  fof(f7,axiom,(
% 1.70/0.60    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 1.70/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 1.70/0.60  fof(f57,plain,(
% 1.70/0.60    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 | k1_xboole_0 != X3) )),
% 1.70/0.60    inference(cnf_transformation,[],[f12])).
% 1.70/0.60  fof(f12,axiom,(
% 1.70/0.60    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0)),
% 1.70/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).
% 1.70/0.60  fof(f72,plain,(
% 1.70/0.60    ( ! [X0,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3)) )),
% 1.70/0.60    inference(equality_resolution,[],[f65])).
% 1.70/0.60  fof(f65,plain,(
% 1.70/0.60    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 != X2) )),
% 1.70/0.60    inference(definition_unfolding,[],[f56,f58])).
% 1.70/0.60  fof(f56,plain,(
% 1.70/0.60    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 | k1_xboole_0 != X2) )),
% 1.70/0.60    inference(cnf_transformation,[],[f12])).
% 1.70/0.60  fof(f244,plain,(
% 1.70/0.60    ( ! [X1] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X1) | k1_xboole_0 = X1) ) | ~spl8_14),
% 1.70/0.60    inference(avatar_component_clause,[],[f243])).
% 1.70/0.60  fof(f243,plain,(
% 1.70/0.60    spl8_14 <=> ! [X1] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X1) | k1_xboole_0 = X1)),
% 1.70/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 1.70/0.60  fof(f93,plain,(
% 1.70/0.60    k1_xboole_0 != sK0 | spl8_4),
% 1.70/0.60    inference(avatar_component_clause,[],[f91])).
% 1.70/0.60  fof(f749,plain,(
% 1.70/0.60    ~spl8_48 | spl8_1 | ~spl8_34),
% 1.70/0.60    inference(avatar_split_clause,[],[f744,f524,f76,f746])).
% 1.70/0.60  fof(f76,plain,(
% 1.70/0.60    spl8_1 <=> sK3 = k7_mcart_1(sK0,sK1,sK2,sK4)),
% 1.70/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.70/0.60  fof(f744,plain,(
% 1.70/0.60    sK3 != k2_mcart_1(sK4) | (spl8_1 | ~spl8_34)),
% 1.70/0.60    inference(superposition,[],[f78,f526])).
% 1.70/0.60  fof(f526,plain,(
% 1.70/0.60    k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) | ~spl8_34),
% 1.70/0.60    inference(avatar_component_clause,[],[f524])).
% 1.70/0.60  fof(f78,plain,(
% 1.70/0.60    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) | spl8_1),
% 1.70/0.60    inference(avatar_component_clause,[],[f76])).
% 1.70/0.60  fof(f741,plain,(
% 1.70/0.60    spl8_12 | spl8_2 | spl8_13 | spl8_14 | ~spl8_8 | ~spl8_11),
% 1.70/0.60    inference(avatar_split_clause,[],[f740,f146,f114,f243,f239,f81,f236])).
% 1.70/0.60  fof(f236,plain,(
% 1.70/0.60    spl8_12 <=> ! [X0] : k1_xboole_0 = X0),
% 1.70/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 1.70/0.60  fof(f239,plain,(
% 1.70/0.60    spl8_13 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 1.70/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 1.70/0.60  fof(f114,plain,(
% 1.70/0.60    spl8_8 <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 1.70/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 1.70/0.60  fof(f740,plain,(
% 1.70/0.60    ( ! [X14,X13] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X14) | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK2 | k1_xboole_0 = X13 | k1_xboole_0 = X14) ) | (~spl8_8 | ~spl8_11)),
% 1.70/0.60    inference(forward_demodulation,[],[f727,f172])).
% 1.70/0.60  fof(f727,plain,(
% 1.70/0.60    ( ! [X14,X13] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X13),X14) | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK2 | k1_xboole_0 = X13 | k1_xboole_0 = X14) ) | ~spl8_8),
% 1.70/0.60    inference(superposition,[],[f68,f116])).
% 1.70/0.60  fof(f116,plain,(
% 1.70/0.60    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl8_8),
% 1.70/0.60    inference(avatar_component_clause,[],[f114])).
% 1.70/0.60  fof(f68,plain,(
% 1.70/0.60    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3) )),
% 1.70/0.60    inference(definition_unfolding,[],[f53,f58])).
% 1.70/0.60  fof(f53,plain,(
% 1.70/0.60    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3) )),
% 1.70/0.60    inference(cnf_transformation,[],[f12])).
% 1.70/0.60  fof(f712,plain,(
% 1.70/0.60    spl8_8 | ~spl8_7),
% 1.70/0.60    inference(avatar_split_clause,[],[f711,f108,f114])).
% 1.70/0.60  fof(f711,plain,(
% 1.70/0.60    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl8_7),
% 1.70/0.60    inference(resolution,[],[f110,f101])).
% 1.70/0.60  fof(f101,plain,(
% 1.70/0.60    ( ! [X1] : (~v1_xboole_0(X1) | k1_xboole_0 = X1) )),
% 1.70/0.60    inference(resolution,[],[f39,f36])).
% 1.70/0.60  fof(f36,plain,(
% 1.70/0.60    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.70/0.60    inference(cnf_transformation,[],[f20])).
% 1.70/0.60  fof(f20,plain,(
% 1.70/0.60    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 1.70/0.60    inference(ennf_transformation,[],[f16])).
% 1.70/0.60  fof(f16,plain,(
% 1.70/0.60    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 1.70/0.60    inference(unused_predicate_definition_removal,[],[f1])).
% 1.70/0.60  fof(f1,axiom,(
% 1.70/0.60    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.70/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.70/0.60  fof(f39,plain,(
% 1.70/0.60    ( ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0) )),
% 1.70/0.60    inference(cnf_transformation,[],[f21])).
% 1.70/0.60  fof(f21,plain,(
% 1.70/0.60    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.70/0.60    inference(ennf_transformation,[],[f10])).
% 1.70/0.60  fof(f10,axiom,(
% 1.70/0.60    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.70/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).
% 1.70/0.60  fof(f110,plain,(
% 1.70/0.60    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl8_7),
% 1.70/0.60    inference(avatar_component_clause,[],[f108])).
% 1.70/0.60  fof(f700,plain,(
% 1.70/0.60    spl8_12 | spl8_3 | spl8_4 | spl8_14 | ~spl8_11 | ~spl8_13),
% 1.70/0.60    inference(avatar_split_clause,[],[f699,f239,f146,f243,f91,f86,f236])).
% 1.70/0.60  fof(f699,plain,(
% 1.70/0.60    ( ! [X10,X9] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X10) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = X9 | k1_xboole_0 = X10) ) | (~spl8_11 | ~spl8_13)),
% 1.70/0.60    inference(forward_demodulation,[],[f679,f172])).
% 1.70/0.60  fof(f679,plain,(
% 1.70/0.60    ( ! [X10,X9] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X9),X10) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = X9 | k1_xboole_0 = X10) ) | ~spl8_13),
% 1.70/0.60    inference(superposition,[],[f68,f241])).
% 1.70/0.60  fof(f241,plain,(
% 1.70/0.60    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl8_13),
% 1.70/0.60    inference(avatar_component_clause,[],[f239])).
% 1.70/0.60  fof(f293,plain,(
% 1.70/0.60    spl8_4 | ~spl8_12),
% 1.70/0.60    inference(avatar_contradiction_clause,[],[f292])).
% 1.70/0.60  fof(f292,plain,(
% 1.70/0.60    $false | (spl8_4 | ~spl8_12)),
% 1.70/0.60    inference(trivial_inequality_removal,[],[f285])).
% 1.70/0.60  fof(f285,plain,(
% 1.70/0.60    k1_xboole_0 != k1_xboole_0 | (spl8_4 | ~spl8_12)),
% 1.70/0.60    inference(superposition,[],[f93,f237])).
% 1.70/0.60  fof(f237,plain,(
% 1.70/0.60    ( ! [X0] : (k1_xboole_0 = X0) ) | ~spl8_12),
% 1.70/0.60    inference(avatar_component_clause,[],[f236])).
% 1.70/0.60  fof(f150,plain,(
% 1.70/0.60    spl8_11),
% 1.70/0.60    inference(avatar_split_clause,[],[f142,f146])).
% 1.70/0.60  fof(f142,plain,(
% 1.70/0.60    k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),
% 1.70/0.60    inference(superposition,[],[f71,f71])).
% 1.70/0.60  fof(f99,plain,(
% 1.70/0.60    spl8_5),
% 1.70/0.60    inference(avatar_split_clause,[],[f59,f96])).
% 1.70/0.60  fof(f59,plain,(
% 1.70/0.60    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.70/0.60    inference(definition_unfolding,[],[f29,f45])).
% 1.70/0.60  fof(f29,plain,(
% 1.70/0.60    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 1.70/0.60    inference(cnf_transformation,[],[f18])).
% 1.70/0.60  fof(f94,plain,(
% 1.70/0.60    ~spl8_4),
% 1.70/0.60    inference(avatar_split_clause,[],[f30,f91])).
% 1.70/0.60  fof(f30,plain,(
% 1.70/0.60    k1_xboole_0 != sK0),
% 1.70/0.60    inference(cnf_transformation,[],[f18])).
% 1.70/0.60  fof(f89,plain,(
% 1.70/0.60    ~spl8_3),
% 1.70/0.60    inference(avatar_split_clause,[],[f31,f86])).
% 1.70/0.60  fof(f31,plain,(
% 1.70/0.60    k1_xboole_0 != sK1),
% 1.70/0.60    inference(cnf_transformation,[],[f18])).
% 1.70/0.60  fof(f84,plain,(
% 1.70/0.60    ~spl8_2),
% 1.70/0.60    inference(avatar_split_clause,[],[f32,f81])).
% 1.70/0.60  fof(f32,plain,(
% 1.70/0.60    k1_xboole_0 != sK2),
% 1.70/0.60    inference(cnf_transformation,[],[f18])).
% 1.70/0.60  fof(f79,plain,(
% 1.70/0.60    ~spl8_1),
% 1.70/0.60    inference(avatar_split_clause,[],[f33,f76])).
% 1.70/0.60  fof(f33,plain,(
% 1.70/0.60    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)),
% 1.70/0.60    inference(cnf_transformation,[],[f18])).
% 1.70/0.60  % SZS output end Proof for theBenchmark
% 1.70/0.60  % (8452)------------------------------
% 1.70/0.60  % (8452)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.60  % (8452)Termination reason: Refutation
% 1.70/0.60  
% 1.70/0.60  % (8452)Memory used [KB]: 11769
% 1.70/0.60  % (8452)Time elapsed: 0.184 s
% 1.70/0.60  % (8452)------------------------------
% 1.70/0.60  % (8452)------------------------------
% 1.98/0.62  % (8433)Success in time 0.263 s
%------------------------------------------------------------------------------
