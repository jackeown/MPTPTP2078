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
% DateTime   : Thu Dec  3 12:59:32 EST 2020

% Result     : Theorem 1.63s
% Output     : Refutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :  187 ( 574 expanded)
%              Number of leaves         :   35 ( 185 expanded)
%              Depth                    :   13
%              Number of atoms          :  574 (2229 expanded)
%              Number of equality atoms :  221 (1291 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1870,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f194,f302,f364,f694,f703,f782,f865,f891,f1215,f1217,f1335,f1365,f1582,f1658,f1686,f1784,f1806,f1810,f1869])).

fof(f1869,plain,
    ( spl8_14
    | spl8_58 ),
    inference(avatar_contradiction_clause,[],[f1866])).

fof(f1866,plain,
    ( $false
    | spl8_14
    | spl8_58 ),
    inference(resolution,[],[f1863,f1656])).

fof(f1656,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | spl8_58 ),
    inference(avatar_component_clause,[],[f1655])).

fof(f1655,plain,
    ( spl8_58
  <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_58])])).

fof(f1863,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | spl8_14 ),
    inference(resolution,[],[f1842,f70])).

fof(f70,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f38,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f38,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK3 = X7
                | k3_mcart_1(X5,X6,X7) != sK4
                | ~ m1_subset_1(X7,sK2) )
            | ~ m1_subset_1(X6,sK1) )
        | ~ m1_subset_1(X5,sK0) )
    & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f18,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2,X3,X4] :
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
        & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) )
   => ( sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK3 = X7
                  | k3_mcart_1(X5,X6,X7) != sK4
                  | ~ m1_subset_1(X7,sK2) )
              | ~ m1_subset_1(X6,sK1) )
          | ~ m1_subset_1(X5,sK0) )
      & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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

fof(f1842,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(X3,sK2))
        | v1_xboole_0(k2_zfmisc_1(X3,sK2)) )
    | spl8_14 ),
    inference(resolution,[],[f1826,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f1826,plain,
    ( ! [X0] : ~ r2_hidden(sK4,k2_zfmisc_1(X0,sK2))
    | spl8_14 ),
    inference(resolution,[],[f272,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f272,plain,
    ( ~ r2_hidden(k2_mcart_1(sK4),sK2)
    | spl8_14 ),
    inference(resolution,[],[f266,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f266,plain,
    ( ~ m1_subset_1(k2_mcart_1(sK4),sK2)
    | spl8_14 ),
    inference(avatar_component_clause,[],[f264])).

fof(f264,plain,
    ( spl8_14
  <=> m1_subset_1(k2_mcart_1(sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f1810,plain,
    ( spl8_10
    | ~ spl8_9
    | ~ spl8_8
    | ~ spl8_3
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f1627,f362,f168,f216,f220,f224])).

fof(f224,plain,
    ( spl8_10
  <=> ! [X5,X6] : ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X5,X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f220,plain,
    ( spl8_9
  <=> r2_hidden(sK7(k1_mcart_1(sK4)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f216,plain,
    ( spl8_8
  <=> r2_hidden(sK6(k1_mcart_1(sK4)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f168,plain,
    ( spl8_3
  <=> sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f362,plain,
    ( spl8_26
  <=> ! [X3,X5,X4] :
        ( sK4 != k4_tarski(X3,k2_mcart_1(sK4))
        | ~ r2_hidden(sK6(X3),sK0)
        | ~ r2_hidden(sK7(X3),sK1)
        | ~ r2_hidden(X3,k2_zfmisc_1(X4,X5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f1627,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK6(k1_mcart_1(sK4)),sK0)
        | ~ r2_hidden(sK7(k1_mcart_1(sK4)),sK1)
        | ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,X1)) )
    | ~ spl8_3
    | ~ spl8_26 ),
    inference(trivial_inequality_removal,[],[f1626])).

fof(f1626,plain,
    ( ! [X0,X1] :
        ( sK4 != sK4
        | ~ r2_hidden(sK6(k1_mcart_1(sK4)),sK0)
        | ~ r2_hidden(sK7(k1_mcart_1(sK4)),sK1)
        | ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,X1)) )
    | ~ spl8_3
    | ~ spl8_26 ),
    inference(superposition,[],[f363,f170])).

fof(f170,plain,
    ( sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f168])).

fof(f363,plain,
    ( ! [X4,X5,X3] :
        ( sK4 != k4_tarski(X3,k2_mcart_1(sK4))
        | ~ r2_hidden(sK6(X3),sK0)
        | ~ r2_hidden(sK7(X3),sK1)
        | ~ r2_hidden(X3,k2_zfmisc_1(X4,X5)) )
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f362])).

fof(f1806,plain,
    ( ~ spl8_22
    | ~ spl8_57
    | spl8_58 ),
    inference(avatar_contradiction_clause,[],[f1805])).

fof(f1805,plain,
    ( $false
    | ~ spl8_22
    | ~ spl8_57
    | spl8_58 ),
    inference(resolution,[],[f1800,f321])).

fof(f321,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f319])).

fof(f319,plain,
    ( spl8_22
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f1800,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl8_57
    | spl8_58 ),
    inference(forward_demodulation,[],[f1798,f104])).

fof(f104,plain,(
    ! [X3] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X3) ),
    inference(forward_demodulation,[],[f95,f90])).

fof(f90,plain,(
    k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f81,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X3
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f67,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f62,f55])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X3
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

fof(f95,plain,(
    ! [X3] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),X3) ),
    inference(superposition,[],[f82,f81])).

fof(f82,plain,(
    ! [X0,X3,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f66,f68])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1798,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK2))
    | ~ spl8_57
    | spl8_58 ),
    inference(backward_demodulation,[],[f1656,f1676])).

fof(f1676,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl8_57 ),
    inference(resolution,[],[f1664,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f1664,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl8_57 ),
    inference(resolution,[],[f1653,f48])).

fof(f48,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK5(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f1653,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
    | ~ spl8_57 ),
    inference(avatar_component_clause,[],[f1652])).

fof(f1652,plain,
    ( spl8_57
  <=> ! [X0] : ~ r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_57])])).

fof(f1784,plain,
    ( spl8_27
    | spl8_28
    | spl8_2
    | spl8_12
    | ~ spl8_58 ),
    inference(avatar_split_clause,[],[f1779,f1655,f249,f164,f687,f683])).

fof(f683,plain,
    ( spl8_27
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f687,plain,
    ( spl8_28
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f164,plain,
    ( spl8_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f249,plain,
    ( spl8_12
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f1779,plain,
    ( ! [X3] :
        ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = sK2
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0 )
    | ~ spl8_58 ),
    inference(superposition,[],[f78,f1698])).

fof(f1698,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl8_58 ),
    inference(resolution,[],[f1657,f44])).

fof(f1657,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl8_58 ),
    inference(avatar_component_clause,[],[f1655])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f63,f68])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1686,plain,
    ( spl8_22
    | ~ spl8_57 ),
    inference(avatar_contradiction_clause,[],[f1683])).

fof(f1683,plain,
    ( $false
    | spl8_22
    | ~ spl8_57 ),
    inference(resolution,[],[f1678,f320])).

fof(f320,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl8_22 ),
    inference(avatar_component_clause,[],[f319])).

fof(f1678,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl8_57 ),
    inference(backward_demodulation,[],[f1664,f1676])).

fof(f1658,plain,
    ( spl8_57
    | spl8_58
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f1647,f780,f1655,f1652])).

fof(f780,plain,
    ( spl8_30
  <=> ! [X0] :
        ( ~ m1_subset_1(k1_mcart_1(sK4),k2_zfmisc_1(sK0,X0))
        | v1_xboole_0(k2_zfmisc_1(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f1647,plain,
    ( ! [X0] :
        ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
        | ~ r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) )
    | ~ spl8_30 ),
    inference(resolution,[],[f1636,f70])).

fof(f1636,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X1),X2))
        | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,X1),X2))
        | ~ r2_hidden(X0,k2_zfmisc_1(sK0,X1)) )
    | ~ spl8_30 ),
    inference(resolution,[],[f1632,f51])).

fof(f1632,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1))
        | ~ r2_hidden(X2,k2_zfmisc_1(sK0,X0)) )
    | ~ spl8_30 ),
    inference(resolution,[],[f1629,f47])).

fof(f47,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1629,plain,
    ( ! [X2,X1] :
        ( v1_xboole_0(k2_zfmisc_1(sK0,X1))
        | ~ r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X1),X2)) )
    | ~ spl8_30 ),
    inference(resolution,[],[f56,f1607])).

fof(f1607,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,X0))
        | v1_xboole_0(k2_zfmisc_1(sK0,X0)) )
    | ~ spl8_30 ),
    inference(resolution,[],[f781,f52])).

fof(f781,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_mcart_1(sK4),k2_zfmisc_1(sK0,X0))
        | v1_xboole_0(k2_zfmisc_1(sK0,X0)) )
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f780])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1582,plain,(
    ~ spl8_12 ),
    inference(avatar_contradiction_clause,[],[f1581])).

fof(f1581,plain,
    ( $false
    | ~ spl8_12 ),
    inference(trivial_inequality_removal,[],[f1568])).

fof(f1568,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl8_12 ),
    inference(superposition,[],[f40,f403])).

fof(f403,plain,
    ( ! [X0] : k1_xboole_0 = X0
    | ~ spl8_12 ),
    inference(trivial_inequality_removal,[],[f402])).

fof(f402,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | k1_xboole_0 = X0 )
    | ~ spl8_12 ),
    inference(superposition,[],[f250,f104])).

fof(f250,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0)
        | k1_xboole_0 = X0 )
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f249])).

fof(f40,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f29])).

fof(f1365,plain,(
    ~ spl8_28 ),
    inference(avatar_contradiction_clause,[],[f1364])).

fof(f1364,plain,
    ( $false
    | ~ spl8_28 ),
    inference(trivial_inequality_removal,[],[f1363])).

fof(f1363,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl8_28 ),
    inference(superposition,[],[f41,f689])).

fof(f689,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f687])).

fof(f41,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f29])).

fof(f1335,plain,
    ( spl8_27
    | spl8_28
    | spl8_12
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f1334,f160,f249,f687,f683])).

fof(f160,plain,
    ( spl8_1
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f1334,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0)
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0 )
    | ~ spl8_1 ),
    inference(condensation,[],[f1333])).

fof(f1333,plain,
    ( ! [X12,X13] :
        ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X13)
        | k1_xboole_0 = X13
        | k1_xboole_0 = X12
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0 )
    | ~ spl8_1 ),
    inference(forward_demodulation,[],[f1328,f104])).

fof(f1328,plain,
    ( ! [X12,X13] :
        ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X12),X13)
        | k1_xboole_0 = X13
        | k1_xboole_0 = X12
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0 )
    | ~ spl8_1 ),
    inference(superposition,[],[f78,f162])).

fof(f162,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f160])).

% (24249)Refutation not found, incomplete strategy% (24249)------------------------------
% (24249)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (24249)Termination reason: Refutation not found, incomplete strategy

% (24249)Memory used [KB]: 1918
% (24249)Time elapsed: 0.200 s
% (24249)------------------------------
% (24249)------------------------------
fof(f1217,plain,
    ( spl8_1
    | spl8_2
    | spl8_3 ),
    inference(avatar_split_clause,[],[f872,f168,f164,f160])).

fof(f872,plain,
    ( sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(resolution,[],[f70,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_mcart_1)).

fof(f1215,plain,(
    ~ spl8_27 ),
    inference(avatar_contradiction_clause,[],[f1214])).

fof(f1214,plain,
    ( $false
    | ~ spl8_27 ),
    inference(trivial_inequality_removal,[],[f1213])).

fof(f1213,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl8_27 ),
    inference(superposition,[],[f40,f685])).

fof(f685,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f683])).

fof(f891,plain,
    ( spl8_27
    | spl8_28
    | spl8_2
    | spl8_12
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f878,f224,f249,f164,f687,f683])).

fof(f878,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0)
        | k1_xboole_0 = X0
        | k1_xboole_0 = sK2
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0 )
    | ~ spl8_10 ),
    inference(superposition,[],[f78,f874])).

fof(f874,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl8_10 ),
    inference(resolution,[],[f870,f44])).

fof(f870,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl8_10 ),
    inference(resolution,[],[f70,f793])).

fof(f793,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
        | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )
    | ~ spl8_10 ),
    inference(resolution,[],[f786,f51])).

fof(f786,plain,
    ( ! [X2,X0,X1] : ~ r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
    | ~ spl8_10 ),
    inference(resolution,[],[f225,f56])).

fof(f225,plain,
    ( ! [X6,X5] : ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X5,X6))
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f224])).

fof(f865,plain,
    ( spl8_27
    | spl8_28
    | spl8_2
    | spl8_12
    | spl8_20 ),
    inference(avatar_split_clause,[],[f859,f299,f249,f164,f687,f683])).

fof(f299,plain,
    ( spl8_20
  <=> r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f859,plain,
    ( ! [X7] :
        ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X7)
        | k1_xboole_0 = X7
        | k1_xboole_0 = sK2
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0 )
    | spl8_20 ),
    inference(superposition,[],[f78,f748])).

fof(f748,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | spl8_20 ),
    inference(resolution,[],[f734,f44])).

fof(f734,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | spl8_20 ),
    inference(resolution,[],[f730,f70])).

fof(f730,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1))
        | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1)) )
    | spl8_20 ),
    inference(resolution,[],[f726,f51])).

fof(f726,plain,
    ( ! [X0,X1] : ~ r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1))
    | spl8_20 ),
    inference(resolution,[],[f56,f332])).

fof(f332,plain,
    ( ! [X0] : ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,sK1))
    | spl8_20 ),
    inference(resolution,[],[f301,f57])).

fof(f301,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | spl8_20 ),
    inference(avatar_component_clause,[],[f299])).

fof(f782,plain,
    ( spl8_10
    | spl8_30
    | spl8_8 ),
    inference(avatar_split_clause,[],[f768,f216,f780,f224])).

fof(f768,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(k1_mcart_1(sK4),k2_zfmisc_1(sK0,X0))
        | v1_xboole_0(k2_zfmisc_1(sK0,X0))
        | ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X1,X2)) )
    | spl8_8 ),
    inference(superposition,[],[f658,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(sK6(X0),sK7(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k4_tarski(sK6(X0),sK7(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f27,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
     => k4_tarski(sK6(X0),sK7(X0)) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X0
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(f658,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k4_tarski(sK6(k1_mcart_1(sK4)),X1),k2_zfmisc_1(sK0,X0))
        | v1_xboole_0(k2_zfmisc_1(sK0,X0)) )
    | spl8_8 ),
    inference(resolution,[],[f274,f51])).

fof(f274,plain,
    ( ! [X2,X3] : ~ r2_hidden(k4_tarski(sK6(k1_mcart_1(sK4)),X2),k2_zfmisc_1(sK0,X3))
    | spl8_8 ),
    inference(resolution,[],[f218,f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(superposition,[],[f56,f49])).

fof(f49,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f218,plain,
    ( ~ r2_hidden(sK6(k1_mcart_1(sK4)),sK0)
    | spl8_8 ),
    inference(avatar_component_clause,[],[f216])).

fof(f703,plain,(
    spl8_29 ),
    inference(avatar_contradiction_clause,[],[f701])).

fof(f701,plain,
    ( $false
    | spl8_29 ),
    inference(resolution,[],[f693,f70])).

fof(f693,plain,
    ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | spl8_29 ),
    inference(avatar_component_clause,[],[f691])).

fof(f691,plain,
    ( spl8_29
  <=> m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f694,plain,
    ( spl8_27
    | spl8_28
    | spl8_2
    | ~ spl8_29
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f303,f227,f691,f164,f687,f683])).

fof(f227,plain,
    ( spl8_11
  <=> sK3 = k2_mcart_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f303,plain,
    ( sK3 != k2_mcart_1(sK4)
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f43,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f60,f55])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f43,plain,(
    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f29])).

fof(f364,plain,
    ( spl8_11
    | spl8_26
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f356,f264,f362,f227])).

fof(f356,plain,
    ( ! [X4,X5,X3] :
        ( sK4 != k4_tarski(X3,k2_mcart_1(sK4))
        | sK3 = k2_mcart_1(sK4)
        | ~ r2_hidden(X3,k2_zfmisc_1(X4,X5))
        | ~ r2_hidden(sK7(X3),sK1)
        | ~ r2_hidden(sK6(X3),sK0) )
    | ~ spl8_14 ),
    inference(resolution,[],[f265,f141])).

fof(f141,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,sK2)
      | sK4 != k4_tarski(X1,X0)
      | sK3 = X0
      | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(sK7(X1),sK1)
      | ~ r2_hidden(sK6(X1),sK0) ) ),
    inference(resolution,[],[f140,f52])).

fof(f140,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK6(X1),sK0)
      | ~ m1_subset_1(X0,sK2)
      | sK4 != k4_tarski(X1,X0)
      | sK3 = X0
      | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(sK7(X1),sK1) ) ),
    inference(resolution,[],[f135,f52])).

fof(f135,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK7(X0),sK1)
      | sK3 = X1
      | ~ m1_subset_1(X1,sK2)
      | k4_tarski(X0,X1) != sK4
      | ~ m1_subset_1(sK6(X0),sK0)
      | ~ r2_hidden(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(superposition,[],[f69,f61])).

fof(f69,plain,(
    ! [X6,X7,X5] :
      ( sK4 != k4_tarski(k4_tarski(X5,X6),X7)
      | sK3 = X7
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(definition_unfolding,[],[f39,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f39,plain,(
    ! [X6,X7,X5] :
      ( sK3 = X7
      | k3_mcart_1(X5,X6,X7) != sK4
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f265,plain,
    ( m1_subset_1(k2_mcart_1(sK4),sK2)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f264])).

fof(f302,plain,
    ( spl8_10
    | ~ spl8_20
    | spl8_9 ),
    inference(avatar_split_clause,[],[f288,f220,f299,f224])).

fof(f288,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1)
        | ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,X1)) )
    | spl8_9 ),
    inference(superposition,[],[f222,f136])).

fof(f136,plain,(
    ! [X6,X4,X5] :
      ( sK7(X4) = k2_mcart_1(X4)
      | ~ r2_hidden(X4,k2_zfmisc_1(X5,X6)) ) ),
    inference(superposition,[],[f50,f61])).

fof(f50,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f14])).

fof(f222,plain,
    ( ~ r2_hidden(sK7(k1_mcart_1(sK4)),sK1)
    | spl8_9 ),
    inference(avatar_component_clause,[],[f220])).

fof(f194,plain,(
    ~ spl8_2 ),
    inference(avatar_contradiction_clause,[],[f193])).

fof(f193,plain,
    ( $false
    | ~ spl8_2 ),
    inference(trivial_inequality_removal,[],[f192])).

fof(f192,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl8_2 ),
    inference(superposition,[],[f42,f166])).

fof(f166,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f164])).

fof(f42,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:25:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (24232)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (24230)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (24239)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (24240)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (24231)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (24233)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (24248)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (24247)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (24251)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (24229)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (24227)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (24243)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (24228)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (24227)Refutation not found, incomplete strategy% (24227)------------------------------
% 0.21/0.53  % (24227)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (24227)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (24227)Memory used [KB]: 1791
% 0.21/0.53  % (24227)Time elapsed: 0.124 s
% 0.21/0.53  % (24227)------------------------------
% 0.21/0.53  % (24227)------------------------------
% 0.21/0.53  % (24242)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (24251)Refutation not found, incomplete strategy% (24251)------------------------------
% 0.21/0.53  % (24251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (24251)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (24251)Memory used [KB]: 1791
% 0.21/0.53  % (24251)Time elapsed: 0.088 s
% 0.21/0.53  % (24251)------------------------------
% 0.21/0.53  % (24251)------------------------------
% 0.21/0.53  % (24253)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (24234)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (24254)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (24252)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (24248)Refutation not found, incomplete strategy% (24248)------------------------------
% 0.21/0.54  % (24248)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24248)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (24248)Memory used [KB]: 10746
% 0.21/0.54  % (24248)Time elapsed: 0.129 s
% 0.21/0.54  % (24248)------------------------------
% 0.21/0.54  % (24248)------------------------------
% 0.21/0.54  % (24257)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (24237)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (24246)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (24250)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.55  % (24244)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (24256)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (24249)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (24245)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (24238)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (24235)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (24238)Refutation not found, incomplete strategy% (24238)------------------------------
% 0.21/0.55  % (24238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (24238)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (24238)Memory used [KB]: 10618
% 0.21/0.55  % (24238)Time elapsed: 0.151 s
% 0.21/0.55  % (24238)------------------------------
% 0.21/0.55  % (24238)------------------------------
% 0.21/0.55  % (24241)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (24255)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.63/0.57  % (24245)Refutation not found, incomplete strategy% (24245)------------------------------
% 1.63/0.57  % (24245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.57  % (24245)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.57  
% 1.63/0.57  % (24245)Memory used [KB]: 10618
% 1.63/0.57  % (24245)Time elapsed: 0.157 s
% 1.63/0.57  % (24245)------------------------------
% 1.63/0.57  % (24245)------------------------------
% 1.63/0.58  % (24240)Refutation found. Thanks to Tanya!
% 1.63/0.58  % SZS status Theorem for theBenchmark
% 1.82/0.60  % SZS output start Proof for theBenchmark
% 1.82/0.60  fof(f1870,plain,(
% 1.82/0.60    $false),
% 1.82/0.60    inference(avatar_sat_refutation,[],[f194,f302,f364,f694,f703,f782,f865,f891,f1215,f1217,f1335,f1365,f1582,f1658,f1686,f1784,f1806,f1810,f1869])).
% 1.82/0.60  fof(f1869,plain,(
% 1.82/0.60    spl8_14 | spl8_58),
% 1.82/0.60    inference(avatar_contradiction_clause,[],[f1866])).
% 1.82/0.60  fof(f1866,plain,(
% 1.82/0.60    $false | (spl8_14 | spl8_58)),
% 1.82/0.60    inference(resolution,[],[f1863,f1656])).
% 1.82/0.60  fof(f1656,plain,(
% 1.82/0.60    ~v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | spl8_58),
% 1.82/0.60    inference(avatar_component_clause,[],[f1655])).
% 1.82/0.60  fof(f1655,plain,(
% 1.82/0.60    spl8_58 <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.82/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_58])])).
% 1.82/0.60  fof(f1863,plain,(
% 1.82/0.60    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | spl8_14),
% 1.82/0.60    inference(resolution,[],[f1842,f70])).
% 1.82/0.60  fof(f70,plain,(
% 1.82/0.60    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.82/0.60    inference(definition_unfolding,[],[f38,f55])).
% 1.82/0.60  fof(f55,plain,(
% 1.82/0.60    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f7])).
% 1.82/0.60  fof(f7,axiom,(
% 1.82/0.60    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.82/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.82/0.60  fof(f38,plain,(
% 1.82/0.60    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 1.82/0.60    inference(cnf_transformation,[],[f29])).
% 1.82/0.60  fof(f29,plain,(
% 1.82/0.60    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 1.82/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f18,f28])).
% 1.82/0.60  fof(f28,plain,(
% 1.82/0.60    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)))),
% 1.82/0.60    introduced(choice_axiom,[])).
% 1.82/0.60  fof(f18,plain,(
% 1.82/0.60    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 1.82/0.60    inference(flattening,[],[f17])).
% 1.82/0.60  fof(f17,plain,(
% 1.82/0.60    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 1.82/0.60    inference(ennf_transformation,[],[f16])).
% 1.82/0.60  fof(f16,negated_conjecture,(
% 1.82/0.60    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.82/0.60    inference(negated_conjecture,[],[f15])).
% 1.82/0.60  fof(f15,conjecture,(
% 1.82/0.60    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.82/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).
% 1.82/0.60  fof(f1842,plain,(
% 1.82/0.60    ( ! [X3] : (~m1_subset_1(sK4,k2_zfmisc_1(X3,sK2)) | v1_xboole_0(k2_zfmisc_1(X3,sK2))) ) | spl8_14),
% 1.82/0.60    inference(resolution,[],[f1826,f51])).
% 1.82/0.60  fof(f51,plain,(
% 1.82/0.60    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f22])).
% 1.82/0.60  fof(f22,plain,(
% 1.82/0.60    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.82/0.60    inference(flattening,[],[f21])).
% 1.82/0.60  fof(f21,plain,(
% 1.82/0.60    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.82/0.60    inference(ennf_transformation,[],[f5])).
% 1.82/0.60  fof(f5,axiom,(
% 1.82/0.60    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.82/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.82/0.60  fof(f1826,plain,(
% 1.82/0.60    ( ! [X0] : (~r2_hidden(sK4,k2_zfmisc_1(X0,sK2))) ) | spl8_14),
% 1.82/0.60    inference(resolution,[],[f272,f57])).
% 1.82/0.60  fof(f57,plain,(
% 1.82/0.60    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 1.82/0.60    inference(cnf_transformation,[],[f25])).
% 1.82/0.60  fof(f25,plain,(
% 1.82/0.60    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.82/0.60    inference(ennf_transformation,[],[f9])).
% 1.82/0.60  fof(f9,axiom,(
% 1.82/0.60    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.82/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.82/0.60  fof(f272,plain,(
% 1.82/0.60    ~r2_hidden(k2_mcart_1(sK4),sK2) | spl8_14),
% 1.82/0.60    inference(resolution,[],[f266,f52])).
% 1.82/0.60  fof(f52,plain,(
% 1.82/0.60    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f23])).
% 1.82/0.60  fof(f23,plain,(
% 1.82/0.60    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.82/0.60    inference(ennf_transformation,[],[f4])).
% 1.82/0.60  fof(f4,axiom,(
% 1.82/0.60    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.82/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.82/0.60  fof(f266,plain,(
% 1.82/0.60    ~m1_subset_1(k2_mcart_1(sK4),sK2) | spl8_14),
% 1.82/0.60    inference(avatar_component_clause,[],[f264])).
% 1.82/0.60  fof(f264,plain,(
% 1.82/0.60    spl8_14 <=> m1_subset_1(k2_mcart_1(sK4),sK2)),
% 1.82/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 1.82/0.60  fof(f1810,plain,(
% 1.82/0.60    spl8_10 | ~spl8_9 | ~spl8_8 | ~spl8_3 | ~spl8_26),
% 1.82/0.60    inference(avatar_split_clause,[],[f1627,f362,f168,f216,f220,f224])).
% 1.82/0.60  fof(f224,plain,(
% 1.82/0.60    spl8_10 <=> ! [X5,X6] : ~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X5,X6))),
% 1.82/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 1.82/0.60  fof(f220,plain,(
% 1.82/0.60    spl8_9 <=> r2_hidden(sK7(k1_mcart_1(sK4)),sK1)),
% 1.82/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 1.82/0.60  fof(f216,plain,(
% 1.82/0.60    spl8_8 <=> r2_hidden(sK6(k1_mcart_1(sK4)),sK0)),
% 1.82/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 1.82/0.60  fof(f168,plain,(
% 1.82/0.60    spl8_3 <=> sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))),
% 1.82/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.82/0.60  fof(f362,plain,(
% 1.82/0.60    spl8_26 <=> ! [X3,X5,X4] : (sK4 != k4_tarski(X3,k2_mcart_1(sK4)) | ~r2_hidden(sK6(X3),sK0) | ~r2_hidden(sK7(X3),sK1) | ~r2_hidden(X3,k2_zfmisc_1(X4,X5)))),
% 1.82/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).
% 1.82/0.60  fof(f1627,plain,(
% 1.82/0.60    ( ! [X0,X1] : (~r2_hidden(sK6(k1_mcart_1(sK4)),sK0) | ~r2_hidden(sK7(k1_mcart_1(sK4)),sK1) | ~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,X1))) ) | (~spl8_3 | ~spl8_26)),
% 1.82/0.60    inference(trivial_inequality_removal,[],[f1626])).
% 1.82/0.60  fof(f1626,plain,(
% 1.82/0.60    ( ! [X0,X1] : (sK4 != sK4 | ~r2_hidden(sK6(k1_mcart_1(sK4)),sK0) | ~r2_hidden(sK7(k1_mcart_1(sK4)),sK1) | ~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,X1))) ) | (~spl8_3 | ~spl8_26)),
% 1.82/0.60    inference(superposition,[],[f363,f170])).
% 1.82/0.60  fof(f170,plain,(
% 1.82/0.60    sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) | ~spl8_3),
% 1.82/0.60    inference(avatar_component_clause,[],[f168])).
% 1.82/0.60  fof(f363,plain,(
% 1.82/0.60    ( ! [X4,X5,X3] : (sK4 != k4_tarski(X3,k2_mcart_1(sK4)) | ~r2_hidden(sK6(X3),sK0) | ~r2_hidden(sK7(X3),sK1) | ~r2_hidden(X3,k2_zfmisc_1(X4,X5))) ) | ~spl8_26),
% 1.82/0.60    inference(avatar_component_clause,[],[f362])).
% 1.82/0.60  fof(f1806,plain,(
% 1.82/0.60    ~spl8_22 | ~spl8_57 | spl8_58),
% 1.82/0.60    inference(avatar_contradiction_clause,[],[f1805])).
% 1.82/0.60  fof(f1805,plain,(
% 1.82/0.60    $false | (~spl8_22 | ~spl8_57 | spl8_58)),
% 1.82/0.60    inference(resolution,[],[f1800,f321])).
% 1.82/0.60  fof(f321,plain,(
% 1.82/0.60    v1_xboole_0(k1_xboole_0) | ~spl8_22),
% 1.82/0.60    inference(avatar_component_clause,[],[f319])).
% 1.82/0.60  fof(f319,plain,(
% 1.82/0.60    spl8_22 <=> v1_xboole_0(k1_xboole_0)),
% 1.82/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 1.82/0.60  fof(f1800,plain,(
% 1.82/0.60    ~v1_xboole_0(k1_xboole_0) | (~spl8_57 | spl8_58)),
% 1.82/0.60    inference(forward_demodulation,[],[f1798,f104])).
% 1.82/0.60  fof(f104,plain,(
% 1.82/0.60    ( ! [X3] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X3)) )),
% 1.82/0.60    inference(forward_demodulation,[],[f95,f90])).
% 1.82/0.60  fof(f90,plain,(
% 1.82/0.60    k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),
% 1.82/0.60    inference(superposition,[],[f81,f81])).
% 1.82/0.60  fof(f81,plain,(
% 1.82/0.60    ( ! [X2,X0,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0)) )),
% 1.82/0.60    inference(equality_resolution,[],[f74])).
% 1.82/0.60  fof(f74,plain,(
% 1.82/0.60    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 1.82/0.60    inference(definition_unfolding,[],[f67,f68])).
% 1.82/0.60  fof(f68,plain,(
% 1.82/0.60    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 1.82/0.60    inference(definition_unfolding,[],[f62,f55])).
% 1.82/0.60  fof(f62,plain,(
% 1.82/0.60    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f8])).
% 1.82/0.60  fof(f8,axiom,(
% 1.82/0.60    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 1.82/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 1.82/0.60  fof(f67,plain,(
% 1.82/0.60    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X3 | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f37])).
% 1.82/0.60  fof(f37,plain,(
% 1.82/0.60    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.82/0.60    inference(flattening,[],[f36])).
% 1.82/0.60  fof(f36,plain,(
% 1.82/0.60    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | (k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.82/0.60    inference(nnf_transformation,[],[f13])).
% 1.82/0.60  fof(f13,axiom,(
% 1.82/0.60    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 1.82/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).
% 1.82/0.60  fof(f95,plain,(
% 1.82/0.60    ( ! [X3] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),X3)) )),
% 1.82/0.60    inference(superposition,[],[f82,f81])).
% 1.82/0.60  fof(f82,plain,(
% 1.82/0.60    ( ! [X0,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3)) )),
% 1.82/0.60    inference(equality_resolution,[],[f75])).
% 1.82/0.60  fof(f75,plain,(
% 1.82/0.60    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X2 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 1.82/0.60    inference(definition_unfolding,[],[f66,f68])).
% 1.82/0.60  fof(f66,plain,(
% 1.82/0.60    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X2 | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f37])).
% 1.82/0.60  fof(f1798,plain,(
% 1.82/0.60    ~v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK2)) | (~spl8_57 | spl8_58)),
% 1.82/0.60    inference(backward_demodulation,[],[f1656,f1676])).
% 1.82/0.60  fof(f1676,plain,(
% 1.82/0.60    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl8_57),
% 1.82/0.60    inference(resolution,[],[f1664,f44])).
% 1.82/0.60  fof(f44,plain,(
% 1.82/0.60    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.82/0.60    inference(cnf_transformation,[],[f19])).
% 1.82/0.60  fof(f19,plain,(
% 1.82/0.60    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.82/0.60    inference(ennf_transformation,[],[f2])).
% 1.82/0.60  fof(f2,axiom,(
% 1.82/0.60    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.82/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.82/0.60  fof(f1664,plain,(
% 1.82/0.60    v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | ~spl8_57),
% 1.82/0.60    inference(resolution,[],[f1653,f48])).
% 1.82/0.60  fof(f48,plain,(
% 1.82/0.60    ( ! [X0] : (r2_hidden(sK5(X0),X0) | v1_xboole_0(X0)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f33])).
% 1.82/0.60  fof(f33,plain,(
% 1.82/0.60    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK5(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.82/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f32])).
% 1.82/0.60  fof(f32,plain,(
% 1.82/0.60    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK5(X0),X0))),
% 1.82/0.60    introduced(choice_axiom,[])).
% 1.82/0.61  fof(f31,plain,(
% 1.82/0.61    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.82/0.61    inference(rectify,[],[f30])).
% 1.82/0.61  fof(f30,plain,(
% 1.82/0.61    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.82/0.61    inference(nnf_transformation,[],[f1])).
% 1.82/0.61  fof(f1,axiom,(
% 1.82/0.61    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.82/0.61  fof(f1653,plain,(
% 1.82/0.61    ( ! [X0] : (~r2_hidden(X0,k2_zfmisc_1(sK0,sK1))) ) | ~spl8_57),
% 1.82/0.61    inference(avatar_component_clause,[],[f1652])).
% 1.82/0.61  fof(f1652,plain,(
% 1.82/0.61    spl8_57 <=> ! [X0] : ~r2_hidden(X0,k2_zfmisc_1(sK0,sK1))),
% 1.82/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_57])])).
% 1.82/0.61  fof(f1784,plain,(
% 1.82/0.61    spl8_27 | spl8_28 | spl8_2 | spl8_12 | ~spl8_58),
% 1.82/0.61    inference(avatar_split_clause,[],[f1779,f1655,f249,f164,f687,f683])).
% 1.82/0.61  fof(f683,plain,(
% 1.82/0.61    spl8_27 <=> k1_xboole_0 = sK0),
% 1.82/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).
% 1.82/0.61  fof(f687,plain,(
% 1.82/0.61    spl8_28 <=> k1_xboole_0 = sK1),
% 1.82/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).
% 1.82/0.61  fof(f164,plain,(
% 1.82/0.61    spl8_2 <=> k1_xboole_0 = sK2),
% 1.82/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.82/0.61  fof(f249,plain,(
% 1.82/0.61    spl8_12 <=> ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0))),
% 1.82/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 1.82/0.61  fof(f1779,plain,(
% 1.82/0.61    ( ! [X3] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X3) | k1_xboole_0 = X3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) ) | ~spl8_58),
% 1.82/0.61    inference(superposition,[],[f78,f1698])).
% 1.82/0.61  fof(f1698,plain,(
% 1.82/0.61    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl8_58),
% 1.82/0.61    inference(resolution,[],[f1657,f44])).
% 1.82/0.61  fof(f1657,plain,(
% 1.82/0.61    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl8_58),
% 1.82/0.61    inference(avatar_component_clause,[],[f1655])).
% 1.82/0.61  fof(f78,plain,(
% 1.82/0.61    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.82/0.61    inference(definition_unfolding,[],[f63,f68])).
% 1.82/0.61  fof(f63,plain,(
% 1.82/0.61    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.82/0.61    inference(cnf_transformation,[],[f37])).
% 1.82/0.61  fof(f1686,plain,(
% 1.82/0.61    spl8_22 | ~spl8_57),
% 1.82/0.61    inference(avatar_contradiction_clause,[],[f1683])).
% 1.82/0.61  fof(f1683,plain,(
% 1.82/0.61    $false | (spl8_22 | ~spl8_57)),
% 1.82/0.61    inference(resolution,[],[f1678,f320])).
% 1.82/0.61  fof(f320,plain,(
% 1.82/0.61    ~v1_xboole_0(k1_xboole_0) | spl8_22),
% 1.82/0.61    inference(avatar_component_clause,[],[f319])).
% 1.82/0.61  fof(f1678,plain,(
% 1.82/0.61    v1_xboole_0(k1_xboole_0) | ~spl8_57),
% 1.82/0.61    inference(backward_demodulation,[],[f1664,f1676])).
% 1.82/0.61  fof(f1658,plain,(
% 1.82/0.61    spl8_57 | spl8_58 | ~spl8_30),
% 1.82/0.61    inference(avatar_split_clause,[],[f1647,f780,f1655,f1652])).
% 1.82/0.61  fof(f780,plain,(
% 1.82/0.61    spl8_30 <=> ! [X0] : (~m1_subset_1(k1_mcart_1(sK4),k2_zfmisc_1(sK0,X0)) | v1_xboole_0(k2_zfmisc_1(sK0,X0)))),
% 1.82/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).
% 1.82/0.61  fof(f1647,plain,(
% 1.82/0.61    ( ! [X0] : (v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~r2_hidden(X0,k2_zfmisc_1(sK0,sK1))) ) | ~spl8_30),
% 1.82/0.61    inference(resolution,[],[f1636,f70])).
% 1.82/0.61  fof(f1636,plain,(
% 1.82/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X1),X2)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,X1),X2)) | ~r2_hidden(X0,k2_zfmisc_1(sK0,X1))) ) | ~spl8_30),
% 1.82/0.61    inference(resolution,[],[f1632,f51])).
% 1.82/0.61  fof(f1632,plain,(
% 1.82/0.61    ( ! [X2,X0,X1] : (~r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1)) | ~r2_hidden(X2,k2_zfmisc_1(sK0,X0))) ) | ~spl8_30),
% 1.82/0.61    inference(resolution,[],[f1629,f47])).
% 1.82/0.61  fof(f47,plain,(
% 1.82/0.61    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f33])).
% 1.82/0.61  fof(f1629,plain,(
% 1.82/0.61    ( ! [X2,X1] : (v1_xboole_0(k2_zfmisc_1(sK0,X1)) | ~r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X1),X2))) ) | ~spl8_30),
% 1.82/0.61    inference(resolution,[],[f56,f1607])).
% 1.82/0.61  fof(f1607,plain,(
% 1.82/0.61    ( ! [X0] : (~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,X0)) | v1_xboole_0(k2_zfmisc_1(sK0,X0))) ) | ~spl8_30),
% 1.82/0.61    inference(resolution,[],[f781,f52])).
% 1.82/0.61  fof(f781,plain,(
% 1.82/0.61    ( ! [X0] : (~m1_subset_1(k1_mcart_1(sK4),k2_zfmisc_1(sK0,X0)) | v1_xboole_0(k2_zfmisc_1(sK0,X0))) ) | ~spl8_30),
% 1.82/0.61    inference(avatar_component_clause,[],[f780])).
% 1.82/0.61  fof(f56,plain,(
% 1.82/0.61    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 1.82/0.61    inference(cnf_transformation,[],[f25])).
% 1.82/0.61  fof(f1582,plain,(
% 1.82/0.61    ~spl8_12),
% 1.82/0.61    inference(avatar_contradiction_clause,[],[f1581])).
% 1.82/0.61  fof(f1581,plain,(
% 1.82/0.61    $false | ~spl8_12),
% 1.82/0.61    inference(trivial_inequality_removal,[],[f1568])).
% 1.82/0.61  fof(f1568,plain,(
% 1.82/0.61    k1_xboole_0 != k1_xboole_0 | ~spl8_12),
% 1.82/0.61    inference(superposition,[],[f40,f403])).
% 1.82/0.61  fof(f403,plain,(
% 1.82/0.61    ( ! [X0] : (k1_xboole_0 = X0) ) | ~spl8_12),
% 1.82/0.61    inference(trivial_inequality_removal,[],[f402])).
% 1.82/0.61  fof(f402,plain,(
% 1.82/0.61    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = X0) ) | ~spl8_12),
% 1.82/0.61    inference(superposition,[],[f250,f104])).
% 1.82/0.61  fof(f250,plain,(
% 1.82/0.61    ( ! [X0] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0) | k1_xboole_0 = X0) ) | ~spl8_12),
% 1.82/0.61    inference(avatar_component_clause,[],[f249])).
% 1.82/0.61  fof(f40,plain,(
% 1.82/0.61    k1_xboole_0 != sK0),
% 1.82/0.61    inference(cnf_transformation,[],[f29])).
% 1.82/0.61  fof(f1365,plain,(
% 1.82/0.61    ~spl8_28),
% 1.82/0.61    inference(avatar_contradiction_clause,[],[f1364])).
% 1.82/0.61  fof(f1364,plain,(
% 1.82/0.61    $false | ~spl8_28),
% 1.82/0.61    inference(trivial_inequality_removal,[],[f1363])).
% 1.82/0.61  fof(f1363,plain,(
% 1.82/0.61    k1_xboole_0 != k1_xboole_0 | ~spl8_28),
% 1.82/0.61    inference(superposition,[],[f41,f689])).
% 1.82/0.61  fof(f689,plain,(
% 1.82/0.61    k1_xboole_0 = sK1 | ~spl8_28),
% 1.82/0.61    inference(avatar_component_clause,[],[f687])).
% 1.82/0.61  fof(f41,plain,(
% 1.82/0.61    k1_xboole_0 != sK1),
% 1.82/0.61    inference(cnf_transformation,[],[f29])).
% 1.82/0.61  fof(f1335,plain,(
% 1.82/0.61    spl8_27 | spl8_28 | spl8_12 | ~spl8_1),
% 1.82/0.61    inference(avatar_split_clause,[],[f1334,f160,f249,f687,f683])).
% 1.82/0.61  fof(f160,plain,(
% 1.82/0.61    spl8_1 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 1.82/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.82/0.61  fof(f1334,plain,(
% 1.82/0.61    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) ) | ~spl8_1),
% 1.82/0.61    inference(condensation,[],[f1333])).
% 1.82/0.61  fof(f1333,plain,(
% 1.82/0.61    ( ! [X12,X13] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X13) | k1_xboole_0 = X13 | k1_xboole_0 = X12 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) ) | ~spl8_1),
% 1.82/0.61    inference(forward_demodulation,[],[f1328,f104])).
% 1.82/0.61  fof(f1328,plain,(
% 1.82/0.61    ( ! [X12,X13] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X12),X13) | k1_xboole_0 = X13 | k1_xboole_0 = X12 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) ) | ~spl8_1),
% 1.82/0.61    inference(superposition,[],[f78,f162])).
% 1.82/0.61  fof(f162,plain,(
% 1.82/0.61    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl8_1),
% 1.82/0.61    inference(avatar_component_clause,[],[f160])).
% 1.82/0.61  % (24249)Refutation not found, incomplete strategy% (24249)------------------------------
% 1.82/0.61  % (24249)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.82/0.61  % (24249)Termination reason: Refutation not found, incomplete strategy
% 1.82/0.61  
% 1.82/0.61  % (24249)Memory used [KB]: 1918
% 1.82/0.61  % (24249)Time elapsed: 0.200 s
% 1.82/0.61  % (24249)------------------------------
% 1.82/0.61  % (24249)------------------------------
% 1.82/0.61  fof(f1217,plain,(
% 1.82/0.61    spl8_1 | spl8_2 | spl8_3),
% 1.82/0.61    inference(avatar_split_clause,[],[f872,f168,f164,f160])).
% 1.82/0.61  fof(f872,plain,(
% 1.82/0.61    sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) | k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 1.82/0.61    inference(resolution,[],[f70,f53])).
% 1.82/0.61  fof(f53,plain,(
% 1.82/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k2_zfmisc_1(X0,X1)) | k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.82/0.61    inference(cnf_transformation,[],[f24])).
% 1.82/0.61  fof(f24,plain,(
% 1.82/0.61    ! [X0,X1] : (! [X2] : (k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 | ~m1_subset_1(X2,k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.82/0.61    inference(ennf_transformation,[],[f11])).
% 1.82/0.61  fof(f11,axiom,(
% 1.82/0.61    ! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_mcart_1)).
% 1.82/0.61  fof(f1215,plain,(
% 1.82/0.61    ~spl8_27),
% 1.82/0.61    inference(avatar_contradiction_clause,[],[f1214])).
% 1.82/0.61  fof(f1214,plain,(
% 1.82/0.61    $false | ~spl8_27),
% 1.82/0.61    inference(trivial_inequality_removal,[],[f1213])).
% 1.82/0.61  fof(f1213,plain,(
% 1.82/0.61    k1_xboole_0 != k1_xboole_0 | ~spl8_27),
% 1.82/0.61    inference(superposition,[],[f40,f685])).
% 1.82/0.61  fof(f685,plain,(
% 1.82/0.61    k1_xboole_0 = sK0 | ~spl8_27),
% 1.82/0.61    inference(avatar_component_clause,[],[f683])).
% 1.82/0.61  fof(f891,plain,(
% 1.82/0.61    spl8_27 | spl8_28 | spl8_2 | spl8_12 | ~spl8_10),
% 1.82/0.61    inference(avatar_split_clause,[],[f878,f224,f249,f164,f687,f683])).
% 1.82/0.61  fof(f878,plain,(
% 1.82/0.61    ( ! [X0] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0) | k1_xboole_0 = X0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) ) | ~spl8_10),
% 1.82/0.61    inference(superposition,[],[f78,f874])).
% 1.82/0.61  fof(f874,plain,(
% 1.82/0.61    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl8_10),
% 1.82/0.61    inference(resolution,[],[f870,f44])).
% 1.82/0.61  fof(f870,plain,(
% 1.82/0.61    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl8_10),
% 1.82/0.61    inference(resolution,[],[f70,f793])).
% 1.82/0.61  fof(f793,plain,(
% 1.82/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) ) | ~spl8_10),
% 1.82/0.61    inference(resolution,[],[f786,f51])).
% 1.82/0.61  fof(f786,plain,(
% 1.82/0.61    ( ! [X2,X0,X1] : (~r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) ) | ~spl8_10),
% 1.82/0.61    inference(resolution,[],[f225,f56])).
% 1.82/0.61  fof(f225,plain,(
% 1.82/0.61    ( ! [X6,X5] : (~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X5,X6))) ) | ~spl8_10),
% 1.82/0.61    inference(avatar_component_clause,[],[f224])).
% 1.82/0.61  fof(f865,plain,(
% 1.82/0.61    spl8_27 | spl8_28 | spl8_2 | spl8_12 | spl8_20),
% 1.82/0.61    inference(avatar_split_clause,[],[f859,f299,f249,f164,f687,f683])).
% 1.82/0.61  fof(f299,plain,(
% 1.82/0.61    spl8_20 <=> r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1)),
% 1.82/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 1.82/0.61  fof(f859,plain,(
% 1.82/0.61    ( ! [X7] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X7) | k1_xboole_0 = X7 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) ) | spl8_20),
% 1.82/0.61    inference(superposition,[],[f78,f748])).
% 1.82/0.61  fof(f748,plain,(
% 1.82/0.61    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | spl8_20),
% 1.82/0.61    inference(resolution,[],[f734,f44])).
% 1.82/0.61  fof(f734,plain,(
% 1.82/0.61    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | spl8_20),
% 1.82/0.61    inference(resolution,[],[f730,f70])).
% 1.82/0.61  fof(f730,plain,(
% 1.82/0.61    ( ! [X0,X1] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1))) ) | spl8_20),
% 1.82/0.61    inference(resolution,[],[f726,f51])).
% 1.82/0.61  fof(f726,plain,(
% 1.82/0.61    ( ! [X0,X1] : (~r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1))) ) | spl8_20),
% 1.82/0.61    inference(resolution,[],[f56,f332])).
% 1.82/0.61  fof(f332,plain,(
% 1.82/0.61    ( ! [X0] : (~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,sK1))) ) | spl8_20),
% 1.82/0.61    inference(resolution,[],[f301,f57])).
% 1.82/0.61  fof(f301,plain,(
% 1.82/0.61    ~r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1) | spl8_20),
% 1.82/0.61    inference(avatar_component_clause,[],[f299])).
% 1.82/0.61  fof(f782,plain,(
% 1.82/0.61    spl8_10 | spl8_30 | spl8_8),
% 1.82/0.61    inference(avatar_split_clause,[],[f768,f216,f780,f224])).
% 1.82/0.61  fof(f768,plain,(
% 1.82/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(k1_mcart_1(sK4),k2_zfmisc_1(sK0,X0)) | v1_xboole_0(k2_zfmisc_1(sK0,X0)) | ~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X1,X2))) ) | spl8_8),
% 1.82/0.61    inference(superposition,[],[f658,f61])).
% 1.82/0.61  fof(f61,plain,(
% 1.82/0.61    ( ! [X2,X0,X1] : (k4_tarski(sK6(X0),sK7(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 1.82/0.61    inference(cnf_transformation,[],[f35])).
% 1.82/0.61  fof(f35,plain,(
% 1.82/0.61    ! [X0,X1,X2] : (k4_tarski(sK6(X0),sK7(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.82/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f27,f34])).
% 1.82/0.61  fof(f34,plain,(
% 1.82/0.61    ! [X0] : (? [X3,X4] : k4_tarski(X3,X4) = X0 => k4_tarski(sK6(X0),sK7(X0)) = X0)),
% 1.82/0.61    introduced(choice_axiom,[])).
% 1.82/0.61  fof(f27,plain,(
% 1.82/0.61    ! [X0,X1,X2] : (? [X3,X4] : k4_tarski(X3,X4) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.82/0.61    inference(ennf_transformation,[],[f3])).
% 1.82/0.61  fof(f3,axiom,(
% 1.82/0.61    ! [X0,X1,X2] : ~(! [X3,X4] : k4_tarski(X3,X4) != X0 & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).
% 1.82/0.61  fof(f658,plain,(
% 1.82/0.61    ( ! [X0,X1] : (~m1_subset_1(k4_tarski(sK6(k1_mcart_1(sK4)),X1),k2_zfmisc_1(sK0,X0)) | v1_xboole_0(k2_zfmisc_1(sK0,X0))) ) | spl8_8),
% 1.82/0.61    inference(resolution,[],[f274,f51])).
% 1.82/0.61  fof(f274,plain,(
% 1.82/0.61    ( ! [X2,X3] : (~r2_hidden(k4_tarski(sK6(k1_mcart_1(sK4)),X2),k2_zfmisc_1(sK0,X3))) ) | spl8_8),
% 1.82/0.61    inference(resolution,[],[f218,f87])).
% 1.82/0.61  fof(f87,plain,(
% 1.82/0.61    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 1.82/0.61    inference(superposition,[],[f56,f49])).
% 1.82/0.61  fof(f49,plain,(
% 1.82/0.61    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 1.82/0.61    inference(cnf_transformation,[],[f14])).
% 1.82/0.61  fof(f14,axiom,(
% 1.82/0.61    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 1.82/0.61  fof(f218,plain,(
% 1.82/0.61    ~r2_hidden(sK6(k1_mcart_1(sK4)),sK0) | spl8_8),
% 1.82/0.61    inference(avatar_component_clause,[],[f216])).
% 1.82/0.61  fof(f703,plain,(
% 1.82/0.61    spl8_29),
% 1.82/0.61    inference(avatar_contradiction_clause,[],[f701])).
% 1.82/0.61  fof(f701,plain,(
% 1.82/0.61    $false | spl8_29),
% 1.82/0.61    inference(resolution,[],[f693,f70])).
% 1.82/0.61  fof(f693,plain,(
% 1.82/0.61    ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | spl8_29),
% 1.82/0.61    inference(avatar_component_clause,[],[f691])).
% 1.82/0.61  fof(f691,plain,(
% 1.82/0.61    spl8_29 <=> m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.82/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).
% 1.82/0.61  fof(f694,plain,(
% 1.82/0.61    spl8_27 | spl8_28 | spl8_2 | ~spl8_29 | ~spl8_11),
% 1.82/0.61    inference(avatar_split_clause,[],[f303,f227,f691,f164,f687,f683])).
% 1.82/0.61  fof(f227,plain,(
% 1.82/0.61    spl8_11 <=> sK3 = k2_mcart_1(sK4)),
% 1.82/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 1.82/0.61  fof(f303,plain,(
% 1.82/0.61    sK3 != k2_mcart_1(sK4) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.82/0.61    inference(superposition,[],[f43,f71])).
% 1.82/0.61  fof(f71,plain,(
% 1.82/0.61    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.82/0.61    inference(definition_unfolding,[],[f60,f55])).
% 1.82/0.61  fof(f60,plain,(
% 1.82/0.61    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.82/0.61    inference(cnf_transformation,[],[f26])).
% 1.82/0.61  fof(f26,plain,(
% 1.82/0.61    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.82/0.61    inference(ennf_transformation,[],[f12])).
% 1.82/0.61  fof(f12,axiom,(
% 1.82/0.61    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).
% 1.82/0.61  fof(f43,plain,(
% 1.82/0.61    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)),
% 1.82/0.61    inference(cnf_transformation,[],[f29])).
% 1.82/0.61  fof(f364,plain,(
% 1.82/0.61    spl8_11 | spl8_26 | ~spl8_14),
% 1.82/0.61    inference(avatar_split_clause,[],[f356,f264,f362,f227])).
% 1.82/0.61  fof(f356,plain,(
% 1.82/0.61    ( ! [X4,X5,X3] : (sK4 != k4_tarski(X3,k2_mcart_1(sK4)) | sK3 = k2_mcart_1(sK4) | ~r2_hidden(X3,k2_zfmisc_1(X4,X5)) | ~r2_hidden(sK7(X3),sK1) | ~r2_hidden(sK6(X3),sK0)) ) | ~spl8_14),
% 1.82/0.61    inference(resolution,[],[f265,f141])).
% 1.82/0.61  fof(f141,plain,(
% 1.82/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,sK2) | sK4 != k4_tarski(X1,X0) | sK3 = X0 | ~r2_hidden(X1,k2_zfmisc_1(X2,X3)) | ~r2_hidden(sK7(X1),sK1) | ~r2_hidden(sK6(X1),sK0)) )),
% 1.82/0.61    inference(resolution,[],[f140,f52])).
% 1.82/0.61  fof(f140,plain,(
% 1.82/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK6(X1),sK0) | ~m1_subset_1(X0,sK2) | sK4 != k4_tarski(X1,X0) | sK3 = X0 | ~r2_hidden(X1,k2_zfmisc_1(X2,X3)) | ~r2_hidden(sK7(X1),sK1)) )),
% 1.82/0.61    inference(resolution,[],[f135,f52])).
% 1.82/0.61  fof(f135,plain,(
% 1.82/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK7(X0),sK1) | sK3 = X1 | ~m1_subset_1(X1,sK2) | k4_tarski(X0,X1) != sK4 | ~m1_subset_1(sK6(X0),sK0) | ~r2_hidden(X0,k2_zfmisc_1(X2,X3))) )),
% 1.82/0.61    inference(superposition,[],[f69,f61])).
% 1.82/0.61  fof(f69,plain,(
% 1.82/0.61    ( ! [X6,X7,X5] : (sK4 != k4_tarski(k4_tarski(X5,X6),X7) | sK3 = X7 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 1.82/0.61    inference(definition_unfolding,[],[f39,f54])).
% 1.82/0.61  fof(f54,plain,(
% 1.82/0.61    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f6])).
% 1.82/0.61  fof(f6,axiom,(
% 1.82/0.61    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 1.82/0.61  fof(f39,plain,(
% 1.82/0.61    ( ! [X6,X7,X5] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f29])).
% 1.82/0.61  fof(f265,plain,(
% 1.82/0.61    m1_subset_1(k2_mcart_1(sK4),sK2) | ~spl8_14),
% 1.82/0.61    inference(avatar_component_clause,[],[f264])).
% 1.82/0.61  fof(f302,plain,(
% 1.82/0.61    spl8_10 | ~spl8_20 | spl8_9),
% 1.82/0.61    inference(avatar_split_clause,[],[f288,f220,f299,f224])).
% 1.82/0.61  fof(f288,plain,(
% 1.82/0.61    ( ! [X0,X1] : (~r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1) | ~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,X1))) ) | spl8_9),
% 1.82/0.61    inference(superposition,[],[f222,f136])).
% 1.82/0.61  fof(f136,plain,(
% 1.82/0.61    ( ! [X6,X4,X5] : (sK7(X4) = k2_mcart_1(X4) | ~r2_hidden(X4,k2_zfmisc_1(X5,X6))) )),
% 1.82/0.61    inference(superposition,[],[f50,f61])).
% 1.82/0.61  fof(f50,plain,(
% 1.82/0.61    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 1.82/0.61    inference(cnf_transformation,[],[f14])).
% 1.82/0.61  fof(f222,plain,(
% 1.82/0.61    ~r2_hidden(sK7(k1_mcart_1(sK4)),sK1) | spl8_9),
% 1.82/0.61    inference(avatar_component_clause,[],[f220])).
% 1.82/0.61  fof(f194,plain,(
% 1.82/0.61    ~spl8_2),
% 1.82/0.61    inference(avatar_contradiction_clause,[],[f193])).
% 1.82/0.61  fof(f193,plain,(
% 1.82/0.61    $false | ~spl8_2),
% 1.82/0.61    inference(trivial_inequality_removal,[],[f192])).
% 1.82/0.61  fof(f192,plain,(
% 1.82/0.61    k1_xboole_0 != k1_xboole_0 | ~spl8_2),
% 1.82/0.61    inference(superposition,[],[f42,f166])).
% 1.82/0.61  fof(f166,plain,(
% 1.82/0.61    k1_xboole_0 = sK2 | ~spl8_2),
% 1.82/0.61    inference(avatar_component_clause,[],[f164])).
% 1.82/0.61  fof(f42,plain,(
% 1.82/0.61    k1_xboole_0 != sK2),
% 1.82/0.61    inference(cnf_transformation,[],[f29])).
% 1.82/0.61  % SZS output end Proof for theBenchmark
% 1.82/0.61  % (24240)------------------------------
% 1.82/0.61  % (24240)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.82/0.61  % (24240)Termination reason: Refutation
% 1.82/0.61  
% 1.82/0.61  % (24240)Memory used [KB]: 6780
% 1.82/0.61  % (24240)Time elapsed: 0.158 s
% 1.82/0.61  % (24240)------------------------------
% 1.82/0.61  % (24240)------------------------------
% 1.82/0.61  % (24224)Success in time 0.252 s
%------------------------------------------------------------------------------
