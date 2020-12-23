%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:30 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  186 ( 402 expanded)
%              Number of leaves         :   39 ( 143 expanded)
%              Depth                    :   10
%              Number of atoms          :  644 (1827 expanded)
%              Number of equality atoms :  195 ( 747 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f986,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f172,f174,f275,f278,f340,f378,f433,f510,f522,f534,f560,f588,f600,f773,f798,f806,f819,f827,f916,f985])).

fof(f985,plain,
    ( spl8_8
    | spl8_27
    | ~ spl8_31 ),
    inference(avatar_split_clause,[],[f981,f804,f770,f264])).

fof(f264,plain,
    ( spl8_8
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f770,plain,
    ( spl8_27
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f804,plain,
    ( spl8_31
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(X0,X1))
        | k1_xboole_0 = X0
        | k1_xboole_0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f981,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK2
    | ~ spl8_31 ),
    inference(resolution,[],[f805,f74])).

fof(f74,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f42,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f42,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f18,f29])).

fof(f29,plain,
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_mcart_1)).

fof(f805,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(X0,X1))
        | k1_xboole_0 = X0
        | k1_xboole_0 = X1 )
    | ~ spl8_31 ),
    inference(avatar_component_clause,[],[f804])).

fof(f916,plain,
    ( spl8_20
    | spl8_23 ),
    inference(avatar_contradiction_clause,[],[f908])).

fof(f908,plain,
    ( $false
    | spl8_20
    | spl8_23 ),
    inference(resolution,[],[f901,f705])).

fof(f705,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | spl8_23 ),
    inference(avatar_component_clause,[],[f704])).

fof(f704,plain,
    ( spl8_23
  <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f901,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | spl8_20 ),
    inference(resolution,[],[f840,f74])).

fof(f840,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X3,sK1),X4))
        | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X3,sK1),X4)) )
    | spl8_20 ),
    inference(resolution,[],[f834,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f834,plain,
    ( ! [X0,X1] : ~ r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1))
    | spl8_20 ),
    inference(resolution,[],[f828,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f828,plain,
    ( ! [X0] : ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,sK1))
    | spl8_20 ),
    inference(resolution,[],[f599,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f599,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | spl8_20 ),
    inference(avatar_component_clause,[],[f597])).

fof(f597,plain,
    ( spl8_20
  <=> r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f827,plain,
    ( spl8_7
    | spl8_6
    | ~ spl8_2
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f820,f795,f90,f256,f260])).

fof(f260,plain,
    ( spl8_7
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f256,plain,
    ( spl8_6
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f90,plain,
    ( spl8_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f795,plain,
    ( spl8_30
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f820,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ spl8_2
    | ~ spl8_30 ),
    inference(resolution,[],[f797,f456])).

fof(f456,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(k2_zfmisc_1(X1,X0))
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | ~ spl8_2 ),
    inference(resolution,[],[f453,f175])).

fof(f175,plain,
    ( ! [X0] :
        ( m1_subset_1(k1_xboole_0,X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl8_2 ),
    inference(resolution,[],[f92,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f92,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f453,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k1_xboole_0,k2_zfmisc_1(X0,X1))
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | ~ spl8_2 ),
    inference(resolution,[],[f192,f92])).

fof(f192,plain,(
    ! [X6,X4,X5] :
      ( ~ v1_xboole_0(X4)
      | ~ m1_subset_1(X4,k2_zfmisc_1(X5,X6))
      | k1_xboole_0 = X6
      | k1_xboole_0 = X5 ) ),
    inference(superposition,[],[f54,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2
      | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( ~ ! [X2] :
              ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
             => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_mcart_1)).

fof(f54,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k4_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : ~ v1_xboole_0(k4_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_zfmisc_1)).

fof(f797,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f795])).

fof(f819,plain,
    ( ~ spl8_2
    | ~ spl8_27
    | spl8_30 ),
    inference(avatar_contradiction_clause,[],[f818])).

fof(f818,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_27
    | spl8_30 ),
    inference(resolution,[],[f811,f92])).

fof(f811,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl8_27
    | spl8_30 ),
    inference(backward_demodulation,[],[f796,f772])).

fof(f772,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f770])).

fof(f796,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | spl8_30 ),
    inference(avatar_component_clause,[],[f795])).

fof(f806,plain,
    ( spl8_31
    | spl8_10
    | ~ spl8_16
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f802,f591,f507,f272,f804])).

fof(f272,plain,
    ( spl8_10
  <=> sK3 = k2_mcart_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f507,plain,
    ( spl8_16
  <=> m1_subset_1(k2_mcart_1(sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f591,plain,
    ( spl8_18
  <=> ! [X2] :
        ( sK3 = X2
        | ~ m1_subset_1(X2,sK2)
        | sK4 != k4_tarski(k1_mcart_1(sK4),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f802,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k2_mcart_1(sK4),sK2)
        | sK3 = k2_mcart_1(sK4)
        | ~ m1_subset_1(sK4,k2_zfmisc_1(X0,X1))
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | ~ spl8_18 ),
    inference(trivial_inequality_removal,[],[f801])).

fof(f801,plain,
    ( ! [X0,X1] :
        ( sK4 != sK4
        | ~ m1_subset_1(k2_mcart_1(sK4),sK2)
        | sK3 = k2_mcart_1(sK4)
        | ~ m1_subset_1(sK4,k2_zfmisc_1(X0,X1))
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | ~ spl8_18 ),
    inference(superposition,[],[f592,f63])).

fof(f592,plain,
    ( ! [X2] :
        ( sK4 != k4_tarski(k1_mcart_1(sK4),X2)
        | ~ m1_subset_1(X2,sK2)
        | sK3 = X2 )
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f591])).

fof(f798,plain,
    ( spl8_23
    | spl8_6
    | spl8_7
    | spl8_30
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f788,f594,f795,f260,f256,f704])).

fof(f594,plain,
    ( spl8_19
  <=> ! [X1,X0] :
        ( k1_xboole_0 = X0
        | ~ m1_subset_1(k1_mcart_1(sK4),k2_zfmisc_1(X0,X1))
        | k1_xboole_0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f788,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl8_19 ),
    inference(resolution,[],[f736,f74])).

fof(f736,plain,
    ( ! [X6,X4,X5] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6))
        | v1_xboole_0(k2_zfmisc_1(X4,X5))
        | k1_xboole_0 = X5
        | k1_xboole_0 = X4
        | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6)) )
    | ~ spl8_19 ),
    inference(resolution,[],[f717,f55])).

fof(f717,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(X1,X0),X2))
        | k1_xboole_0 = X1
        | v1_xboole_0(k2_zfmisc_1(X1,X0))
        | k1_xboole_0 = X0 )
    | ~ spl8_19 ),
    inference(resolution,[],[f694,f66])).

fof(f694,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,X1))
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | v1_xboole_0(k2_zfmisc_1(X0,X1)) )
    | ~ spl8_19 ),
    inference(resolution,[],[f595,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f595,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k1_mcart_1(sK4),k2_zfmisc_1(X0,X1))
        | k1_xboole_0 = X0
        | k1_xboole_0 = X1 )
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f594])).

fof(f773,plain,
    ( spl8_8
    | spl8_27
    | ~ spl8_2
    | ~ spl8_23 ),
    inference(avatar_split_clause,[],[f762,f704,f90,f770,f264])).

fof(f762,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK2
    | ~ spl8_2
    | ~ spl8_23 ),
    inference(resolution,[],[f706,f456])).

fof(f706,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f704])).

fof(f600,plain,
    ( spl8_18
    | spl8_19
    | ~ spl8_20
    | ~ spl8_13
    | ~ spl8_17 ),
    inference(avatar_split_clause,[],[f589,f585,f338,f597,f594,f591])).

fof(f338,plain,
    ( spl8_13
  <=> ! [X1,X3,X0,X2] :
        ( sK3 = X0
        | ~ r2_hidden(k2_mcart_1(X1),sK1)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X3
        | ~ m1_subset_1(X1,k2_zfmisc_1(X2,X3))
        | ~ m1_subset_1(k1_mcart_1(X1),sK0)
        | sK4 != k4_tarski(X1,X0)
        | ~ m1_subset_1(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f585,plain,
    ( spl8_17
  <=> m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f589,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1)
        | k1_xboole_0 = X0
        | k1_xboole_0 = X1
        | ~ m1_subset_1(k1_mcart_1(sK4),k2_zfmisc_1(X0,X1))
        | sK3 = X2
        | sK4 != k4_tarski(k1_mcart_1(sK4),X2)
        | ~ m1_subset_1(X2,sK2) )
    | ~ spl8_13
    | ~ spl8_17 ),
    inference(resolution,[],[f587,f339])).

fof(f339,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(k1_mcart_1(X1),sK0)
        | ~ r2_hidden(k2_mcart_1(X1),sK1)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X3
        | ~ m1_subset_1(X1,k2_zfmisc_1(X2,X3))
        | sK3 = X0
        | sK4 != k4_tarski(X1,X0)
        | ~ m1_subset_1(X0,sK2) )
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f338])).

fof(f587,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f585])).

fof(f588,plain,
    ( spl8_6
    | spl8_7
    | spl8_8
    | spl8_17 ),
    inference(avatar_split_clause,[],[f580,f585,f264,f260,f256])).

fof(f580,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f395,f74])).

fof(f395,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | m1_subset_1(k1_mcart_1(k1_mcart_1(X3)),X0)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f392])).

fof(f392,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k1_mcart_1(k1_mcart_1(X3)),X0)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f78,f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f68,f65])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f71,f65])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_mcart_1)).

fof(f560,plain,(
    ~ spl8_8 ),
    inference(avatar_contradiction_clause,[],[f559])).

fof(f559,plain,
    ( $false
    | ~ spl8_8 ),
    inference(trivial_inequality_removal,[],[f558])).

fof(f558,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl8_8 ),
    inference(superposition,[],[f46,f266])).

fof(f266,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f264])).

fof(f46,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f30])).

fof(f534,plain,
    ( ~ spl8_2
    | ~ spl8_6
    | spl8_14 ),
    inference(avatar_contradiction_clause,[],[f533])).

fof(f533,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_6
    | spl8_14 ),
    inference(resolution,[],[f528,f92])).

fof(f528,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl8_6
    | spl8_14 ),
    inference(backward_demodulation,[],[f385,f258])).

fof(f258,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f256])).

fof(f385,plain,
    ( ~ v1_xboole_0(sK0)
    | spl8_14 ),
    inference(avatar_component_clause,[],[f384])).

fof(f384,plain,
    ( spl8_14
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f522,plain,
    ( ~ spl8_2
    | ~ spl8_7
    | spl8_12 ),
    inference(avatar_contradiction_clause,[],[f521])).

fof(f521,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_7
    | spl8_12 ),
    inference(resolution,[],[f515,f92])).

fof(f515,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl8_7
    | spl8_12 ),
    inference(backward_demodulation,[],[f335,f262])).

fof(f262,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f260])).

fof(f335,plain,
    ( ~ v1_xboole_0(sK1)
    | spl8_12 ),
    inference(avatar_component_clause,[],[f334])).

fof(f334,plain,
    ( spl8_12
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f510,plain,
    ( spl8_6
    | spl8_7
    | spl8_8
    | spl8_16 ),
    inference(avatar_split_clause,[],[f502,f507,f264,f260,f256])).

fof(f502,plain,
    ( m1_subset_1(k2_mcart_1(sK4),sK2)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f254,f74])).

fof(f254,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | m1_subset_1(k2_mcart_1(X3),X2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f253])).

fof(f253,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_mcart_1(X3),X2)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f79,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f70,f65])).

% (7248)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f72,f65])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_mcart_1)).

fof(f433,plain,(
    ~ spl8_14 ),
    inference(avatar_contradiction_clause,[],[f432])).

fof(f432,plain,
    ( $false
    | ~ spl8_14 ),
    inference(trivial_inequality_removal,[],[f431])).

fof(f431,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl8_14 ),
    inference(superposition,[],[f44,f400])).

fof(f400,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_14 ),
    inference(resolution,[],[f398,f51])).

fof(f51,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK6(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK6(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f19,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X5,X4,X3,X2] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK6(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK6(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).

fof(f398,plain,
    ( ! [X2] : ~ r2_hidden(X2,sK0)
    | ~ spl8_14 ),
    inference(resolution,[],[f386,f49])).

fof(f49,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK5(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f32,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f386,plain,
    ( v1_xboole_0(sK0)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f384])).

fof(f44,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f30])).

fof(f378,plain,(
    ~ spl8_12 ),
    inference(avatar_contradiction_clause,[],[f377])).

fof(f377,plain,
    ( $false
    | ~ spl8_12 ),
    inference(trivial_inequality_removal,[],[f376])).

fof(f376,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl8_12 ),
    inference(superposition,[],[f45,f345])).

fof(f345,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_12 ),
    inference(resolution,[],[f343,f51])).

fof(f343,plain,
    ( ! [X2] : ~ r2_hidden(X2,sK1)
    | ~ spl8_12 ),
    inference(resolution,[],[f336,f49])).

fof(f336,plain,
    ( v1_xboole_0(sK1)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f334])).

fof(f45,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f30])).

fof(f340,plain,
    ( spl8_12
    | spl8_13 ),
    inference(avatar_split_clause,[],[f332,f338,f334])).

fof(f332,plain,(
    ! [X2,X0,X3,X1] :
      ( sK3 = X0
      | ~ m1_subset_1(X0,sK2)
      | sK4 != k4_tarski(X1,X0)
      | ~ m1_subset_1(k1_mcart_1(X1),sK0)
      | ~ m1_subset_1(X1,k2_zfmisc_1(X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | ~ r2_hidden(k2_mcart_1(X1),sK1)
      | v1_xboole_0(sK1) ) ),
    inference(resolution,[],[f191,f56])).

fof(f191,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(k2_mcart_1(X0),sK1)
      | sK3 = X1
      | ~ m1_subset_1(X1,sK2)
      | k4_tarski(X0,X1) != sK4
      | ~ m1_subset_1(k1_mcart_1(X0),sK0)
      | ~ m1_subset_1(X0,k2_zfmisc_1(X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2 ) ),
    inference(superposition,[],[f73,f63])).

fof(f73,plain,(
    ! [X6,X7,X5] :
      ( sK4 != k4_tarski(k4_tarski(X5,X6),X7)
      | sK3 = X7
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(definition_unfolding,[],[f43,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f43,plain,(
    ! [X6,X7,X5] :
      ( sK3 = X7
      | k3_mcart_1(X5,X6,X7) != sK4
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f278,plain,(
    spl8_9 ),
    inference(avatar_contradiction_clause,[],[f276])).

fof(f276,plain,
    ( $false
    | spl8_9 ),
    inference(resolution,[],[f270,f74])).

fof(f270,plain,
    ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | spl8_9 ),
    inference(avatar_component_clause,[],[f268])).

fof(f268,plain,
    ( spl8_9
  <=> m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f275,plain,
    ( spl8_6
    | spl8_7
    | spl8_8
    | ~ spl8_9
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f252,f272,f268,f264,f260,f256])).

fof(f252,plain,
    ( sK3 != k2_mcart_1(sK4)
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f47,f75])).

fof(f47,plain,(
    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f174,plain,(
    spl8_5 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | spl8_5 ),
    inference(resolution,[],[f171,f48])).

fof(f48,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f171,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | spl8_5 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl8_5
  <=> r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f172,plain,
    ( spl8_2
    | ~ spl8_5
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f167,f86,f169,f90])).

fof(f86,plain,
    ( spl8_1
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f167,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0)
    | ~ spl8_1 ),
    inference(resolution,[],[f88,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_xboole_0(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f88,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f93,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f82,f90,f86])).

fof(f82,plain,
    ( v1_xboole_0(k1_xboole_0)
    | r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f81,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f39,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f81,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK7(X0,k1_xboole_0),k1_xboole_0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f80,f48])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(sK7(X0,X1),X1)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f62,f59])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK7(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:43:01 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.48  % (7250)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.50  % (7267)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.50  % (7249)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (7241)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (7258)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.52  % (7255)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.52  % (7237)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (7266)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.52  % (7260)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (7247)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (7247)Refutation not found, incomplete strategy% (7247)------------------------------
% 0.20/0.52  % (7247)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (7247)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (7247)Memory used [KB]: 10618
% 0.20/0.52  % (7247)Time elapsed: 0.123 s
% 0.20/0.52  % (7247)------------------------------
% 0.20/0.52  % (7247)------------------------------
% 0.20/0.53  % (7251)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (7264)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.53  % (7239)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (7263)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (7238)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (7239)Refutation not found, incomplete strategy% (7239)------------------------------
% 0.20/0.53  % (7239)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (7239)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (7239)Memory used [KB]: 10746
% 0.20/0.53  % (7239)Time elapsed: 0.125 s
% 0.20/0.53  % (7239)------------------------------
% 0.20/0.53  % (7239)------------------------------
% 0.20/0.53  % (7240)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (7243)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (7253)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (7252)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (7258)Refutation not found, incomplete strategy% (7258)------------------------------
% 0.20/0.54  % (7258)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (7258)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (7258)Memory used [KB]: 10746
% 0.20/0.54  % (7258)Time elapsed: 0.115 s
% 0.20/0.54  % (7258)------------------------------
% 0.20/0.54  % (7258)------------------------------
% 0.20/0.54  % (7254)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (7262)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (7242)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.54  % (7261)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.55  % (7246)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.55  % (7245)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.55  % (7244)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.56  % (7259)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.56  % (7259)Refutation not found, incomplete strategy% (7259)------------------------------
% 0.20/0.56  % (7259)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (7259)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (7259)Memory used [KB]: 1791
% 0.20/0.56  % (7259)Time elapsed: 0.156 s
% 0.20/0.56  % (7259)------------------------------
% 0.20/0.56  % (7259)------------------------------
% 0.20/0.57  % (7265)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.57  % (7249)Refutation found. Thanks to Tanya!
% 0.20/0.57  % SZS status Theorem for theBenchmark
% 0.20/0.57  % (7257)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.57  % SZS output start Proof for theBenchmark
% 0.20/0.57  fof(f986,plain,(
% 0.20/0.57    $false),
% 0.20/0.57    inference(avatar_sat_refutation,[],[f93,f172,f174,f275,f278,f340,f378,f433,f510,f522,f534,f560,f588,f600,f773,f798,f806,f819,f827,f916,f985])).
% 0.20/0.57  fof(f985,plain,(
% 0.20/0.57    spl8_8 | spl8_27 | ~spl8_31),
% 0.20/0.57    inference(avatar_split_clause,[],[f981,f804,f770,f264])).
% 0.20/0.57  fof(f264,plain,(
% 0.20/0.57    spl8_8 <=> k1_xboole_0 = sK2),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.20/0.57  fof(f770,plain,(
% 0.20/0.57    spl8_27 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).
% 0.20/0.57  fof(f804,plain,(
% 0.20/0.57    spl8_31 <=> ! [X1,X0] : (~m1_subset_1(sK4,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X0 | k1_xboole_0 = X1)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).
% 0.20/0.57  fof(f981,plain,(
% 0.20/0.57    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK2 | ~spl8_31),
% 0.20/0.57    inference(resolution,[],[f805,f74])).
% 0.20/0.57  fof(f74,plain,(
% 0.20/0.57    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.20/0.57    inference(definition_unfolding,[],[f42,f65])).
% 0.20/0.57  fof(f65,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f8])).
% 0.20/0.57  fof(f8,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.20/0.57  fof(f42,plain,(
% 0.20/0.57    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.20/0.57    inference(cnf_transformation,[],[f30])).
% 0.20/0.57  fof(f30,plain,(
% 0.20/0.57    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f18,f29])).
% 0.20/0.57  fof(f29,plain,(
% 0.20/0.57    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f18,plain,(
% 0.20/0.57    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.20/0.57    inference(flattening,[],[f17])).
% 0.20/0.57  fof(f17,plain,(
% 0.20/0.57    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.20/0.57    inference(ennf_transformation,[],[f16])).
% 0.20/0.57  fof(f16,negated_conjecture,(
% 0.20/0.57    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.20/0.57    inference(negated_conjecture,[],[f15])).
% 0.20/0.57  fof(f15,conjecture,(
% 0.20/0.57    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_mcart_1)).
% 0.20/0.57  fof(f805,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~m1_subset_1(sK4,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X0 | k1_xboole_0 = X1) ) | ~spl8_31),
% 0.20/0.57    inference(avatar_component_clause,[],[f804])).
% 0.20/0.57  fof(f916,plain,(
% 0.20/0.57    spl8_20 | spl8_23),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f908])).
% 0.20/0.57  fof(f908,plain,(
% 0.20/0.57    $false | (spl8_20 | spl8_23)),
% 0.20/0.57    inference(resolution,[],[f901,f705])).
% 0.20/0.57  fof(f705,plain,(
% 0.20/0.57    ~v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | spl8_23),
% 0.20/0.57    inference(avatar_component_clause,[],[f704])).
% 0.20/0.57  fof(f704,plain,(
% 0.20/0.57    spl8_23 <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 0.20/0.57  fof(f901,plain,(
% 0.20/0.57    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | spl8_20),
% 0.20/0.57    inference(resolution,[],[f840,f74])).
% 0.20/0.57  fof(f840,plain,(
% 0.20/0.57    ( ! [X4,X3] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X3,sK1),X4)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X3,sK1),X4))) ) | spl8_20),
% 0.20/0.57    inference(resolution,[],[f834,f55])).
% 0.20/0.57  fof(f55,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f37])).
% 0.20/0.57  fof(f37,plain,(
% 0.20/0.57    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.20/0.57    inference(nnf_transformation,[],[f20])).
% 0.20/0.57  fof(f20,plain,(
% 0.20/0.57    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.20/0.57    inference(ennf_transformation,[],[f6])).
% 0.20/0.57  fof(f6,axiom,(
% 0.20/0.57    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.20/0.57  fof(f834,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1))) ) | spl8_20),
% 0.20/0.57    inference(resolution,[],[f828,f66])).
% 0.20/0.57  fof(f66,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f25])).
% 0.20/0.57  fof(f25,plain,(
% 0.20/0.57    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.57    inference(ennf_transformation,[],[f11])).
% 0.20/0.57  fof(f11,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.20/0.57  fof(f828,plain,(
% 0.20/0.57    ( ! [X0] : (~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,sK1))) ) | spl8_20),
% 0.20/0.57    inference(resolution,[],[f599,f67])).
% 0.20/0.57  fof(f67,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f25])).
% 0.20/0.57  fof(f599,plain,(
% 0.20/0.57    ~r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1) | spl8_20),
% 0.20/0.57    inference(avatar_component_clause,[],[f597])).
% 0.20/0.57  fof(f597,plain,(
% 0.20/0.57    spl8_20 <=> r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 0.20/0.57  fof(f827,plain,(
% 0.20/0.57    spl8_7 | spl8_6 | ~spl8_2 | ~spl8_30),
% 0.20/0.57    inference(avatar_split_clause,[],[f820,f795,f90,f256,f260])).
% 0.20/0.57  fof(f260,plain,(
% 0.20/0.57    spl8_7 <=> k1_xboole_0 = sK1),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.20/0.57  fof(f256,plain,(
% 0.20/0.57    spl8_6 <=> k1_xboole_0 = sK0),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.20/0.57  fof(f90,plain,(
% 0.20/0.57    spl8_2 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.20/0.57  fof(f795,plain,(
% 0.20/0.57    spl8_30 <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).
% 0.20/0.57  fof(f820,plain,(
% 0.20/0.57    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | (~spl8_2 | ~spl8_30)),
% 0.20/0.57    inference(resolution,[],[f797,f456])).
% 0.20/0.57  fof(f456,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~v1_xboole_0(k2_zfmisc_1(X1,X0)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) ) | ~spl8_2),
% 0.20/0.57    inference(resolution,[],[f453,f175])).
% 0.20/0.57  fof(f175,plain,(
% 0.20/0.57    ( ! [X0] : (m1_subset_1(k1_xboole_0,X0) | ~v1_xboole_0(X0)) ) | ~spl8_2),
% 0.20/0.57    inference(resolution,[],[f92,f58])).
% 0.20/0.57  fof(f58,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~v1_xboole_0(X1) | m1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f37])).
% 0.20/0.57  fof(f92,plain,(
% 0.20/0.57    v1_xboole_0(k1_xboole_0) | ~spl8_2),
% 0.20/0.57    inference(avatar_component_clause,[],[f90])).
% 0.20/0.57  fof(f453,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~m1_subset_1(k1_xboole_0,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) ) | ~spl8_2),
% 0.20/0.57    inference(resolution,[],[f192,f92])).
% 0.20/0.57  fof(f192,plain,(
% 0.20/0.57    ( ! [X6,X4,X5] : (~v1_xboole_0(X4) | ~m1_subset_1(X4,k2_zfmisc_1(X5,X6)) | k1_xboole_0 = X6 | k1_xboole_0 = X5) )),
% 0.20/0.57    inference(superposition,[],[f54,f63])).
% 0.20/0.57  fof(f63,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 | ~m1_subset_1(X2,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.57    inference(cnf_transformation,[],[f24])).
% 0.20/0.57  fof(f24,plain,(
% 0.20/0.57    ! [X0,X1] : (! [X2] : (k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 | ~m1_subset_1(X2,k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.57    inference(ennf_transformation,[],[f12])).
% 0.20/0.57  fof(f12,axiom,(
% 0.20/0.57    ! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_mcart_1)).
% 0.20/0.57  fof(f54,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~v1_xboole_0(k4_tarski(X0,X1))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f5])).
% 0.20/0.57  fof(f5,axiom,(
% 0.20/0.57    ! [X0,X1] : ~v1_xboole_0(k4_tarski(X0,X1))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_zfmisc_1)).
% 0.20/0.57  fof(f797,plain,(
% 0.20/0.57    v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | ~spl8_30),
% 0.20/0.57    inference(avatar_component_clause,[],[f795])).
% 0.20/0.57  fof(f819,plain,(
% 0.20/0.57    ~spl8_2 | ~spl8_27 | spl8_30),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f818])).
% 0.20/0.57  fof(f818,plain,(
% 0.20/0.57    $false | (~spl8_2 | ~spl8_27 | spl8_30)),
% 0.20/0.57    inference(resolution,[],[f811,f92])).
% 0.20/0.57  fof(f811,plain,(
% 0.20/0.57    ~v1_xboole_0(k1_xboole_0) | (~spl8_27 | spl8_30)),
% 0.20/0.57    inference(backward_demodulation,[],[f796,f772])).
% 0.20/0.57  fof(f772,plain,(
% 0.20/0.57    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl8_27),
% 0.20/0.57    inference(avatar_component_clause,[],[f770])).
% 0.20/0.57  fof(f796,plain,(
% 0.20/0.57    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | spl8_30),
% 0.20/0.57    inference(avatar_component_clause,[],[f795])).
% 0.20/0.57  fof(f806,plain,(
% 0.20/0.57    spl8_31 | spl8_10 | ~spl8_16 | ~spl8_18),
% 0.20/0.57    inference(avatar_split_clause,[],[f802,f591,f507,f272,f804])).
% 0.20/0.57  fof(f272,plain,(
% 0.20/0.57    spl8_10 <=> sK3 = k2_mcart_1(sK4)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.20/0.57  fof(f507,plain,(
% 0.20/0.57    spl8_16 <=> m1_subset_1(k2_mcart_1(sK4),sK2)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.20/0.57  fof(f591,plain,(
% 0.20/0.57    spl8_18 <=> ! [X2] : (sK3 = X2 | ~m1_subset_1(X2,sK2) | sK4 != k4_tarski(k1_mcart_1(sK4),X2))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.20/0.57  fof(f802,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~m1_subset_1(k2_mcart_1(sK4),sK2) | sK3 = k2_mcart_1(sK4) | ~m1_subset_1(sK4,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) ) | ~spl8_18),
% 0.20/0.57    inference(trivial_inequality_removal,[],[f801])).
% 0.20/0.57  fof(f801,plain,(
% 0.20/0.57    ( ! [X0,X1] : (sK4 != sK4 | ~m1_subset_1(k2_mcart_1(sK4),sK2) | sK3 = k2_mcart_1(sK4) | ~m1_subset_1(sK4,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) ) | ~spl8_18),
% 0.20/0.57    inference(superposition,[],[f592,f63])).
% 0.20/0.57  fof(f592,plain,(
% 0.20/0.57    ( ! [X2] : (sK4 != k4_tarski(k1_mcart_1(sK4),X2) | ~m1_subset_1(X2,sK2) | sK3 = X2) ) | ~spl8_18),
% 0.20/0.57    inference(avatar_component_clause,[],[f591])).
% 0.20/0.57  fof(f798,plain,(
% 0.20/0.57    spl8_23 | spl8_6 | spl8_7 | spl8_30 | ~spl8_19),
% 0.20/0.57    inference(avatar_split_clause,[],[f788,f594,f795,f260,f256,f704])).
% 0.20/0.57  fof(f594,plain,(
% 0.20/0.57    spl8_19 <=> ! [X1,X0] : (k1_xboole_0 = X0 | ~m1_subset_1(k1_mcart_1(sK4),k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X1)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 0.20/0.57  fof(f788,plain,(
% 0.20/0.57    v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl8_19),
% 0.20/0.57    inference(resolution,[],[f736,f74])).
% 0.20/0.57  fof(f736,plain,(
% 0.20/0.57    ( ! [X6,X4,X5] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6)) | v1_xboole_0(k2_zfmisc_1(X4,X5)) | k1_xboole_0 = X5 | k1_xboole_0 = X4 | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6))) ) | ~spl8_19),
% 0.20/0.57    inference(resolution,[],[f717,f55])).
% 0.20/0.57  fof(f717,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(X1,X0),X2)) | k1_xboole_0 = X1 | v1_xboole_0(k2_zfmisc_1(X1,X0)) | k1_xboole_0 = X0) ) | ~spl8_19),
% 0.20/0.57    inference(resolution,[],[f694,f66])).
% 0.20/0.57  fof(f694,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | v1_xboole_0(k2_zfmisc_1(X0,X1))) ) | ~spl8_19),
% 0.20/0.57    inference(resolution,[],[f595,f56])).
% 0.20/0.57  fof(f56,plain,(
% 0.20/0.57    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f37])).
% 0.20/0.57  fof(f595,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~m1_subset_1(k1_mcart_1(sK4),k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X0 | k1_xboole_0 = X1) ) | ~spl8_19),
% 0.20/0.57    inference(avatar_component_clause,[],[f594])).
% 0.20/0.57  fof(f773,plain,(
% 0.20/0.57    spl8_8 | spl8_27 | ~spl8_2 | ~spl8_23),
% 0.20/0.57    inference(avatar_split_clause,[],[f762,f704,f90,f770,f264])).
% 0.20/0.57  fof(f762,plain,(
% 0.20/0.57    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK2 | (~spl8_2 | ~spl8_23)),
% 0.20/0.57    inference(resolution,[],[f706,f456])).
% 0.20/0.57  fof(f706,plain,(
% 0.20/0.57    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl8_23),
% 0.20/0.57    inference(avatar_component_clause,[],[f704])).
% 0.20/0.57  fof(f600,plain,(
% 0.20/0.57    spl8_18 | spl8_19 | ~spl8_20 | ~spl8_13 | ~spl8_17),
% 0.20/0.57    inference(avatar_split_clause,[],[f589,f585,f338,f597,f594,f591])).
% 0.20/0.57  fof(f338,plain,(
% 0.20/0.57    spl8_13 <=> ! [X1,X3,X0,X2] : (sK3 = X0 | ~r2_hidden(k2_mcart_1(X1),sK1) | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X1,k2_zfmisc_1(X2,X3)) | ~m1_subset_1(k1_mcart_1(X1),sK0) | sK4 != k4_tarski(X1,X0) | ~m1_subset_1(X0,sK2))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.20/0.57  fof(f585,plain,(
% 0.20/0.57    spl8_17 <=> m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.20/0.57  fof(f589,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | ~m1_subset_1(k1_mcart_1(sK4),k2_zfmisc_1(X0,X1)) | sK3 = X2 | sK4 != k4_tarski(k1_mcart_1(sK4),X2) | ~m1_subset_1(X2,sK2)) ) | (~spl8_13 | ~spl8_17)),
% 0.20/0.57    inference(resolution,[],[f587,f339])).
% 0.20/0.57  fof(f339,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(k1_mcart_1(X1),sK0) | ~r2_hidden(k2_mcart_1(X1),sK1) | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X1,k2_zfmisc_1(X2,X3)) | sK3 = X0 | sK4 != k4_tarski(X1,X0) | ~m1_subset_1(X0,sK2)) ) | ~spl8_13),
% 0.20/0.57    inference(avatar_component_clause,[],[f338])).
% 0.20/0.57  fof(f587,plain,(
% 0.20/0.57    m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) | ~spl8_17),
% 0.20/0.57    inference(avatar_component_clause,[],[f585])).
% 0.20/0.57  fof(f588,plain,(
% 0.20/0.57    spl8_6 | spl8_7 | spl8_8 | spl8_17),
% 0.20/0.57    inference(avatar_split_clause,[],[f580,f585,f264,f260,f256])).
% 0.20/0.57  fof(f580,plain,(
% 0.20/0.57    m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.20/0.57    inference(resolution,[],[f395,f74])).
% 0.20/0.57  fof(f395,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | m1_subset_1(k1_mcart_1(k1_mcart_1(X3)),X0) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.57    inference(duplicate_literal_removal,[],[f392])).
% 0.20/0.57  fof(f392,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (m1_subset_1(k1_mcart_1(k1_mcart_1(X3)),X0) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.57    inference(superposition,[],[f78,f77])).
% 0.20/0.57  fof(f77,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.57    inference(definition_unfolding,[],[f68,f65])).
% 0.20/0.57  fof(f68,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.57    inference(cnf_transformation,[],[f26])).
% 0.20/0.57  fof(f26,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.57    inference(ennf_transformation,[],[f14])).
% 0.20/0.57  fof(f14,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).
% 0.20/0.57  fof(f78,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 0.20/0.57    inference(definition_unfolding,[],[f71,f65])).
% 0.20/0.57  fof(f71,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f27])).
% 0.20/0.57  fof(f27,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 0.20/0.57    inference(ennf_transformation,[],[f9])).
% 0.20/0.57  fof(f9,axiom,(
% 0.20/0.57    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_mcart_1)).
% 0.20/0.57  fof(f560,plain,(
% 0.20/0.57    ~spl8_8),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f559])).
% 0.20/0.57  fof(f559,plain,(
% 0.20/0.57    $false | ~spl8_8),
% 0.20/0.57    inference(trivial_inequality_removal,[],[f558])).
% 0.20/0.57  fof(f558,plain,(
% 0.20/0.57    k1_xboole_0 != k1_xboole_0 | ~spl8_8),
% 0.20/0.57    inference(superposition,[],[f46,f266])).
% 0.20/0.57  fof(f266,plain,(
% 0.20/0.57    k1_xboole_0 = sK2 | ~spl8_8),
% 0.20/0.57    inference(avatar_component_clause,[],[f264])).
% 0.20/0.57  fof(f46,plain,(
% 0.20/0.57    k1_xboole_0 != sK2),
% 0.20/0.57    inference(cnf_transformation,[],[f30])).
% 0.20/0.57  fof(f534,plain,(
% 0.20/0.57    ~spl8_2 | ~spl8_6 | spl8_14),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f533])).
% 0.20/0.57  fof(f533,plain,(
% 0.20/0.57    $false | (~spl8_2 | ~spl8_6 | spl8_14)),
% 0.20/0.57    inference(resolution,[],[f528,f92])).
% 0.20/0.57  fof(f528,plain,(
% 0.20/0.57    ~v1_xboole_0(k1_xboole_0) | (~spl8_6 | spl8_14)),
% 0.20/0.57    inference(backward_demodulation,[],[f385,f258])).
% 0.20/0.57  fof(f258,plain,(
% 0.20/0.57    k1_xboole_0 = sK0 | ~spl8_6),
% 0.20/0.57    inference(avatar_component_clause,[],[f256])).
% 0.20/0.57  fof(f385,plain,(
% 0.20/0.57    ~v1_xboole_0(sK0) | spl8_14),
% 0.20/0.57    inference(avatar_component_clause,[],[f384])).
% 0.20/0.57  fof(f384,plain,(
% 0.20/0.57    spl8_14 <=> v1_xboole_0(sK0)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.20/0.57  fof(f522,plain,(
% 0.20/0.57    ~spl8_2 | ~spl8_7 | spl8_12),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f521])).
% 0.20/0.57  fof(f521,plain,(
% 0.20/0.57    $false | (~spl8_2 | ~spl8_7 | spl8_12)),
% 0.20/0.57    inference(resolution,[],[f515,f92])).
% 0.20/0.57  fof(f515,plain,(
% 0.20/0.57    ~v1_xboole_0(k1_xboole_0) | (~spl8_7 | spl8_12)),
% 0.20/0.57    inference(backward_demodulation,[],[f335,f262])).
% 0.20/0.57  fof(f262,plain,(
% 0.20/0.57    k1_xboole_0 = sK1 | ~spl8_7),
% 0.20/0.57    inference(avatar_component_clause,[],[f260])).
% 0.20/0.57  fof(f335,plain,(
% 0.20/0.57    ~v1_xboole_0(sK1) | spl8_12),
% 0.20/0.57    inference(avatar_component_clause,[],[f334])).
% 0.20/0.57  fof(f334,plain,(
% 0.20/0.57    spl8_12 <=> v1_xboole_0(sK1)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.20/0.57  fof(f510,plain,(
% 0.20/0.57    spl8_6 | spl8_7 | spl8_8 | spl8_16),
% 0.20/0.57    inference(avatar_split_clause,[],[f502,f507,f264,f260,f256])).
% 0.20/0.57  fof(f502,plain,(
% 0.20/0.57    m1_subset_1(k2_mcart_1(sK4),sK2) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.20/0.57    inference(resolution,[],[f254,f74])).
% 0.20/0.58  fof(f254,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | m1_subset_1(k2_mcart_1(X3),X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.58    inference(duplicate_literal_removal,[],[f253])).
% 0.20/0.58  fof(f253,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_mcart_1(X3),X2) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.58    inference(superposition,[],[f79,f75])).
% 0.20/0.58  fof(f75,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.58    inference(definition_unfolding,[],[f70,f65])).
% 0.20/0.58  % (7248)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.58  fof(f70,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.58    inference(cnf_transformation,[],[f26])).
% 0.20/0.58  fof(f79,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 0.20/0.58    inference(definition_unfolding,[],[f72,f65])).
% 0.20/0.58  fof(f72,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f28])).
% 0.20/0.58  fof(f28,plain,(
% 0.20/0.58    ! [X0,X1,X2,X3] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 0.20/0.58    inference(ennf_transformation,[],[f10])).
% 0.20/0.58  fof(f10,axiom,(
% 0.20/0.58    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_mcart_1)).
% 0.20/0.58  fof(f433,plain,(
% 0.20/0.58    ~spl8_14),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f432])).
% 0.20/0.58  fof(f432,plain,(
% 0.20/0.58    $false | ~spl8_14),
% 0.20/0.58    inference(trivial_inequality_removal,[],[f431])).
% 0.20/0.58  fof(f431,plain,(
% 0.20/0.58    k1_xboole_0 != k1_xboole_0 | ~spl8_14),
% 0.20/0.58    inference(superposition,[],[f44,f400])).
% 0.20/0.58  fof(f400,plain,(
% 0.20/0.58    k1_xboole_0 = sK0 | ~spl8_14),
% 0.20/0.58    inference(resolution,[],[f398,f51])).
% 0.20/0.58  fof(f51,plain,(
% 0.20/0.58    ( ! [X0] : (r2_hidden(sK6(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.58    inference(cnf_transformation,[],[f36])).
% 0.20/0.58  fof(f36,plain,(
% 0.20/0.58    ! [X0] : ((! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != sK6(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK6(X0),X0)) | k1_xboole_0 = X0)),
% 0.20/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f19,f35])).
% 0.20/0.58  fof(f35,plain,(
% 0.20/0.58    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X5,X4,X3,X2] : (k4_mcart_1(X2,X3,X4,X5) != sK6(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK6(X0),X0)))),
% 0.20/0.58    introduced(choice_axiom,[])).
% 0.20/0.58  fof(f19,plain,(
% 0.20/0.58    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.20/0.58    inference(ennf_transformation,[],[f13])).
% 0.20/0.58  fof(f13,axiom,(
% 0.20/0.58    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).
% 0.20/0.58  fof(f398,plain,(
% 0.20/0.58    ( ! [X2] : (~r2_hidden(X2,sK0)) ) | ~spl8_14),
% 0.20/0.58    inference(resolution,[],[f386,f49])).
% 0.20/0.58  fof(f49,plain,(
% 0.20/0.58    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f34])).
% 0.20/0.58  fof(f34,plain,(
% 0.20/0.58    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK5(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f32,f33])).
% 0.20/0.58  fof(f33,plain,(
% 0.20/0.58    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK5(X0),X0))),
% 0.20/0.58    introduced(choice_axiom,[])).
% 0.20/0.58  fof(f32,plain,(
% 0.20/0.58    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.58    inference(rectify,[],[f31])).
% 0.20/0.58  fof(f31,plain,(
% 0.20/0.58    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.58    inference(nnf_transformation,[],[f1])).
% 0.20/0.58  fof(f1,axiom,(
% 0.20/0.58    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.58  fof(f386,plain,(
% 0.20/0.58    v1_xboole_0(sK0) | ~spl8_14),
% 0.20/0.58    inference(avatar_component_clause,[],[f384])).
% 0.20/0.58  fof(f44,plain,(
% 0.20/0.58    k1_xboole_0 != sK0),
% 0.20/0.58    inference(cnf_transformation,[],[f30])).
% 0.20/0.58  fof(f378,plain,(
% 0.20/0.58    ~spl8_12),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f377])).
% 0.20/0.58  fof(f377,plain,(
% 0.20/0.58    $false | ~spl8_12),
% 0.20/0.58    inference(trivial_inequality_removal,[],[f376])).
% 0.20/0.58  fof(f376,plain,(
% 0.20/0.58    k1_xboole_0 != k1_xboole_0 | ~spl8_12),
% 0.20/0.58    inference(superposition,[],[f45,f345])).
% 0.20/0.58  fof(f345,plain,(
% 0.20/0.58    k1_xboole_0 = sK1 | ~spl8_12),
% 0.20/0.58    inference(resolution,[],[f343,f51])).
% 0.20/0.58  fof(f343,plain,(
% 0.20/0.58    ( ! [X2] : (~r2_hidden(X2,sK1)) ) | ~spl8_12),
% 0.20/0.58    inference(resolution,[],[f336,f49])).
% 0.20/0.58  fof(f336,plain,(
% 0.20/0.58    v1_xboole_0(sK1) | ~spl8_12),
% 0.20/0.58    inference(avatar_component_clause,[],[f334])).
% 0.20/0.58  fof(f45,plain,(
% 0.20/0.58    k1_xboole_0 != sK1),
% 0.20/0.58    inference(cnf_transformation,[],[f30])).
% 0.20/0.58  fof(f340,plain,(
% 0.20/0.58    spl8_12 | spl8_13),
% 0.20/0.58    inference(avatar_split_clause,[],[f332,f338,f334])).
% 0.20/0.58  fof(f332,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (sK3 = X0 | ~m1_subset_1(X0,sK2) | sK4 != k4_tarski(X1,X0) | ~m1_subset_1(k1_mcart_1(X1),sK0) | ~m1_subset_1(X1,k2_zfmisc_1(X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | ~r2_hidden(k2_mcart_1(X1),sK1) | v1_xboole_0(sK1)) )),
% 0.20/0.58    inference(resolution,[],[f191,f56])).
% 0.20/0.58  fof(f191,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(k2_mcart_1(X0),sK1) | sK3 = X1 | ~m1_subset_1(X1,sK2) | k4_tarski(X0,X1) != sK4 | ~m1_subset_1(k1_mcart_1(X0),sK0) | ~m1_subset_1(X0,k2_zfmisc_1(X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2) )),
% 0.20/0.58    inference(superposition,[],[f73,f63])).
% 0.20/0.58  fof(f73,plain,(
% 0.20/0.58    ( ! [X6,X7,X5] : (sK4 != k4_tarski(k4_tarski(X5,X6),X7) | sK3 = X7 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 0.20/0.58    inference(definition_unfolding,[],[f43,f64])).
% 0.20/0.58  fof(f64,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f7])).
% 0.20/0.58  fof(f7,axiom,(
% 0.20/0.58    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.20/0.58  fof(f43,plain,(
% 0.20/0.58    ( ! [X6,X7,X5] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f30])).
% 0.20/0.58  fof(f278,plain,(
% 0.20/0.58    spl8_9),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f276])).
% 0.20/0.58  fof(f276,plain,(
% 0.20/0.58    $false | spl8_9),
% 0.20/0.58    inference(resolution,[],[f270,f74])).
% 0.20/0.58  fof(f270,plain,(
% 0.20/0.58    ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | spl8_9),
% 0.20/0.58    inference(avatar_component_clause,[],[f268])).
% 0.20/0.58  fof(f268,plain,(
% 0.20/0.58    spl8_9 <=> m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.20/0.58  fof(f275,plain,(
% 0.20/0.58    spl8_6 | spl8_7 | spl8_8 | ~spl8_9 | ~spl8_10),
% 0.20/0.58    inference(avatar_split_clause,[],[f252,f272,f268,f264,f260,f256])).
% 0.20/0.58  fof(f252,plain,(
% 0.20/0.58    sK3 != k2_mcart_1(sK4) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.20/0.58    inference(superposition,[],[f47,f75])).
% 0.20/0.58  fof(f47,plain,(
% 0.20/0.58    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)),
% 0.20/0.58    inference(cnf_transformation,[],[f30])).
% 0.20/0.58  fof(f174,plain,(
% 0.20/0.58    spl8_5),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f173])).
% 0.20/0.58  fof(f173,plain,(
% 0.20/0.58    $false | spl8_5),
% 0.20/0.58    inference(resolution,[],[f171,f48])).
% 0.20/0.58  fof(f48,plain,(
% 0.20/0.58    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f3])).
% 0.20/0.58  fof(f3,axiom,(
% 0.20/0.58    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.20/0.58  fof(f171,plain,(
% 0.20/0.58    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | spl8_5),
% 0.20/0.58    inference(avatar_component_clause,[],[f169])).
% 0.20/0.58  fof(f169,plain,(
% 0.20/0.58    spl8_5 <=> r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.20/0.58  fof(f172,plain,(
% 0.20/0.58    spl8_2 | ~spl8_5 | ~spl8_1),
% 0.20/0.58    inference(avatar_split_clause,[],[f167,f86,f169,f90])).
% 0.20/0.58  fof(f86,plain,(
% 0.20/0.58    spl8_1 <=> r1_tarski(k1_xboole_0,k1_xboole_0)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.20/0.58  fof(f167,plain,(
% 0.20/0.58    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | v1_xboole_0(k1_xboole_0) | ~spl8_1),
% 0.20/0.58    inference(resolution,[],[f88,f59])).
% 0.20/0.58  fof(f59,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_xboole_0(X1,X0) | v1_xboole_0(X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f22])).
% 0.20/0.58  fof(f22,plain,(
% 0.20/0.58    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.20/0.58    inference(flattening,[],[f21])).
% 0.20/0.58  fof(f21,plain,(
% 0.20/0.58    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.20/0.58    inference(ennf_transformation,[],[f4])).
% 0.20/0.58  fof(f4,axiom,(
% 0.20/0.58    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.20/0.58  fof(f88,plain,(
% 0.20/0.58    r1_tarski(k1_xboole_0,k1_xboole_0) | ~spl8_1),
% 0.20/0.58    inference(avatar_component_clause,[],[f86])).
% 0.20/0.58  fof(f93,plain,(
% 0.20/0.58    spl8_1 | spl8_2),
% 0.20/0.58    inference(avatar_split_clause,[],[f82,f90,f86])).
% 0.20/0.58  fof(f82,plain,(
% 0.20/0.58    v1_xboole_0(k1_xboole_0) | r1_tarski(k1_xboole_0,k1_xboole_0)),
% 0.20/0.58    inference(resolution,[],[f81,f61])).
% 0.20/0.58  fof(f61,plain,(
% 0.20/0.58    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f41])).
% 0.20/0.58  fof(f41,plain,(
% 0.20/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f39,f40])).
% 0.20/0.58  fof(f40,plain,(
% 0.20/0.58    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 0.20/0.58    introduced(choice_axiom,[])).
% 0.20/0.58  fof(f39,plain,(
% 0.20/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.58    inference(rectify,[],[f38])).
% 0.20/0.58  fof(f38,plain,(
% 0.20/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.58    inference(nnf_transformation,[],[f23])).
% 0.20/0.58  fof(f23,plain,(
% 0.20/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.58    inference(ennf_transformation,[],[f2])).
% 0.20/0.58  fof(f2,axiom,(
% 0.20/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.58  fof(f81,plain,(
% 0.20/0.58    ( ! [X0] : (~r2_hidden(sK7(X0,k1_xboole_0),k1_xboole_0) | v1_xboole_0(X0)) )),
% 0.20/0.58    inference(resolution,[],[f80,f48])).
% 0.20/0.58  fof(f80,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(sK7(X0,X1),X1) | v1_xboole_0(X0)) )),
% 0.20/0.58    inference(resolution,[],[f62,f59])).
% 0.20/0.58  fof(f62,plain,(
% 0.20/0.58    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK7(X0,X1),X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f41])).
% 0.20/0.58  % SZS output end Proof for theBenchmark
% 0.20/0.58  % (7249)------------------------------
% 0.20/0.58  % (7249)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (7249)Termination reason: Refutation
% 0.20/0.58  
% 0.20/0.58  % (7249)Memory used [KB]: 6780
% 0.20/0.58  % (7249)Time elapsed: 0.170 s
% 0.20/0.58  % (7249)------------------------------
% 0.20/0.58  % (7249)------------------------------
% 0.20/0.58  % (7236)Success in time 0.224 s
%------------------------------------------------------------------------------
