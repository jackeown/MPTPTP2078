%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:31 EST 2020

% Result     : Theorem 1.95s
% Output     : Refutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 637 expanded)
%              Number of leaves         :   32 ( 194 expanded)
%              Depth                    :   20
%              Number of atoms          :  520 (2286 expanded)
%              Number of equality atoms :  217 (1287 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2153,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f475,f1146,f1800,f1833,f1940,f2009,f2069,f2103,f2120,f2126,f2136,f2146,f2152])).

fof(f2152,plain,
    ( ~ spl11_1
    | spl11_11
    | ~ spl11_19
    | ~ spl11_22 ),
    inference(avatar_contradiction_clause,[],[f2151])).

fof(f2151,plain,
    ( $false
    | ~ spl11_1
    | spl11_11
    | ~ spl11_19
    | ~ spl11_22 ),
    inference(subsumption_resolution,[],[f2150,f1862])).

fof(f1862,plain,
    ( r2_hidden(k2_mcart_1(sK6),sK4)
    | ~ spl11_1 ),
    inference(resolution,[],[f103,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f103,plain,
    ( r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl11_1
  <=> r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f2150,plain,
    ( ~ r2_hidden(k2_mcart_1(sK6),sK4)
    | spl11_11
    | ~ spl11_19
    | ~ spl11_22 ),
    inference(resolution,[],[f2149,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f2149,plain,
    ( ~ m1_subset_1(k2_mcart_1(sK6),sK4)
    | spl11_11
    | ~ spl11_19
    | ~ spl11_22 ),
    inference(subsumption_resolution,[],[f2148,f474])).

fof(f474,plain,
    ( sK5 != k2_mcart_1(sK6)
    | spl11_11 ),
    inference(avatar_component_clause,[],[f472])).

fof(f472,plain,
    ( spl11_11
  <=> sK5 = k2_mcart_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f2148,plain,
    ( sK5 = k2_mcart_1(sK6)
    | ~ m1_subset_1(k2_mcart_1(sK6),sK4)
    | ~ spl11_19
    | ~ spl11_22 ),
    inference(trivial_inequality_removal,[],[f2147])).

fof(f2147,plain,
    ( sK6 != sK6
    | sK5 = k2_mcart_1(sK6)
    | ~ m1_subset_1(k2_mcart_1(sK6),sK4)
    | ~ spl11_19
    | ~ spl11_22 ),
    inference(superposition,[],[f2034,f1939])).

fof(f1939,plain,
    ( sK6 = k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6))
    | ~ spl11_19 ),
    inference(avatar_component_clause,[],[f1937])).

fof(f1937,plain,
    ( spl11_19
  <=> sK6 = k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).

fof(f2034,plain,
    ( ! [X0] :
        ( sK6 != k4_tarski(k1_mcart_1(sK6),X0)
        | sK5 = X0
        | ~ m1_subset_1(X0,sK4) )
    | ~ spl11_22 ),
    inference(avatar_component_clause,[],[f2033])).

fof(f2033,plain,
    ( spl11_22
  <=> ! [X0] :
        ( sK5 = X0
        | sK6 != k4_tarski(k1_mcart_1(sK6),X0)
        | ~ m1_subset_1(X0,sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_22])])).

fof(f2146,plain,
    ( spl11_22
    | ~ spl11_1
    | ~ spl11_20
    | ~ spl11_25
    | ~ spl11_26 ),
    inference(avatar_split_clause,[],[f2145,f2131,f2123,f2025,f101,f2033])).

fof(f2025,plain,
    ( spl11_20
  <=> m1_subset_1(sK9(k1_mcart_1(sK6)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f2123,plain,
    ( spl11_25
  <=> k1_mcart_1(sK6) = k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_25])])).

fof(f2131,plain,
    ( spl11_26
  <=> m1_subset_1(k2_mcart_1(k1_mcart_1(sK6)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_26])])).

fof(f2145,plain,
    ( ! [X0] :
        ( sK6 != k4_tarski(k1_mcart_1(sK6),X0)
        | sK5 = X0
        | ~ m1_subset_1(X0,sK4) )
    | ~ spl11_1
    | ~ spl11_20
    | ~ spl11_25
    | ~ spl11_26 ),
    inference(subsumption_resolution,[],[f2144,f2078])).

fof(f2078,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK6)),sK2)
    | ~ spl11_1
    | ~ spl11_20 ),
    inference(forward_demodulation,[],[f2026,f2012])).

fof(f2012,plain,
    ( k1_mcart_1(k1_mcart_1(sK6)) = sK9(k1_mcart_1(sK6))
    | ~ spl11_1 ),
    inference(resolution,[],[f1863,f371])).

fof(f371,plain,(
    ! [X8,X7,X9] :
      ( ~ r2_hidden(X7,k2_zfmisc_1(X8,X9))
      | k1_mcart_1(X7) = sK9(X7) ) ),
    inference(superposition,[],[f60,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(sK9(X0),sK10(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k4_tarski(sK9(X0),sK10(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f25,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
     => k4_tarski(sK9(X0),sK10(X0)) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X0
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(f60,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f1863,plain,
    ( r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK2,sK3))
    | ~ spl11_1 ),
    inference(resolution,[],[f103,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2026,plain,
    ( m1_subset_1(sK9(k1_mcart_1(sK6)),sK2)
    | ~ spl11_20 ),
    inference(avatar_component_clause,[],[f2025])).

fof(f2144,plain,
    ( ! [X0] :
        ( sK6 != k4_tarski(k1_mcart_1(sK6),X0)
        | sK5 = X0
        | ~ m1_subset_1(X0,sK4)
        | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK6)),sK2) )
    | ~ spl11_25
    | ~ spl11_26 ),
    inference(subsumption_resolution,[],[f2143,f2132])).

fof(f2132,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK6)),sK3)
    | ~ spl11_26 ),
    inference(avatar_component_clause,[],[f2131])).

fof(f2143,plain,
    ( ! [X0] :
        ( sK6 != k4_tarski(k1_mcart_1(sK6),X0)
        | sK5 = X0
        | ~ m1_subset_1(X0,sK4)
        | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK6)),sK3)
        | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK6)),sK2) )
    | ~ spl11_25 ),
    inference(superposition,[],[f80,f2125])).

fof(f2125,plain,
    ( k1_mcart_1(sK6) = k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6)))
    | ~ spl11_25 ),
    inference(avatar_component_clause,[],[f2123])).

fof(f80,plain,(
    ! [X6,X7,X5] :
      ( sK6 != k4_tarski(k4_tarski(X5,X6),X7)
      | sK5 = X7
      | ~ m1_subset_1(X7,sK4)
      | ~ m1_subset_1(X6,sK3)
      | ~ m1_subset_1(X5,sK2) ) ),
    inference(definition_unfolding,[],[f47,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f47,plain,(
    ! [X6,X7,X5] :
      ( sK5 = X7
      | k3_mcart_1(X5,X6,X7) != sK6
      | ~ m1_subset_1(X7,sK4)
      | ~ m1_subset_1(X6,sK3)
      | ~ m1_subset_1(X5,sK2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( sK5 != k7_mcart_1(sK2,sK3,sK4,sK6)
    & k1_xboole_0 != sK4
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK5 = X7
                | k3_mcart_1(X5,X6,X7) != sK6
                | ~ m1_subset_1(X7,sK4) )
            | ~ m1_subset_1(X6,sK3) )
        | ~ m1_subset_1(X5,sK2) )
    & m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f18,f30])).

fof(f30,plain,
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
   => ( sK5 != k7_mcart_1(sK2,sK3,sK4,sK6)
      & k1_xboole_0 != sK4
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK5 = X7
                  | k3_mcart_1(X5,X6,X7) != sK6
                  | ~ m1_subset_1(X7,sK4) )
              | ~ m1_subset_1(X6,sK3) )
          | ~ m1_subset_1(X5,sK2) )
      & m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4)) ) ),
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

fof(f2136,plain,
    ( spl11_26
    | ~ spl11_1
    | ~ spl11_21 ),
    inference(avatar_split_clause,[],[f2135,f2029,f101,f2131])).

fof(f2029,plain,
    ( spl11_21
  <=> m1_subset_1(sK10(k1_mcart_1(sK6)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_21])])).

fof(f2135,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK6)),sK3)
    | ~ spl11_1
    | ~ spl11_21 ),
    inference(forward_demodulation,[],[f2030,f2013])).

fof(f2013,plain,
    ( k2_mcart_1(k1_mcart_1(sK6)) = sK10(k1_mcart_1(sK6))
    | ~ spl11_1 ),
    inference(resolution,[],[f1863,f370])).

fof(f370,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(X4,k2_zfmisc_1(X5,X6))
      | k2_mcart_1(X4) = sK10(X4) ) ),
    inference(superposition,[],[f61,f72])).

fof(f61,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f14])).

fof(f2030,plain,
    ( m1_subset_1(sK10(k1_mcart_1(sK6)),sK3)
    | ~ spl11_21 ),
    inference(avatar_component_clause,[],[f2029])).

fof(f2126,plain,
    ( spl11_23
    | spl11_25
    | ~ spl11_1 ),
    inference(avatar_split_clause,[],[f2121,f101,f2123,f2071])).

fof(f2071,plain,
    ( spl11_23
  <=> ! [X1,X0] : ~ r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_23])])).

fof(f2121,plain,
    ( ! [X0,X1] :
        ( k1_mcart_1(sK6) = k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6)))
        | ~ r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(X0,X1)) )
    | ~ spl11_1 ),
    inference(forward_demodulation,[],[f2118,f2012])).

fof(f2118,plain,
    ( ! [X0,X1] :
        ( k1_mcart_1(sK6) = k4_tarski(sK9(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6)))
        | ~ r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(X0,X1)) )
    | ~ spl11_1 ),
    inference(superposition,[],[f72,f2013])).

fof(f2120,plain,
    ( ~ spl11_1
    | spl11_21 ),
    inference(avatar_contradiction_clause,[],[f2119])).

fof(f2119,plain,
    ( $false
    | ~ spl11_1
    | spl11_21 ),
    inference(subsumption_resolution,[],[f2116,f2015])).

fof(f2015,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK3)
    | ~ spl11_1 ),
    inference(resolution,[],[f1863,f67])).

fof(f2116,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK3)
    | ~ spl11_1
    | spl11_21 ),
    inference(backward_demodulation,[],[f2079,f2013])).

fof(f2079,plain,
    ( ~ r2_hidden(sK10(k1_mcart_1(sK6)),sK3)
    | spl11_21 ),
    inference(resolution,[],[f2031,f63])).

fof(f2031,plain,
    ( ~ m1_subset_1(sK10(k1_mcart_1(sK6)),sK3)
    | spl11_21 ),
    inference(avatar_component_clause,[],[f2029])).

fof(f2103,plain,
    ( ~ spl11_1
    | ~ spl11_23 ),
    inference(avatar_contradiction_clause,[],[f2081])).

fof(f2081,plain,
    ( $false
    | ~ spl11_1
    | ~ spl11_23 ),
    inference(subsumption_resolution,[],[f1863,f2072])).

fof(f2072,plain,
    ( ! [X0,X1] : ~ r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(X0,X1))
    | ~ spl11_23 ),
    inference(avatar_component_clause,[],[f2071])).

fof(f2069,plain,
    ( ~ spl11_1
    | spl11_20 ),
    inference(avatar_contradiction_clause,[],[f2068])).

fof(f2068,plain,
    ( $false
    | ~ spl11_1
    | spl11_20 ),
    inference(subsumption_resolution,[],[f2065,f2016])).

fof(f2016,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK2)
    | ~ spl11_1 ),
    inference(resolution,[],[f1863,f66])).

fof(f2065,plain,
    ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK2)
    | ~ spl11_1
    | spl11_20 ),
    inference(backward_demodulation,[],[f2063,f2012])).

fof(f2063,plain,
    ( ~ r2_hidden(sK9(k1_mcart_1(sK6)),sK2)
    | spl11_20 ),
    inference(resolution,[],[f2027,f63])).

fof(f2027,plain,
    ( ~ m1_subset_1(sK9(k1_mcart_1(sK6)),sK2)
    | spl11_20 ),
    inference(avatar_component_clause,[],[f2025])).

fof(f2009,plain,
    ( ~ spl11_1
    | ~ spl11_17 ),
    inference(avatar_contradiction_clause,[],[f1987])).

fof(f1987,plain,
    ( $false
    | ~ spl11_1
    | ~ spl11_17 ),
    inference(subsumption_resolution,[],[f103,f1928])).

fof(f1928,plain,
    ( ! [X0,X1] : ~ r2_hidden(sK6,k2_zfmisc_1(X0,X1))
    | ~ spl11_17 ),
    inference(avatar_component_clause,[],[f1927])).

fof(f1927,plain,
    ( spl11_17
  <=> ! [X1,X0] : ~ r2_hidden(sK6,k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).

fof(f1940,plain,
    ( spl11_17
    | spl11_19
    | ~ spl11_1 ),
    inference(avatar_split_clause,[],[f1935,f101,f1937,f1927])).

fof(f1935,plain,
    ( ! [X0,X1] :
        ( sK6 = k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6))
        | ~ r2_hidden(sK6,k2_zfmisc_1(X0,X1)) )
    | ~ spl11_1 ),
    inference(forward_demodulation,[],[f1934,f1859])).

fof(f1859,plain,
    ( k1_mcart_1(sK6) = sK9(sK6)
    | ~ spl11_1 ),
    inference(resolution,[],[f103,f371])).

fof(f1934,plain,
    ( ! [X0,X1] :
        ( sK6 = k4_tarski(sK9(sK6),k2_mcart_1(sK6))
        | ~ r2_hidden(sK6,k2_zfmisc_1(X0,X1)) )
    | ~ spl11_1 ),
    inference(superposition,[],[f72,f1860])).

fof(f1860,plain,
    ( k2_mcart_1(sK6) = sK10(sK6)
    | ~ spl11_1 ),
    inference(resolution,[],[f103,f370])).

fof(f1833,plain,
    ( spl11_1
    | spl11_2 ),
    inference(avatar_split_clause,[],[f1816,f105,f101])).

fof(f105,plain,
    ( spl11_2
  <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f1816,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))
    | r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
    inference(resolution,[],[f81,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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

fof(f81,plain,(
    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
    inference(definition_unfolding,[],[f46,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f46,plain,(
    m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f31])).

fof(f1800,plain,(
    ~ spl11_2 ),
    inference(avatar_contradiction_clause,[],[f1799])).

fof(f1799,plain,
    ( $false
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f1798,f49])).

fof(f49,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f31])).

fof(f1798,plain,
    ( k1_xboole_0 = sK3
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f1797,f48])).

fof(f48,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f31])).

fof(f1797,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f1781,f52])).

fof(f52,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f1781,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | ~ spl11_2 ),
    inference(superposition,[],[f1342,f1749])).

fof(f1749,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK2,sK3)
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f1702,f50])).

fof(f50,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f31])).

fof(f1702,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK2,sK3)
    | k1_xboole_0 = sK4
    | ~ spl11_2 ),
    inference(resolution,[],[f1342,f107])).

fof(f107,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f105])).

fof(f1342,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X1,X0))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(condensation,[],[f1341])).

fof(f1341,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | ~ v1_xboole_0(k2_zfmisc_1(X1,X2)) ) ),
    inference(subsumption_resolution,[],[f1295,f277])).

fof(f277,plain,(
    ! [X15,X16] :
      ( k1_xboole_0 = k2_zfmisc_1(X15,X16)
      | ~ v1_xboole_0(X15) ) ),
    inference(duplicate_literal_removal,[],[f264])).

fof(f264,plain,(
    ! [X15,X16] :
      ( k1_xboole_0 = k2_zfmisc_1(X15,X16)
      | ~ v1_xboole_0(X15)
      | ~ v1_xboole_0(X15) ) ),
    inference(superposition,[],[f197,f133])).

fof(f133,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f121,f95])).

fof(f95,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f58,f54])).

fof(f54,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK7(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f33,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK7(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
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

fof(f58,plain,(
    ! [X0] :
      ( r2_hidden(sK8(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( sP0(sK8(X0),X0)
        & r2_hidden(sK8(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f27,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( sP0(X1,X0)
          & r2_hidden(X1,X0) )
     => ( sP0(sK8(X0),X0)
        & r2_hidden(sK8(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( sP0(X1,X0)
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(definition_folding,[],[f19,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ! [X2,X3,X4,X5] :
          ( k4_mcart_1(X2,X3,X4,X5) != X1
          | ( ~ r2_hidden(X3,X0)
            & ~ r2_hidden(X2,X0) ) )
      | ~ sP0(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).

fof(f121,plain,(
    ! [X3] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X3) ),
    inference(superposition,[],[f91,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X3
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f78,f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f73,f65])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X3
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f44,plain,(
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

fof(f91,plain,(
    ! [X0,X3,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f77,f79])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f197,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f91,f127])).

fof(f127,plain,(
    ! [X0] :
      ( k2_zfmisc_1(X0,X0) = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f114,f95])).

fof(f114,plain,(
    k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f90,f90])).

fof(f1295,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X1,X2),X0)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | ~ v1_xboole_0(k2_zfmisc_1(X1,X2)) ) ),
    inference(condensation,[],[f1270])).

fof(f1270,plain,(
    ! [X59,X57,X60,X58] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X57,X58),X60)
      | k1_xboole_0 = X60
      | k1_xboole_0 = X59
      | k1_xboole_0 = X58
      | k1_xboole_0 = X57
      | ~ v1_xboole_0(k2_zfmisc_1(X57,X58)) ) ),
    inference(superposition,[],[f87,f133])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f74,f79])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f1146,plain,(
    spl11_10 ),
    inference(avatar_split_clause,[],[f1145,f468])).

fof(f468,plain,
    ( spl11_10
  <=> sP1(sK6,sK4,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f1145,plain,(
    sP1(sK6,sK4,sK3,sK2) ),
    inference(subsumption_resolution,[],[f1144,f48])).

fof(f1144,plain,
    ( sP1(sK6,sK4,sK3,sK2)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f1143,f49])).

fof(f1143,plain,
    ( sP1(sK6,sK4,sK3,sK2)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f1104,f50])).

fof(f1104,plain,
    ( sP1(sK6,sK4,sK3,sK2)
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f82,f81])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | sP1(X3,X2,X1,X0)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f71,f65])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X3,X2,X1,X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( sP1(X3,X2,X1,X0)
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_folding,[],[f24,f28])).

fof(f28,plain,(
    ! [X3,X2,X1,X0] :
      ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
        & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
        & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
      | ~ sP1(X3,X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f24,plain,(
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

fof(f475,plain,
    ( ~ spl11_10
    | ~ spl11_11 ),
    inference(avatar_split_clause,[],[f466,f472,f468])).

fof(f466,plain,
    ( sK5 != k2_mcart_1(sK6)
    | ~ sP1(sK6,sK4,sK3,sK2) ),
    inference(superposition,[],[f51,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X0) = k7_mcart_1(X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k2_mcart_1(X0) = k7_mcart_1(X3,X2,X1,X0)
        & k6_mcart_1(X3,X2,X1,X0) = k2_mcart_1(k1_mcart_1(X0))
        & k5_mcart_1(X3,X2,X1,X0) = k1_mcart_1(k1_mcart_1(X0)) )
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X3,X2,X1,X0] :
      ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
        & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
        & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
      | ~ sP1(X3,X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f51,plain,(
    sK5 != k7_mcart_1(sK2,sK3,sK4,sK6) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:20:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (8937)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (8955)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (8947)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (8955)Refutation not found, incomplete strategy% (8955)------------------------------
% 0.21/0.52  % (8955)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (8939)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (8955)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (8955)Memory used [KB]: 1791
% 0.21/0.52  % (8955)Time elapsed: 0.060 s
% 0.21/0.52  % (8955)------------------------------
% 0.21/0.52  % (8955)------------------------------
% 1.29/0.54  % (8936)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.29/0.54  % (8937)Refutation not found, incomplete strategy% (8937)------------------------------
% 1.29/0.54  % (8937)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (8937)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (8937)Memory used [KB]: 6396
% 1.29/0.54  % (8937)Time elapsed: 0.130 s
% 1.29/0.54  % (8937)------------------------------
% 1.29/0.54  % (8937)------------------------------
% 1.29/0.54  % (8961)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.29/0.54  % (8959)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.29/0.54  % (8934)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.29/0.54  % (8933)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.40/0.54  % (8934)Refutation not found, incomplete strategy% (8934)------------------------------
% 1.40/0.54  % (8934)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  % (8934)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.54  
% 1.40/0.54  % (8934)Memory used [KB]: 10746
% 1.40/0.54  % (8934)Time elapsed: 0.134 s
% 1.40/0.54  % (8934)------------------------------
% 1.40/0.54  % (8934)------------------------------
% 1.40/0.54  % (8935)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.40/0.54  % (8941)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.40/0.54  % (8942)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.40/0.55  % (8953)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.40/0.55  % (8942)Refutation not found, incomplete strategy% (8942)------------------------------
% 1.40/0.55  % (8942)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (8942)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (8942)Memory used [KB]: 10618
% 1.40/0.55  % (8942)Time elapsed: 0.132 s
% 1.40/0.55  % (8942)------------------------------
% 1.40/0.55  % (8942)------------------------------
% 1.40/0.55  % (8932)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.40/0.55  % (8953)Refutation not found, incomplete strategy% (8953)------------------------------
% 1.40/0.55  % (8953)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (8953)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (8953)Memory used [KB]: 1791
% 1.40/0.55  % (8953)Time elapsed: 0.142 s
% 1.40/0.55  % (8953)------------------------------
% 1.40/0.55  % (8953)------------------------------
% 1.40/0.55  % (8960)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.40/0.55  % (8945)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.40/0.55  % (8958)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.40/0.55  % (8951)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.40/0.55  % (8952)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.40/0.55  % (8957)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.40/0.56  % (8952)Refutation not found, incomplete strategy% (8952)------------------------------
% 1.40/0.56  % (8952)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.56  % (8952)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.56  
% 1.40/0.56  % (8952)Memory used [KB]: 10746
% 1.40/0.56  % (8952)Time elapsed: 0.148 s
% 1.40/0.56  % (8952)------------------------------
% 1.40/0.56  % (8952)------------------------------
% 1.40/0.56  % (8950)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.40/0.56  % (8944)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.40/0.56  % (8943)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.40/0.56  % (8949)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.40/0.56  % (8948)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.40/0.56  % (8956)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.40/0.57  % (8940)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.40/0.57  % (8940)Refutation not found, incomplete strategy% (8940)------------------------------
% 1.40/0.57  % (8940)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.57  % (8940)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.57  
% 1.40/0.57  % (8940)Memory used [KB]: 10746
% 1.40/0.57  % (8940)Time elapsed: 0.168 s
% 1.40/0.57  % (8940)------------------------------
% 1.40/0.57  % (8940)------------------------------
% 1.40/0.57  % (8938)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.40/0.59  % (8954)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.40/0.59  % (8946)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.40/0.60  % (8954)Refutation not found, incomplete strategy% (8954)------------------------------
% 1.40/0.60  % (8954)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.62  % (8954)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.62  
% 1.40/0.62  % (8954)Memory used [KB]: 10874
% 1.40/0.62  % (8954)Time elapsed: 0.164 s
% 1.40/0.62  % (8954)------------------------------
% 1.40/0.62  % (8954)------------------------------
% 1.95/0.68  % (8965)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.95/0.68  % (8959)Refutation found. Thanks to Tanya!
% 1.95/0.68  % SZS status Theorem for theBenchmark
% 1.95/0.68  % SZS output start Proof for theBenchmark
% 1.95/0.68  fof(f2153,plain,(
% 1.95/0.68    $false),
% 1.95/0.68    inference(avatar_sat_refutation,[],[f475,f1146,f1800,f1833,f1940,f2009,f2069,f2103,f2120,f2126,f2136,f2146,f2152])).
% 1.95/0.68  fof(f2152,plain,(
% 1.95/0.68    ~spl11_1 | spl11_11 | ~spl11_19 | ~spl11_22),
% 1.95/0.68    inference(avatar_contradiction_clause,[],[f2151])).
% 1.95/0.68  fof(f2151,plain,(
% 1.95/0.68    $false | (~spl11_1 | spl11_11 | ~spl11_19 | ~spl11_22)),
% 1.95/0.68    inference(subsumption_resolution,[],[f2150,f1862])).
% 1.95/0.68  fof(f1862,plain,(
% 1.95/0.68    r2_hidden(k2_mcart_1(sK6),sK4) | ~spl11_1),
% 1.95/0.68    inference(resolution,[],[f103,f67])).
% 1.95/0.68  fof(f67,plain,(
% 1.95/0.68    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 1.95/0.68    inference(cnf_transformation,[],[f23])).
% 1.95/0.68  fof(f23,plain,(
% 1.95/0.68    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.95/0.68    inference(ennf_transformation,[],[f10])).
% 1.95/0.68  fof(f10,axiom,(
% 1.95/0.68    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.95/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.95/0.68  fof(f103,plain,(
% 1.95/0.68    r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) | ~spl11_1),
% 1.95/0.68    inference(avatar_component_clause,[],[f101])).
% 1.95/0.68  fof(f101,plain,(
% 1.95/0.68    spl11_1 <=> r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))),
% 1.95/0.68    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 1.95/0.68  fof(f2150,plain,(
% 1.95/0.68    ~r2_hidden(k2_mcart_1(sK6),sK4) | (spl11_11 | ~spl11_19 | ~spl11_22)),
% 1.95/0.68    inference(resolution,[],[f2149,f63])).
% 1.95/0.68  fof(f63,plain,(
% 1.95/0.68    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.95/0.68    inference(cnf_transformation,[],[f22])).
% 1.95/0.68  fof(f22,plain,(
% 1.95/0.68    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.95/0.68    inference(ennf_transformation,[],[f5])).
% 1.95/0.68  fof(f5,axiom,(
% 1.95/0.68    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.95/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.95/0.68  fof(f2149,plain,(
% 1.95/0.68    ~m1_subset_1(k2_mcart_1(sK6),sK4) | (spl11_11 | ~spl11_19 | ~spl11_22)),
% 1.95/0.68    inference(subsumption_resolution,[],[f2148,f474])).
% 1.95/0.68  fof(f474,plain,(
% 1.95/0.68    sK5 != k2_mcart_1(sK6) | spl11_11),
% 1.95/0.68    inference(avatar_component_clause,[],[f472])).
% 1.95/0.68  fof(f472,plain,(
% 1.95/0.68    spl11_11 <=> sK5 = k2_mcart_1(sK6)),
% 1.95/0.68    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).
% 1.95/0.68  fof(f2148,plain,(
% 1.95/0.68    sK5 = k2_mcart_1(sK6) | ~m1_subset_1(k2_mcart_1(sK6),sK4) | (~spl11_19 | ~spl11_22)),
% 1.95/0.68    inference(trivial_inequality_removal,[],[f2147])).
% 1.95/0.68  fof(f2147,plain,(
% 1.95/0.68    sK6 != sK6 | sK5 = k2_mcart_1(sK6) | ~m1_subset_1(k2_mcart_1(sK6),sK4) | (~spl11_19 | ~spl11_22)),
% 1.95/0.68    inference(superposition,[],[f2034,f1939])).
% 1.95/0.68  fof(f1939,plain,(
% 1.95/0.68    sK6 = k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) | ~spl11_19),
% 1.95/0.68    inference(avatar_component_clause,[],[f1937])).
% 1.95/0.68  fof(f1937,plain,(
% 1.95/0.68    spl11_19 <=> sK6 = k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6))),
% 1.95/0.68    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).
% 1.95/0.68  fof(f2034,plain,(
% 1.95/0.68    ( ! [X0] : (sK6 != k4_tarski(k1_mcart_1(sK6),X0) | sK5 = X0 | ~m1_subset_1(X0,sK4)) ) | ~spl11_22),
% 1.95/0.68    inference(avatar_component_clause,[],[f2033])).
% 1.95/0.68  fof(f2033,plain,(
% 1.95/0.68    spl11_22 <=> ! [X0] : (sK5 = X0 | sK6 != k4_tarski(k1_mcart_1(sK6),X0) | ~m1_subset_1(X0,sK4))),
% 1.95/0.68    introduced(avatar_definition,[new_symbols(naming,[spl11_22])])).
% 1.95/0.68  fof(f2146,plain,(
% 1.95/0.68    spl11_22 | ~spl11_1 | ~spl11_20 | ~spl11_25 | ~spl11_26),
% 1.95/0.68    inference(avatar_split_clause,[],[f2145,f2131,f2123,f2025,f101,f2033])).
% 1.95/0.68  fof(f2025,plain,(
% 1.95/0.68    spl11_20 <=> m1_subset_1(sK9(k1_mcart_1(sK6)),sK2)),
% 1.95/0.68    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).
% 1.95/0.68  fof(f2123,plain,(
% 1.95/0.68    spl11_25 <=> k1_mcart_1(sK6) = k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6)))),
% 1.95/0.68    introduced(avatar_definition,[new_symbols(naming,[spl11_25])])).
% 1.95/0.68  fof(f2131,plain,(
% 1.95/0.68    spl11_26 <=> m1_subset_1(k2_mcart_1(k1_mcart_1(sK6)),sK3)),
% 1.95/0.68    introduced(avatar_definition,[new_symbols(naming,[spl11_26])])).
% 1.95/0.68  fof(f2145,plain,(
% 1.95/0.68    ( ! [X0] : (sK6 != k4_tarski(k1_mcart_1(sK6),X0) | sK5 = X0 | ~m1_subset_1(X0,sK4)) ) | (~spl11_1 | ~spl11_20 | ~spl11_25 | ~spl11_26)),
% 1.95/0.68    inference(subsumption_resolution,[],[f2144,f2078])).
% 1.95/0.68  fof(f2078,plain,(
% 1.95/0.68    m1_subset_1(k1_mcart_1(k1_mcart_1(sK6)),sK2) | (~spl11_1 | ~spl11_20)),
% 1.95/0.68    inference(forward_demodulation,[],[f2026,f2012])).
% 1.95/0.68  fof(f2012,plain,(
% 1.95/0.68    k1_mcart_1(k1_mcart_1(sK6)) = sK9(k1_mcart_1(sK6)) | ~spl11_1),
% 1.95/0.68    inference(resolution,[],[f1863,f371])).
% 1.95/0.68  fof(f371,plain,(
% 1.95/0.68    ( ! [X8,X7,X9] : (~r2_hidden(X7,k2_zfmisc_1(X8,X9)) | k1_mcart_1(X7) = sK9(X7)) )),
% 1.95/0.68    inference(superposition,[],[f60,f72])).
% 1.95/0.68  fof(f72,plain,(
% 1.95/0.68    ( ! [X2,X0,X1] : (k4_tarski(sK9(X0),sK10(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 1.95/0.68    inference(cnf_transformation,[],[f43])).
% 1.95/0.68  fof(f43,plain,(
% 1.95/0.68    ! [X0,X1,X2] : (k4_tarski(sK9(X0),sK10(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.95/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f25,f42])).
% 1.95/0.68  fof(f42,plain,(
% 1.95/0.68    ! [X0] : (? [X3,X4] : k4_tarski(X3,X4) = X0 => k4_tarski(sK9(X0),sK10(X0)) = X0)),
% 1.95/0.68    introduced(choice_axiom,[])).
% 1.95/0.68  fof(f25,plain,(
% 1.95/0.68    ! [X0,X1,X2] : (? [X3,X4] : k4_tarski(X3,X4) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.95/0.68    inference(ennf_transformation,[],[f3])).
% 1.95/0.68  fof(f3,axiom,(
% 1.95/0.68    ! [X0,X1,X2] : ~(! [X3,X4] : k4_tarski(X3,X4) != X0 & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.95/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).
% 1.95/0.68  fof(f60,plain,(
% 1.95/0.68    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 1.95/0.68    inference(cnf_transformation,[],[f14])).
% 1.95/0.68  fof(f14,axiom,(
% 1.95/0.68    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 1.95/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 1.95/0.68  fof(f1863,plain,(
% 1.95/0.68    r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK2,sK3)) | ~spl11_1),
% 1.95/0.68    inference(resolution,[],[f103,f66])).
% 1.95/0.68  fof(f66,plain,(
% 1.95/0.68    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 1.95/0.68    inference(cnf_transformation,[],[f23])).
% 1.95/0.68  fof(f2026,plain,(
% 1.95/0.68    m1_subset_1(sK9(k1_mcart_1(sK6)),sK2) | ~spl11_20),
% 1.95/0.68    inference(avatar_component_clause,[],[f2025])).
% 1.95/0.68  fof(f2144,plain,(
% 1.95/0.68    ( ! [X0] : (sK6 != k4_tarski(k1_mcart_1(sK6),X0) | sK5 = X0 | ~m1_subset_1(X0,sK4) | ~m1_subset_1(k1_mcart_1(k1_mcart_1(sK6)),sK2)) ) | (~spl11_25 | ~spl11_26)),
% 1.95/0.68    inference(subsumption_resolution,[],[f2143,f2132])).
% 1.95/0.68  fof(f2132,plain,(
% 1.95/0.68    m1_subset_1(k2_mcart_1(k1_mcart_1(sK6)),sK3) | ~spl11_26),
% 1.95/0.68    inference(avatar_component_clause,[],[f2131])).
% 1.95/0.68  fof(f2143,plain,(
% 1.95/0.68    ( ! [X0] : (sK6 != k4_tarski(k1_mcart_1(sK6),X0) | sK5 = X0 | ~m1_subset_1(X0,sK4) | ~m1_subset_1(k2_mcart_1(k1_mcart_1(sK6)),sK3) | ~m1_subset_1(k1_mcart_1(k1_mcart_1(sK6)),sK2)) ) | ~spl11_25),
% 1.95/0.68    inference(superposition,[],[f80,f2125])).
% 1.95/0.68  fof(f2125,plain,(
% 1.95/0.68    k1_mcart_1(sK6) = k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))) | ~spl11_25),
% 1.95/0.68    inference(avatar_component_clause,[],[f2123])).
% 1.95/0.68  fof(f80,plain,(
% 1.95/0.68    ( ! [X6,X7,X5] : (sK6 != k4_tarski(k4_tarski(X5,X6),X7) | sK5 = X7 | ~m1_subset_1(X7,sK4) | ~m1_subset_1(X6,sK3) | ~m1_subset_1(X5,sK2)) )),
% 1.95/0.68    inference(definition_unfolding,[],[f47,f64])).
% 1.95/0.68  fof(f64,plain,(
% 1.95/0.68    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 1.95/0.68    inference(cnf_transformation,[],[f7])).
% 1.95/0.68  fof(f7,axiom,(
% 1.95/0.68    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 1.95/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 1.95/0.68  fof(f47,plain,(
% 1.95/0.68    ( ! [X6,X7,X5] : (sK5 = X7 | k3_mcart_1(X5,X6,X7) != sK6 | ~m1_subset_1(X7,sK4) | ~m1_subset_1(X6,sK3) | ~m1_subset_1(X5,sK2)) )),
% 1.95/0.68    inference(cnf_transformation,[],[f31])).
% 1.95/0.68  fof(f31,plain,(
% 1.95/0.68    sK5 != k7_mcart_1(sK2,sK3,sK4,sK6) & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & ! [X5] : (! [X6] : (! [X7] : (sK5 = X7 | k3_mcart_1(X5,X6,X7) != sK6 | ~m1_subset_1(X7,sK4)) | ~m1_subset_1(X6,sK3)) | ~m1_subset_1(X5,sK2)) & m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4))),
% 1.95/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f18,f30])).
% 1.95/0.68  fof(f30,plain,(
% 1.95/0.68    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (sK5 != k7_mcart_1(sK2,sK3,sK4,sK6) & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & ! [X5] : (! [X6] : (! [X7] : (sK5 = X7 | k3_mcart_1(X5,X6,X7) != sK6 | ~m1_subset_1(X7,sK4)) | ~m1_subset_1(X6,sK3)) | ~m1_subset_1(X5,sK2)) & m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4)))),
% 1.95/0.68    introduced(choice_axiom,[])).
% 1.95/0.68  fof(f18,plain,(
% 1.95/0.68    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 1.95/0.68    inference(flattening,[],[f17])).
% 1.95/0.68  fof(f17,plain,(
% 1.95/0.68    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 1.95/0.68    inference(ennf_transformation,[],[f16])).
% 1.95/0.68  fof(f16,negated_conjecture,(
% 1.95/0.68    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.95/0.68    inference(negated_conjecture,[],[f15])).
% 1.95/0.68  fof(f15,conjecture,(
% 1.95/0.68    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.95/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).
% 1.95/0.68  fof(f2136,plain,(
% 1.95/0.68    spl11_26 | ~spl11_1 | ~spl11_21),
% 1.95/0.68    inference(avatar_split_clause,[],[f2135,f2029,f101,f2131])).
% 1.95/0.68  fof(f2029,plain,(
% 1.95/0.68    spl11_21 <=> m1_subset_1(sK10(k1_mcart_1(sK6)),sK3)),
% 1.95/0.68    introduced(avatar_definition,[new_symbols(naming,[spl11_21])])).
% 1.95/0.68  fof(f2135,plain,(
% 1.95/0.68    m1_subset_1(k2_mcart_1(k1_mcart_1(sK6)),sK3) | (~spl11_1 | ~spl11_21)),
% 1.95/0.68    inference(forward_demodulation,[],[f2030,f2013])).
% 1.95/0.68  fof(f2013,plain,(
% 1.95/0.68    k2_mcart_1(k1_mcart_1(sK6)) = sK10(k1_mcart_1(sK6)) | ~spl11_1),
% 1.95/0.68    inference(resolution,[],[f1863,f370])).
% 1.95/0.68  fof(f370,plain,(
% 1.95/0.68    ( ! [X6,X4,X5] : (~r2_hidden(X4,k2_zfmisc_1(X5,X6)) | k2_mcart_1(X4) = sK10(X4)) )),
% 1.95/0.68    inference(superposition,[],[f61,f72])).
% 1.95/0.68  fof(f61,plain,(
% 1.95/0.68    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 1.95/0.68    inference(cnf_transformation,[],[f14])).
% 1.95/0.68  fof(f2030,plain,(
% 1.95/0.68    m1_subset_1(sK10(k1_mcart_1(sK6)),sK3) | ~spl11_21),
% 1.95/0.68    inference(avatar_component_clause,[],[f2029])).
% 1.95/0.68  fof(f2126,plain,(
% 1.95/0.68    spl11_23 | spl11_25 | ~spl11_1),
% 1.95/0.68    inference(avatar_split_clause,[],[f2121,f101,f2123,f2071])).
% 1.95/0.68  fof(f2071,plain,(
% 1.95/0.68    spl11_23 <=> ! [X1,X0] : ~r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(X0,X1))),
% 1.95/0.68    introduced(avatar_definition,[new_symbols(naming,[spl11_23])])).
% 1.95/0.68  fof(f2121,plain,(
% 1.95/0.68    ( ! [X0,X1] : (k1_mcart_1(sK6) = k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))) | ~r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(X0,X1))) ) | ~spl11_1),
% 1.95/0.68    inference(forward_demodulation,[],[f2118,f2012])).
% 1.95/0.68  fof(f2118,plain,(
% 1.95/0.68    ( ! [X0,X1] : (k1_mcart_1(sK6) = k4_tarski(sK9(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))) | ~r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(X0,X1))) ) | ~spl11_1),
% 1.95/0.68    inference(superposition,[],[f72,f2013])).
% 1.95/0.68  fof(f2120,plain,(
% 1.95/0.68    ~spl11_1 | spl11_21),
% 1.95/0.68    inference(avatar_contradiction_clause,[],[f2119])).
% 1.95/0.68  fof(f2119,plain,(
% 1.95/0.68    $false | (~spl11_1 | spl11_21)),
% 1.95/0.68    inference(subsumption_resolution,[],[f2116,f2015])).
% 1.95/0.68  fof(f2015,plain,(
% 1.95/0.68    r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK3) | ~spl11_1),
% 1.95/0.68    inference(resolution,[],[f1863,f67])).
% 1.95/0.68  fof(f2116,plain,(
% 1.95/0.68    ~r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK3) | (~spl11_1 | spl11_21)),
% 1.95/0.68    inference(backward_demodulation,[],[f2079,f2013])).
% 1.95/0.68  fof(f2079,plain,(
% 1.95/0.68    ~r2_hidden(sK10(k1_mcart_1(sK6)),sK3) | spl11_21),
% 1.95/0.68    inference(resolution,[],[f2031,f63])).
% 1.95/0.68  fof(f2031,plain,(
% 1.95/0.68    ~m1_subset_1(sK10(k1_mcart_1(sK6)),sK3) | spl11_21),
% 1.95/0.68    inference(avatar_component_clause,[],[f2029])).
% 1.95/0.68  fof(f2103,plain,(
% 1.95/0.68    ~spl11_1 | ~spl11_23),
% 1.95/0.68    inference(avatar_contradiction_clause,[],[f2081])).
% 1.95/0.68  fof(f2081,plain,(
% 1.95/0.68    $false | (~spl11_1 | ~spl11_23)),
% 1.95/0.68    inference(subsumption_resolution,[],[f1863,f2072])).
% 1.95/0.68  fof(f2072,plain,(
% 1.95/0.68    ( ! [X0,X1] : (~r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(X0,X1))) ) | ~spl11_23),
% 1.95/0.68    inference(avatar_component_clause,[],[f2071])).
% 1.95/0.68  fof(f2069,plain,(
% 1.95/0.68    ~spl11_1 | spl11_20),
% 1.95/0.68    inference(avatar_contradiction_clause,[],[f2068])).
% 1.95/0.68  fof(f2068,plain,(
% 1.95/0.68    $false | (~spl11_1 | spl11_20)),
% 1.95/0.68    inference(subsumption_resolution,[],[f2065,f2016])).
% 1.95/0.68  fof(f2016,plain,(
% 1.95/0.68    r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK2) | ~spl11_1),
% 1.95/0.68    inference(resolution,[],[f1863,f66])).
% 1.95/0.68  fof(f2065,plain,(
% 1.95/0.68    ~r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK2) | (~spl11_1 | spl11_20)),
% 1.95/0.68    inference(backward_demodulation,[],[f2063,f2012])).
% 1.95/0.68  fof(f2063,plain,(
% 1.95/0.68    ~r2_hidden(sK9(k1_mcart_1(sK6)),sK2) | spl11_20),
% 1.95/0.68    inference(resolution,[],[f2027,f63])).
% 1.95/0.68  fof(f2027,plain,(
% 1.95/0.68    ~m1_subset_1(sK9(k1_mcart_1(sK6)),sK2) | spl11_20),
% 1.95/0.68    inference(avatar_component_clause,[],[f2025])).
% 1.95/0.68  fof(f2009,plain,(
% 1.95/0.68    ~spl11_1 | ~spl11_17),
% 1.95/0.68    inference(avatar_contradiction_clause,[],[f1987])).
% 1.95/0.68  fof(f1987,plain,(
% 1.95/0.68    $false | (~spl11_1 | ~spl11_17)),
% 1.95/0.68    inference(subsumption_resolution,[],[f103,f1928])).
% 1.95/0.68  fof(f1928,plain,(
% 1.95/0.68    ( ! [X0,X1] : (~r2_hidden(sK6,k2_zfmisc_1(X0,X1))) ) | ~spl11_17),
% 1.95/0.68    inference(avatar_component_clause,[],[f1927])).
% 1.95/0.68  fof(f1927,plain,(
% 1.95/0.68    spl11_17 <=> ! [X1,X0] : ~r2_hidden(sK6,k2_zfmisc_1(X0,X1))),
% 1.95/0.68    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).
% 1.95/0.68  fof(f1940,plain,(
% 1.95/0.68    spl11_17 | spl11_19 | ~spl11_1),
% 1.95/0.68    inference(avatar_split_clause,[],[f1935,f101,f1937,f1927])).
% 1.95/0.68  fof(f1935,plain,(
% 1.95/0.68    ( ! [X0,X1] : (sK6 = k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) | ~r2_hidden(sK6,k2_zfmisc_1(X0,X1))) ) | ~spl11_1),
% 1.95/0.68    inference(forward_demodulation,[],[f1934,f1859])).
% 1.95/0.68  fof(f1859,plain,(
% 1.95/0.68    k1_mcart_1(sK6) = sK9(sK6) | ~spl11_1),
% 1.95/0.68    inference(resolution,[],[f103,f371])).
% 1.95/0.68  fof(f1934,plain,(
% 1.95/0.68    ( ! [X0,X1] : (sK6 = k4_tarski(sK9(sK6),k2_mcart_1(sK6)) | ~r2_hidden(sK6,k2_zfmisc_1(X0,X1))) ) | ~spl11_1),
% 1.95/0.68    inference(superposition,[],[f72,f1860])).
% 1.95/0.68  fof(f1860,plain,(
% 1.95/0.68    k2_mcart_1(sK6) = sK10(sK6) | ~spl11_1),
% 1.95/0.68    inference(resolution,[],[f103,f370])).
% 1.95/0.68  fof(f1833,plain,(
% 1.95/0.68    spl11_1 | spl11_2),
% 1.95/0.68    inference(avatar_split_clause,[],[f1816,f105,f101])).
% 1.95/0.68  fof(f105,plain,(
% 1.95/0.68    spl11_2 <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))),
% 1.95/0.68    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 1.95/0.68  fof(f1816,plain,(
% 1.95/0.68    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) | r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))),
% 1.95/0.68    inference(resolution,[],[f81,f62])).
% 1.95/0.68  fof(f62,plain,(
% 1.95/0.68    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.95/0.68    inference(cnf_transformation,[],[f21])).
% 1.95/0.68  fof(f21,plain,(
% 1.95/0.68    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.95/0.68    inference(flattening,[],[f20])).
% 1.95/0.68  fof(f20,plain,(
% 1.95/0.68    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.95/0.68    inference(ennf_transformation,[],[f6])).
% 1.95/0.68  fof(f6,axiom,(
% 1.95/0.68    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.95/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.95/0.68  fof(f81,plain,(
% 1.95/0.68    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))),
% 1.95/0.68    inference(definition_unfolding,[],[f46,f65])).
% 1.95/0.68  fof(f65,plain,(
% 1.95/0.68    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.95/0.68    inference(cnf_transformation,[],[f8])).
% 1.95/0.68  fof(f8,axiom,(
% 1.95/0.68    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.95/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.95/0.68  fof(f46,plain,(
% 1.95/0.68    m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4))),
% 1.95/0.68    inference(cnf_transformation,[],[f31])).
% 1.95/0.68  fof(f1800,plain,(
% 1.95/0.68    ~spl11_2),
% 1.95/0.68    inference(avatar_contradiction_clause,[],[f1799])).
% 1.95/0.68  fof(f1799,plain,(
% 1.95/0.68    $false | ~spl11_2),
% 1.95/0.68    inference(subsumption_resolution,[],[f1798,f49])).
% 1.95/0.68  fof(f49,plain,(
% 1.95/0.68    k1_xboole_0 != sK3),
% 1.95/0.68    inference(cnf_transformation,[],[f31])).
% 1.95/0.68  fof(f1798,plain,(
% 1.95/0.68    k1_xboole_0 = sK3 | ~spl11_2),
% 1.95/0.68    inference(subsumption_resolution,[],[f1797,f48])).
% 1.95/0.68  fof(f48,plain,(
% 1.95/0.68    k1_xboole_0 != sK2),
% 1.95/0.68    inference(cnf_transformation,[],[f31])).
% 1.95/0.68  fof(f1797,plain,(
% 1.95/0.68    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~spl11_2),
% 1.95/0.68    inference(subsumption_resolution,[],[f1781,f52])).
% 1.95/0.68  fof(f52,plain,(
% 1.95/0.68    v1_xboole_0(k1_xboole_0)),
% 1.95/0.68    inference(cnf_transformation,[],[f2])).
% 1.95/0.68  fof(f2,axiom,(
% 1.95/0.68    v1_xboole_0(k1_xboole_0)),
% 2.32/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 2.32/0.68  fof(f1781,plain,(
% 2.32/0.68    ~v1_xboole_0(k1_xboole_0) | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~spl11_2),
% 2.32/0.68    inference(superposition,[],[f1342,f1749])).
% 2.32/0.68  fof(f1749,plain,(
% 2.32/0.68    k1_xboole_0 = k2_zfmisc_1(sK2,sK3) | ~spl11_2),
% 2.32/0.68    inference(subsumption_resolution,[],[f1702,f50])).
% 2.32/0.68  fof(f50,plain,(
% 2.32/0.68    k1_xboole_0 != sK4),
% 2.32/0.68    inference(cnf_transformation,[],[f31])).
% 2.32/0.68  fof(f1702,plain,(
% 2.32/0.68    k1_xboole_0 = k2_zfmisc_1(sK2,sK3) | k1_xboole_0 = sK4 | ~spl11_2),
% 2.32/0.68    inference(resolution,[],[f1342,f107])).
% 2.32/0.68  fof(f107,plain,(
% 2.32/0.68    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) | ~spl11_2),
% 2.32/0.68    inference(avatar_component_clause,[],[f105])).
% 2.32/0.68  fof(f1342,plain,(
% 2.32/0.68    ( ! [X0,X1] : (~v1_xboole_0(k2_zfmisc_1(X1,X0)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.32/0.68    inference(condensation,[],[f1341])).
% 2.32/0.68  fof(f1341,plain,(
% 2.32/0.68    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | ~v1_xboole_0(k2_zfmisc_1(X1,X2))) )),
% 2.32/0.68    inference(subsumption_resolution,[],[f1295,f277])).
% 2.32/0.68  fof(f277,plain,(
% 2.32/0.68    ( ! [X15,X16] : (k1_xboole_0 = k2_zfmisc_1(X15,X16) | ~v1_xboole_0(X15)) )),
% 2.32/0.68    inference(duplicate_literal_removal,[],[f264])).
% 2.32/0.68  fof(f264,plain,(
% 2.32/0.68    ( ! [X15,X16] : (k1_xboole_0 = k2_zfmisc_1(X15,X16) | ~v1_xboole_0(X15) | ~v1_xboole_0(X15)) )),
% 2.32/0.68    inference(superposition,[],[f197,f133])).
% 2.32/0.68  fof(f133,plain,(
% 2.32/0.68    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = X0 | ~v1_xboole_0(X0)) )),
% 2.32/0.68    inference(superposition,[],[f121,f95])).
% 2.32/0.68  fof(f95,plain,(
% 2.32/0.68    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.32/0.68    inference(resolution,[],[f58,f54])).
% 2.32/0.68  fof(f54,plain,(
% 2.32/0.68    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.32/0.68    inference(cnf_transformation,[],[f35])).
% 2.32/0.68  fof(f35,plain,(
% 2.32/0.68    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK7(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.32/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f33,f34])).
% 2.32/0.68  fof(f34,plain,(
% 2.32/0.68    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK7(X0),X0))),
% 2.32/0.68    introduced(choice_axiom,[])).
% 2.32/0.68  fof(f33,plain,(
% 2.32/0.68    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.32/0.68    inference(rectify,[],[f32])).
% 2.32/0.68  fof(f32,plain,(
% 2.32/0.68    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.32/0.68    inference(nnf_transformation,[],[f1])).
% 2.32/0.68  fof(f1,axiom,(
% 2.32/0.68    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.32/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.32/0.68  fof(f58,plain,(
% 2.32/0.68    ( ! [X0] : (r2_hidden(sK8(X0),X0) | k1_xboole_0 = X0) )),
% 2.32/0.68    inference(cnf_transformation,[],[f39])).
% 2.32/0.68  fof(f39,plain,(
% 2.32/0.68    ! [X0] : ((sP0(sK8(X0),X0) & r2_hidden(sK8(X0),X0)) | k1_xboole_0 = X0)),
% 2.32/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f27,f38])).
% 2.32/0.68  fof(f38,plain,(
% 2.32/0.68    ! [X0] : (? [X1] : (sP0(X1,X0) & r2_hidden(X1,X0)) => (sP0(sK8(X0),X0) & r2_hidden(sK8(X0),X0)))),
% 2.32/0.68    introduced(choice_axiom,[])).
% 2.32/0.68  fof(f27,plain,(
% 2.32/0.68    ! [X0] : (? [X1] : (sP0(X1,X0) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 2.32/0.68    inference(definition_folding,[],[f19,f26])).
% 2.32/0.68  fof(f26,plain,(
% 2.32/0.68    ! [X1,X0] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) | ~sP0(X1,X0))),
% 2.32/0.68    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.32/0.68  fof(f19,plain,(
% 2.32/0.68    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 2.32/0.68    inference(ennf_transformation,[],[f11])).
% 2.32/0.68  fof(f11,axiom,(
% 2.32/0.68    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.32/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).
% 2.32/0.68  fof(f121,plain,(
% 2.32/0.68    ( ! [X3] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X3)) )),
% 2.32/0.68    inference(superposition,[],[f91,f90])).
% 2.32/0.68  fof(f90,plain,(
% 2.32/0.68    ( ! [X2,X0,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0)) )),
% 2.32/0.68    inference(equality_resolution,[],[f83])).
% 2.32/0.68  fof(f83,plain,(
% 2.32/0.68    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 2.32/0.68    inference(definition_unfolding,[],[f78,f79])).
% 2.32/0.68  fof(f79,plain,(
% 2.32/0.68    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 2.32/0.68    inference(definition_unfolding,[],[f73,f65])).
% 2.32/0.68  fof(f73,plain,(
% 2.32/0.68    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 2.32/0.68    inference(cnf_transformation,[],[f9])).
% 2.32/0.68  fof(f9,axiom,(
% 2.32/0.68    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 2.32/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 2.32/0.68  fof(f78,plain,(
% 2.32/0.68    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X3 | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 2.32/0.68    inference(cnf_transformation,[],[f45])).
% 2.32/0.68  fof(f45,plain,(
% 2.32/0.68    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.32/0.68    inference(flattening,[],[f44])).
% 2.32/0.68  fof(f44,plain,(
% 2.32/0.68    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | (k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.32/0.68    inference(nnf_transformation,[],[f13])).
% 2.32/0.68  fof(f13,axiom,(
% 2.32/0.68    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 2.32/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).
% 2.32/0.68  fof(f91,plain,(
% 2.32/0.68    ( ! [X0,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3)) )),
% 2.32/0.68    inference(equality_resolution,[],[f84])).
% 2.32/0.68  fof(f84,plain,(
% 2.32/0.68    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X2 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 2.32/0.68    inference(definition_unfolding,[],[f77,f79])).
% 2.32/0.68  fof(f77,plain,(
% 2.32/0.68    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X2 | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 2.32/0.68    inference(cnf_transformation,[],[f45])).
% 2.32/0.68  fof(f197,plain,(
% 2.32/0.68    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X1) | ~v1_xboole_0(X0)) )),
% 2.32/0.68    inference(superposition,[],[f91,f127])).
% 2.32/0.68  fof(f127,plain,(
% 2.32/0.68    ( ! [X0] : (k2_zfmisc_1(X0,X0) = X0 | ~v1_xboole_0(X0)) )),
% 2.32/0.68    inference(superposition,[],[f114,f95])).
% 2.32/0.68  fof(f114,plain,(
% 2.32/0.68    k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),
% 2.32/0.68    inference(superposition,[],[f90,f90])).
% 2.32/0.68  fof(f1295,plain,(
% 2.32/0.68    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X1,X2),X0) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | ~v1_xboole_0(k2_zfmisc_1(X1,X2))) )),
% 2.32/0.68    inference(condensation,[],[f1270])).
% 2.32/0.68  fof(f1270,plain,(
% 2.32/0.68    ( ! [X59,X57,X60,X58] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X57,X58),X60) | k1_xboole_0 = X60 | k1_xboole_0 = X59 | k1_xboole_0 = X58 | k1_xboole_0 = X57 | ~v1_xboole_0(k2_zfmisc_1(X57,X58))) )),
% 2.32/0.68    inference(superposition,[],[f87,f133])).
% 2.32/0.68  fof(f87,plain,(
% 2.32/0.68    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.32/0.68    inference(definition_unfolding,[],[f74,f79])).
% 2.32/0.68  fof(f74,plain,(
% 2.32/0.68    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.32/0.68    inference(cnf_transformation,[],[f45])).
% 2.32/0.68  fof(f1146,plain,(
% 2.32/0.68    spl11_10),
% 2.32/0.68    inference(avatar_split_clause,[],[f1145,f468])).
% 2.32/0.68  fof(f468,plain,(
% 2.32/0.68    spl11_10 <=> sP1(sK6,sK4,sK3,sK2)),
% 2.32/0.68    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).
% 2.32/0.68  fof(f1145,plain,(
% 2.32/0.68    sP1(sK6,sK4,sK3,sK2)),
% 2.32/0.68    inference(subsumption_resolution,[],[f1144,f48])).
% 2.32/0.68  fof(f1144,plain,(
% 2.32/0.68    sP1(sK6,sK4,sK3,sK2) | k1_xboole_0 = sK2),
% 2.32/0.68    inference(subsumption_resolution,[],[f1143,f49])).
% 2.32/0.68  fof(f1143,plain,(
% 2.32/0.68    sP1(sK6,sK4,sK3,sK2) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2),
% 2.32/0.68    inference(subsumption_resolution,[],[f1104,f50])).
% 2.32/0.68  fof(f1104,plain,(
% 2.32/0.68    sP1(sK6,sK4,sK3,sK2) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2),
% 2.32/0.68    inference(resolution,[],[f82,f81])).
% 2.32/0.68  fof(f82,plain,(
% 2.32/0.68    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | sP1(X3,X2,X1,X0) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.32/0.68    inference(definition_unfolding,[],[f71,f65])).
% 2.32/0.68  fof(f71,plain,(
% 2.32/0.68    ( ! [X2,X0,X3,X1] : (sP1(X3,X2,X1,X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.32/0.68    inference(cnf_transformation,[],[f29])).
% 2.32/0.68  fof(f29,plain,(
% 2.32/0.68    ! [X0,X1,X2] : (! [X3] : (sP1(X3,X2,X1,X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.32/0.68    inference(definition_folding,[],[f24,f28])).
% 2.32/0.68  fof(f28,plain,(
% 2.32/0.68    ! [X3,X2,X1,X0] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~sP1(X3,X2,X1,X0))),
% 2.32/0.68    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.32/0.68  fof(f24,plain,(
% 2.32/0.68    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.32/0.68    inference(ennf_transformation,[],[f12])).
% 2.32/0.68  fof(f12,axiom,(
% 2.32/0.68    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.32/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).
% 2.32/0.68  fof(f475,plain,(
% 2.32/0.68    ~spl11_10 | ~spl11_11),
% 2.32/0.68    inference(avatar_split_clause,[],[f466,f472,f468])).
% 2.32/0.68  fof(f466,plain,(
% 2.32/0.68    sK5 != k2_mcart_1(sK6) | ~sP1(sK6,sK4,sK3,sK2)),
% 2.32/0.68    inference(superposition,[],[f51,f70])).
% 2.32/0.68  fof(f70,plain,(
% 2.32/0.68    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X0) = k7_mcart_1(X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3)) )),
% 2.32/0.68    inference(cnf_transformation,[],[f41])).
% 2.32/0.68  fof(f41,plain,(
% 2.32/0.68    ! [X0,X1,X2,X3] : ((k2_mcart_1(X0) = k7_mcart_1(X3,X2,X1,X0) & k6_mcart_1(X3,X2,X1,X0) = k2_mcart_1(k1_mcart_1(X0)) & k5_mcart_1(X3,X2,X1,X0) = k1_mcart_1(k1_mcart_1(X0))) | ~sP1(X0,X1,X2,X3))),
% 2.32/0.68    inference(rectify,[],[f40])).
% 2.32/0.68  fof(f40,plain,(
% 2.32/0.68    ! [X3,X2,X1,X0] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~sP1(X3,X2,X1,X0))),
% 2.32/0.68    inference(nnf_transformation,[],[f28])).
% 2.32/0.68  fof(f51,plain,(
% 2.32/0.68    sK5 != k7_mcart_1(sK2,sK3,sK4,sK6)),
% 2.32/0.68    inference(cnf_transformation,[],[f31])).
% 2.32/0.68  % SZS output end Proof for theBenchmark
% 2.32/0.68  % (8959)------------------------------
% 2.32/0.68  % (8959)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.32/0.68  % (8959)Termination reason: Refutation
% 2.32/0.68  
% 2.32/0.68  % (8959)Memory used [KB]: 7036
% 2.32/0.68  % (8959)Time elapsed: 0.281 s
% 2.32/0.68  % (8959)------------------------------
% 2.32/0.68  % (8959)------------------------------
% 2.32/0.71  % (8968)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.32/0.71  % (8931)Success in time 0.345 s
%------------------------------------------------------------------------------
