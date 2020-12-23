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
% DateTime   : Thu Dec  3 12:59:39 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 352 expanded)
%              Number of leaves         :   28 ( 141 expanded)
%              Depth                    :   11
%              Number of atoms          :  361 (1719 expanded)
%              Number of equality atoms :   68 ( 132 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f301,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f131,f171,f198,f202,f203,f225,f239,f252,f280,f285,f286,f287,f295,f297,f300])).

fof(f300,plain,
    ( spl9_3
    | ~ spl9_9 ),
    inference(avatar_contradiction_clause,[],[f299])).

fof(f299,plain,
    ( $false
    | spl9_3
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f76,f298])).

fof(f298,plain,
    ( ~ r2_hidden(k2_mcart_1(sK6),sK5)
    | spl9_3
    | ~ spl9_9 ),
    inference(forward_demodulation,[],[f66,f99])).

fof(f99,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6)
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl9_9
  <=> k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f66,plain,
    ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
    | spl9_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl9_3
  <=> r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f76,plain,(
    r2_hidden(k2_mcart_1(sK6),sK5) ),
    inference(resolution,[],[f53,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f53,plain,(
    r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f36,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f36,plain,(
    r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
      | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
      | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) )
    & r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5))
    & m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))
    & m1_subset_1(sK5,k1_zfmisc_1(sK2))
    & m1_subset_1(sK4,k1_zfmisc_1(sK1))
    & m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f14,f23,f22,f21,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                      | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                      | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                    & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                    & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
                & m1_subset_1(X5,k1_zfmisc_1(X2)) )
            & m1_subset_1(X4,k1_zfmisc_1(X1)) )
        & m1_subset_1(X3,k1_zfmisc_1(X0)) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3) )
                  & r2_hidden(X6,k3_zfmisc_1(sK3,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
              & m1_subset_1(X5,k1_zfmisc_1(sK2)) )
          & m1_subset_1(X4,k1_zfmisc_1(sK1)) )
      & m1_subset_1(sK3,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5)
                  | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),X4)
                  | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3) )
                & r2_hidden(X6,k3_zfmisc_1(sK3,X4,X5))
                & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
            & m1_subset_1(X5,k1_zfmisc_1(sK2)) )
        & m1_subset_1(X4,k1_zfmisc_1(sK1)) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5)
                | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4)
                | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3) )
              & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,X5))
              & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
          & m1_subset_1(X5,k1_zfmisc_1(sK2)) )
      & m1_subset_1(sK4,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5)
              | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4)
              | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3) )
            & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,X5))
            & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
        & m1_subset_1(X5,k1_zfmisc_1(sK2)) )
   => ( ? [X6] :
          ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),sK5)
            | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4)
            | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3) )
          & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,sK5))
          & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
      & m1_subset_1(sK5,k1_zfmisc_1(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X6] :
        ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),sK5)
          | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4)
          | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3) )
        & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,sK5))
        & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
   => ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
        | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
        | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) )
      & r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5))
      & m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                  & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
              & m1_subset_1(X5,k1_zfmisc_1(X2)) )
          & m1_subset_1(X4,k1_zfmisc_1(X1)) )
      & m1_subset_1(X3,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                  & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
              & m1_subset_1(X5,k1_zfmisc_1(X2)) )
          & m1_subset_1(X4,k1_zfmisc_1(X1)) )
      & m1_subset_1(X3,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(X0))
       => ! [X4] :
            ( m1_subset_1(X4,k1_zfmisc_1(X1))
           => ! [X5] :
                ( m1_subset_1(X5,k1_zfmisc_1(X2))
               => ! [X6] :
                    ( m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))
                   => ( r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                     => ( r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                        & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                        & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X0))
     => ! [X4] :
          ( m1_subset_1(X4,k1_zfmisc_1(X1))
         => ! [X5] :
              ( m1_subset_1(X5,k1_zfmisc_1(X2))
             => ! [X6] :
                  ( m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))
                 => ( r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                   => ( r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                      & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                      & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_mcart_1)).

fof(f297,plain,
    ( spl9_2
    | ~ spl9_8 ),
    inference(avatar_contradiction_clause,[],[f296])).

fof(f296,plain,
    ( $false
    | spl9_2
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f292,f114])).

fof(f114,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) ),
    inference(resolution,[],[f75,f49])).

fof(f75,plain,(
    r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4)) ),
    inference(resolution,[],[f53,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f292,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)
    | spl9_2
    | ~ spl9_8 ),
    inference(backward_demodulation,[],[f63,f95])).

fof(f95,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl9_8
  <=> k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f63,plain,
    ( ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl9_2
  <=> r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f295,plain,(
    ~ spl9_15 ),
    inference(avatar_contradiction_clause,[],[f294])).

fof(f294,plain,
    ( $false
    | ~ spl9_15 ),
    inference(resolution,[],[f113,f140])).

fof(f140,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3)
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl9_15
  <=> ! [X0] : ~ r2_hidden(X0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f113,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) ),
    inference(resolution,[],[f75,f48])).

fof(f287,plain,
    ( spl9_4
    | spl9_5
    | spl9_6
    | spl9_9 ),
    inference(avatar_split_clause,[],[f284,f98,f87,f84,f81])).

fof(f81,plain,
    ( spl9_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f84,plain,
    ( spl9_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f87,plain,
    ( spl9_6
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f284,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f54,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f52,f47])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f54,plain,(
    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f35,f47])).

fof(f35,plain,(
    m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f286,plain,
    ( spl9_4
    | spl9_5
    | spl9_6
    | spl9_8 ),
    inference(avatar_split_clause,[],[f283,f94,f87,f84,f81])).

fof(f283,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f54,f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f51,f47])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f285,plain,
    ( spl9_4
    | spl9_5
    | spl9_6
    | spl9_7 ),
    inference(avatar_split_clause,[],[f282,f90,f87,f84,f81])).

fof(f90,plain,
    ( spl9_7
  <=> k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f282,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f54,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f50,f47])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f280,plain,
    ( ~ spl9_4
    | spl9_16 ),
    inference(avatar_contradiction_clause,[],[f278])).

fof(f278,plain,
    ( $false
    | ~ spl9_4
    | spl9_16 ),
    inference(resolution,[],[f276,f38])).

fof(f38,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f276,plain,
    ( ~ r1_xboole_0(sK3,k1_xboole_0)
    | ~ spl9_4
    | spl9_16 ),
    inference(forward_demodulation,[],[f197,f82])).

fof(f82,plain,
    ( k1_xboole_0 = sK0
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f197,plain,
    ( ~ r1_xboole_0(sK3,sK0)
    | spl9_16 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl9_16
  <=> r1_xboole_0(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f252,plain,(
    ~ spl9_13 ),
    inference(avatar_contradiction_clause,[],[f251])).

fof(f251,plain,
    ( $false
    | ~ spl9_13 ),
    inference(subsumption_resolution,[],[f76,f130])).

fof(f130,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK5)
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl9_13
  <=> ! [X0] : ~ r2_hidden(X0,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f239,plain,
    ( spl9_1
    | ~ spl9_7 ),
    inference(avatar_contradiction_clause,[],[f238])).

fof(f238,plain,
    ( $false
    | spl9_1
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f113,f236])).

fof(f236,plain,
    ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)
    | spl9_1
    | ~ spl9_7 ),
    inference(backward_demodulation,[],[f60,f91])).

fof(f91,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f90])).

fof(f60,plain,
    ( ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl9_1
  <=> r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f225,plain,(
    ~ spl9_11 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f114,f122])).

fof(f122,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK4)
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl9_11
  <=> ! [X0] : ~ r2_hidden(X0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f203,plain,
    ( ~ spl9_10
    | spl9_11 ),
    inference(avatar_split_clause,[],[f199,f121,f118])).

fof(f118,plain,
    ( spl9_10
  <=> r1_xboole_0(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f199,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK4)
      | ~ r1_xboole_0(sK4,sK1) ) ),
    inference(superposition,[],[f40,f74])).

fof(f74,plain,(
    sK4 = k3_xboole_0(sK4,sK1) ),
    inference(resolution,[],[f71,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f71,plain,(
    r1_tarski(sK4,sK1) ),
    inference(resolution,[],[f33,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f33,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK7(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f15,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK7(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f202,plain,
    ( ~ spl9_6
    | spl9_12 ),
    inference(avatar_contradiction_clause,[],[f200])).

fof(f200,plain,
    ( $false
    | ~ spl9_6
    | spl9_12 ),
    inference(resolution,[],[f183,f38])).

fof(f183,plain,
    ( ~ r1_xboole_0(sK5,k1_xboole_0)
    | ~ spl9_6
    | spl9_12 ),
    inference(backward_demodulation,[],[f127,f88])).

fof(f88,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f87])).

fof(f127,plain,
    ( ~ r1_xboole_0(sK5,sK2)
    | spl9_12 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl9_12
  <=> r1_xboole_0(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f198,plain,
    ( ~ spl9_16
    | spl9_15 ),
    inference(avatar_split_clause,[],[f194,f139,f196])).

fof(f194,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | ~ r1_xboole_0(sK3,sK0) ) ),
    inference(superposition,[],[f40,f70])).

fof(f70,plain,(
    sK3 = k3_xboole_0(sK3,sK0) ),
    inference(resolution,[],[f68,f41])).

fof(f68,plain,(
    r1_tarski(sK3,sK0) ),
    inference(resolution,[],[f32,f45])).

fof(f32,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f171,plain,
    ( ~ spl9_5
    | spl9_10 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | ~ spl9_5
    | spl9_10 ),
    inference(resolution,[],[f159,f38])).

fof(f159,plain,
    ( ~ r1_xboole_0(sK4,k1_xboole_0)
    | ~ spl9_5
    | spl9_10 ),
    inference(backward_demodulation,[],[f119,f85])).

fof(f85,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f84])).

fof(f119,plain,
    ( ~ r1_xboole_0(sK4,sK1)
    | spl9_10 ),
    inference(avatar_component_clause,[],[f118])).

fof(f131,plain,
    ( ~ spl9_12
    | spl9_13 ),
    inference(avatar_split_clause,[],[f124,f129,f126])).

fof(f124,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK5)
      | ~ r1_xboole_0(sK5,sK2) ) ),
    inference(superposition,[],[f40,f102])).

fof(f102,plain,(
    sK5 = k3_xboole_0(sK5,sK2) ),
    inference(resolution,[],[f72,f41])).

fof(f72,plain,(
    r1_tarski(sK5,sK2) ),
    inference(resolution,[],[f34,f45])).

fof(f34,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f67,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f37,f65,f62,f59])).

fof(f37,plain,
    ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
    | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
    | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:21:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (27534)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.47  % (27545)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.53  % (27529)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (27530)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (27529)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f301,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(avatar_sat_refutation,[],[f67,f131,f171,f198,f202,f203,f225,f239,f252,f280,f285,f286,f287,f295,f297,f300])).
% 0.20/0.54  fof(f300,plain,(
% 0.20/0.54    spl9_3 | ~spl9_9),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f299])).
% 0.20/0.54  fof(f299,plain,(
% 0.20/0.54    $false | (spl9_3 | ~spl9_9)),
% 0.20/0.54    inference(subsumption_resolution,[],[f76,f298])).
% 0.20/0.54  fof(f298,plain,(
% 0.20/0.54    ~r2_hidden(k2_mcart_1(sK6),sK5) | (spl9_3 | ~spl9_9)),
% 0.20/0.54    inference(forward_demodulation,[],[f66,f99])).
% 0.20/0.54  fof(f99,plain,(
% 0.20/0.54    k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6) | ~spl9_9),
% 0.20/0.54    inference(avatar_component_clause,[],[f98])).
% 0.20/0.54  fof(f98,plain,(
% 0.20/0.54    spl9_9 <=> k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 0.20/0.54  fof(f66,plain,(
% 0.20/0.54    ~r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) | spl9_3),
% 0.20/0.54    inference(avatar_component_clause,[],[f65])).
% 0.20/0.54  fof(f65,plain,(
% 0.20/0.54    spl9_3 <=> r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.20/0.54  fof(f76,plain,(
% 0.20/0.54    r2_hidden(k2_mcart_1(sK6),sK5)),
% 0.20/0.54    inference(resolution,[],[f53,f49])).
% 0.20/0.54  fof(f49,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f18])).
% 0.20/0.54  fof(f18,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.54    inference(ennf_transformation,[],[f8])).
% 0.20/0.54  fof(f8,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.20/0.54  fof(f53,plain,(
% 0.20/0.54    r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 0.20/0.54    inference(definition_unfolding,[],[f36,f47])).
% 0.20/0.54  fof(f47,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f7])).
% 0.20/0.54  fof(f7,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.20/0.54  fof(f36,plain,(
% 0.20/0.54    r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5))),
% 0.20/0.54    inference(cnf_transformation,[],[f24])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    ((((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)) & r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5)) & m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(sK5,k1_zfmisc_1(sK2))) & m1_subset_1(sK4,k1_zfmisc_1(sK1))) & m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f14,f23,f22,f21,f20])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) => (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),X4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(X5,k1_zfmisc_1(sK2))) & m1_subset_1(X4,k1_zfmisc_1(sK1))) & m1_subset_1(sK3,k1_zfmisc_1(sK0)))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f21,plain,(
% 0.20/0.54    ? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),X4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(X5,k1_zfmisc_1(sK2))) & m1_subset_1(X4,k1_zfmisc_1(sK1))) => (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(X5,k1_zfmisc_1(sK2))) & m1_subset_1(sK4,k1_zfmisc_1(sK1)))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    ? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(X5,k1_zfmisc_1(sK2))) => (? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),sK5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,sK5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(sK5,k1_zfmisc_1(sK2)))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),sK5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,sK5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) => ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)) & r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5)) & m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f14,plain,(
% 0.20/0.54    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 0.20/0.54    inference(flattening,[],[f13])).
% 0.20/0.54  fof(f13,plain,(
% 0.20/0.54    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : (((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f11])).
% 0.20/0.54  fof(f11,negated_conjecture,(
% 0.20/0.54    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 0.20/0.54    inference(negated_conjecture,[],[f10])).
% 0.20/0.54  fof(f10,conjecture,(
% 0.20/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_mcart_1)).
% 0.20/0.54  fof(f297,plain,(
% 0.20/0.54    spl9_2 | ~spl9_8),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f296])).
% 0.20/0.54  fof(f296,plain,(
% 0.20/0.54    $false | (spl9_2 | ~spl9_8)),
% 0.20/0.54    inference(subsumption_resolution,[],[f292,f114])).
% 0.20/0.54  fof(f114,plain,(
% 0.20/0.54    r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)),
% 0.20/0.54    inference(resolution,[],[f75,f49])).
% 0.20/0.54  fof(f75,plain,(
% 0.20/0.54    r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4))),
% 0.20/0.54    inference(resolution,[],[f53,f48])).
% 0.20/0.54  fof(f48,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f18])).
% 0.20/0.54  fof(f292,plain,(
% 0.20/0.54    ~r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) | (spl9_2 | ~spl9_8)),
% 0.20/0.54    inference(backward_demodulation,[],[f63,f95])).
% 0.20/0.54  fof(f95,plain,(
% 0.20/0.54    k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6)) | ~spl9_8),
% 0.20/0.54    inference(avatar_component_clause,[],[f94])).
% 0.20/0.54  fof(f94,plain,(
% 0.20/0.54    spl9_8 <=> k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.20/0.54  fof(f63,plain,(
% 0.20/0.54    ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) | spl9_2),
% 0.20/0.54    inference(avatar_component_clause,[],[f62])).
% 0.20/0.54  fof(f62,plain,(
% 0.20/0.54    spl9_2 <=> r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.20/0.54  fof(f295,plain,(
% 0.20/0.54    ~spl9_15),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f294])).
% 0.20/0.54  fof(f294,plain,(
% 0.20/0.54    $false | ~spl9_15),
% 0.20/0.54    inference(resolution,[],[f113,f140])).
% 0.20/0.54  fof(f140,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(X0,sK3)) ) | ~spl9_15),
% 0.20/0.54    inference(avatar_component_clause,[],[f139])).
% 0.20/0.54  fof(f139,plain,(
% 0.20/0.54    spl9_15 <=> ! [X0] : ~r2_hidden(X0,sK3)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 0.20/0.54  fof(f113,plain,(
% 0.20/0.54    r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)),
% 0.20/0.54    inference(resolution,[],[f75,f48])).
% 0.20/0.54  fof(f287,plain,(
% 0.20/0.54    spl9_4 | spl9_5 | spl9_6 | spl9_9),
% 0.20/0.54    inference(avatar_split_clause,[],[f284,f98,f87,f84,f81])).
% 0.20/0.54  fof(f81,plain,(
% 0.20/0.54    spl9_4 <=> k1_xboole_0 = sK0),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.20/0.54  fof(f84,plain,(
% 0.20/0.54    spl9_5 <=> k1_xboole_0 = sK1),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.20/0.54  fof(f87,plain,(
% 0.20/0.54    spl9_6 <=> k1_xboole_0 = sK2),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.20/0.54  fof(f284,plain,(
% 0.20/0.54    k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.20/0.54    inference(resolution,[],[f54,f55])).
% 0.20/0.54  fof(f55,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.54    inference(definition_unfolding,[],[f52,f47])).
% 0.20/0.54  fof(f52,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f19])).
% 0.20/0.54  fof(f19,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.54    inference(ennf_transformation,[],[f9])).
% 0.20/0.54  fof(f9,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).
% 0.20/0.54  fof(f54,plain,(
% 0.20/0.54    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.20/0.54    inference(definition_unfolding,[],[f35,f47])).
% 0.20/0.54  fof(f35,plain,(
% 0.20/0.54    m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.20/0.54    inference(cnf_transformation,[],[f24])).
% 0.20/0.54  fof(f286,plain,(
% 0.20/0.54    spl9_4 | spl9_5 | spl9_6 | spl9_8),
% 0.20/0.54    inference(avatar_split_clause,[],[f283,f94,f87,f84,f81])).
% 0.20/0.54  fof(f283,plain,(
% 0.20/0.54    k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.20/0.54    inference(resolution,[],[f54,f56])).
% 0.20/0.54  fof(f56,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.54    inference(definition_unfolding,[],[f51,f47])).
% 0.20/0.54  fof(f51,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f19])).
% 0.20/0.54  fof(f285,plain,(
% 0.20/0.54    spl9_4 | spl9_5 | spl9_6 | spl9_7),
% 0.20/0.54    inference(avatar_split_clause,[],[f282,f90,f87,f84,f81])).
% 0.20/0.54  fof(f90,plain,(
% 0.20/0.54    spl9_7 <=> k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.20/0.54  fof(f282,plain,(
% 0.20/0.54    k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.20/0.54    inference(resolution,[],[f54,f57])).
% 0.20/0.54  fof(f57,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.54    inference(definition_unfolding,[],[f50,f47])).
% 0.20/0.54  fof(f50,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f19])).
% 0.20/0.54  fof(f280,plain,(
% 0.20/0.54    ~spl9_4 | spl9_16),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f278])).
% 0.20/0.54  fof(f278,plain,(
% 0.20/0.54    $false | (~spl9_4 | spl9_16)),
% 0.20/0.54    inference(resolution,[],[f276,f38])).
% 0.20/0.54  fof(f38,plain,(
% 0.20/0.54    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.20/0.54  fof(f276,plain,(
% 0.20/0.54    ~r1_xboole_0(sK3,k1_xboole_0) | (~spl9_4 | spl9_16)),
% 0.20/0.54    inference(forward_demodulation,[],[f197,f82])).
% 0.20/0.54  fof(f82,plain,(
% 0.20/0.54    k1_xboole_0 = sK0 | ~spl9_4),
% 0.20/0.54    inference(avatar_component_clause,[],[f81])).
% 0.20/0.54  fof(f197,plain,(
% 0.20/0.54    ~r1_xboole_0(sK3,sK0) | spl9_16),
% 0.20/0.54    inference(avatar_component_clause,[],[f196])).
% 0.20/0.54  fof(f196,plain,(
% 0.20/0.54    spl9_16 <=> r1_xboole_0(sK3,sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 0.20/0.54  fof(f252,plain,(
% 0.20/0.54    ~spl9_13),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f251])).
% 0.20/0.54  fof(f251,plain,(
% 0.20/0.54    $false | ~spl9_13),
% 0.20/0.54    inference(subsumption_resolution,[],[f76,f130])).
% 0.20/0.54  fof(f130,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(X0,sK5)) ) | ~spl9_13),
% 0.20/0.54    inference(avatar_component_clause,[],[f129])).
% 0.20/0.54  fof(f129,plain,(
% 0.20/0.54    spl9_13 <=> ! [X0] : ~r2_hidden(X0,sK5)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 0.20/0.54  fof(f239,plain,(
% 0.20/0.54    spl9_1 | ~spl9_7),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f238])).
% 0.20/0.54  fof(f238,plain,(
% 0.20/0.54    $false | (spl9_1 | ~spl9_7)),
% 0.20/0.54    inference(subsumption_resolution,[],[f113,f236])).
% 0.20/0.54  fof(f236,plain,(
% 0.20/0.54    ~r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) | (spl9_1 | ~spl9_7)),
% 0.20/0.54    inference(backward_demodulation,[],[f60,f91])).
% 0.20/0.54  fof(f91,plain,(
% 0.20/0.54    k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6)) | ~spl9_7),
% 0.20/0.54    inference(avatar_component_clause,[],[f90])).
% 0.20/0.54  fof(f60,plain,(
% 0.20/0.54    ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) | spl9_1),
% 0.20/0.54    inference(avatar_component_clause,[],[f59])).
% 0.20/0.54  fof(f59,plain,(
% 0.20/0.54    spl9_1 <=> r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.20/0.54  fof(f225,plain,(
% 0.20/0.54    ~spl9_11),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f224])).
% 0.20/0.54  fof(f224,plain,(
% 0.20/0.54    $false | ~spl9_11),
% 0.20/0.54    inference(subsumption_resolution,[],[f114,f122])).
% 0.20/0.54  fof(f122,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(X0,sK4)) ) | ~spl9_11),
% 0.20/0.54    inference(avatar_component_clause,[],[f121])).
% 0.20/0.54  fof(f121,plain,(
% 0.20/0.54    spl9_11 <=> ! [X0] : ~r2_hidden(X0,sK4)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 0.20/0.54  fof(f203,plain,(
% 0.20/0.54    ~spl9_10 | spl9_11),
% 0.20/0.54    inference(avatar_split_clause,[],[f199,f121,f118])).
% 0.20/0.54  fof(f118,plain,(
% 0.20/0.54    spl9_10 <=> r1_xboole_0(sK4,sK1)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 0.20/0.54  fof(f199,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(X0,sK4) | ~r1_xboole_0(sK4,sK1)) )),
% 0.20/0.54    inference(superposition,[],[f40,f74])).
% 0.20/0.54  fof(f74,plain,(
% 0.20/0.54    sK4 = k3_xboole_0(sK4,sK1)),
% 0.20/0.54    inference(resolution,[],[f71,f41])).
% 0.20/0.54  fof(f41,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f16])).
% 0.20/0.54  fof(f16,plain,(
% 0.20/0.54    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f4])).
% 0.20/0.54  fof(f4,axiom,(
% 0.20/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.54  fof(f71,plain,(
% 0.20/0.54    r1_tarski(sK4,sK1)),
% 0.20/0.54    inference(resolution,[],[f33,f45])).
% 0.20/0.54  fof(f45,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f31])).
% 0.20/0.54  fof(f31,plain,(
% 0.20/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.54    inference(nnf_transformation,[],[f6])).
% 0.20/0.54  fof(f6,axiom,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 0.20/0.54    inference(cnf_transformation,[],[f24])).
% 0.20/0.54  fof(f40,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f26])).
% 0.20/0.54  fof(f26,plain,(
% 0.20/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK7(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f15,f25])).
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK7(X0,X1),k3_xboole_0(X0,X1)))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f15,plain,(
% 0.20/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.54    inference(ennf_transformation,[],[f12])).
% 0.20/0.54  fof(f12,plain,(
% 0.20/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.54    inference(rectify,[],[f3])).
% 0.20/0.54  fof(f3,axiom,(
% 0.20/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.20/0.54  fof(f202,plain,(
% 0.20/0.54    ~spl9_6 | spl9_12),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f200])).
% 0.20/0.54  fof(f200,plain,(
% 0.20/0.54    $false | (~spl9_6 | spl9_12)),
% 0.20/0.54    inference(resolution,[],[f183,f38])).
% 0.20/0.54  fof(f183,plain,(
% 0.20/0.54    ~r1_xboole_0(sK5,k1_xboole_0) | (~spl9_6 | spl9_12)),
% 0.20/0.54    inference(backward_demodulation,[],[f127,f88])).
% 0.20/0.54  fof(f88,plain,(
% 0.20/0.54    k1_xboole_0 = sK2 | ~spl9_6),
% 0.20/0.54    inference(avatar_component_clause,[],[f87])).
% 0.20/0.54  fof(f127,plain,(
% 0.20/0.54    ~r1_xboole_0(sK5,sK2) | spl9_12),
% 0.20/0.54    inference(avatar_component_clause,[],[f126])).
% 0.20/0.54  fof(f126,plain,(
% 0.20/0.54    spl9_12 <=> r1_xboole_0(sK5,sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 0.20/0.54  fof(f198,plain,(
% 0.20/0.54    ~spl9_16 | spl9_15),
% 0.20/0.54    inference(avatar_split_clause,[],[f194,f139,f196])).
% 0.20/0.54  fof(f194,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(X0,sK3) | ~r1_xboole_0(sK3,sK0)) )),
% 0.20/0.54    inference(superposition,[],[f40,f70])).
% 0.20/0.54  fof(f70,plain,(
% 0.20/0.54    sK3 = k3_xboole_0(sK3,sK0)),
% 0.20/0.54    inference(resolution,[],[f68,f41])).
% 0.20/0.54  fof(f68,plain,(
% 0.20/0.54    r1_tarski(sK3,sK0)),
% 0.20/0.54    inference(resolution,[],[f32,f45])).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.20/0.54    inference(cnf_transformation,[],[f24])).
% 0.20/0.54  fof(f171,plain,(
% 0.20/0.54    ~spl9_5 | spl9_10),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f169])).
% 0.20/0.54  fof(f169,plain,(
% 0.20/0.54    $false | (~spl9_5 | spl9_10)),
% 0.20/0.54    inference(resolution,[],[f159,f38])).
% 0.20/0.54  fof(f159,plain,(
% 0.20/0.54    ~r1_xboole_0(sK4,k1_xboole_0) | (~spl9_5 | spl9_10)),
% 0.20/0.54    inference(backward_demodulation,[],[f119,f85])).
% 0.20/0.54  fof(f85,plain,(
% 0.20/0.54    k1_xboole_0 = sK1 | ~spl9_5),
% 0.20/0.54    inference(avatar_component_clause,[],[f84])).
% 0.20/0.54  fof(f119,plain,(
% 0.20/0.54    ~r1_xboole_0(sK4,sK1) | spl9_10),
% 0.20/0.54    inference(avatar_component_clause,[],[f118])).
% 0.20/0.54  fof(f131,plain,(
% 0.20/0.54    ~spl9_12 | spl9_13),
% 0.20/0.54    inference(avatar_split_clause,[],[f124,f129,f126])).
% 0.20/0.54  fof(f124,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(X0,sK5) | ~r1_xboole_0(sK5,sK2)) )),
% 0.20/0.54    inference(superposition,[],[f40,f102])).
% 0.20/0.54  fof(f102,plain,(
% 0.20/0.54    sK5 = k3_xboole_0(sK5,sK2)),
% 0.20/0.54    inference(resolution,[],[f72,f41])).
% 0.20/0.54  fof(f72,plain,(
% 0.20/0.54    r1_tarski(sK5,sK2)),
% 0.20/0.54    inference(resolution,[],[f34,f45])).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 0.20/0.54    inference(cnf_transformation,[],[f24])).
% 0.20/0.54  fof(f67,plain,(
% 0.20/0.54    ~spl9_1 | ~spl9_2 | ~spl9_3),
% 0.20/0.54    inference(avatar_split_clause,[],[f37,f65,f62,f59])).
% 0.20/0.54  fof(f37,plain,(
% 0.20/0.54    ~r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)),
% 0.20/0.54    inference(cnf_transformation,[],[f24])).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (27529)------------------------------
% 0.20/0.54  % (27529)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (27529)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (27529)Memory used [KB]: 10874
% 0.20/0.54  % (27529)Time elapsed: 0.129 s
% 0.20/0.54  % (27529)------------------------------
% 0.20/0.54  % (27529)------------------------------
% 0.20/0.54  % (27528)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.54  % (27533)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.54  % (27543)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (27553)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (27531)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.54  % (27535)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.54  % (27555)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.55  % (27544)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.55  % (27557)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.55  % (27552)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.55  % (27548)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.55  % (27550)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.55  % (27546)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (27536)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.55  % (27554)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.55  % (27537)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.56  % (27537)Refutation not found, incomplete strategy% (27537)------------------------------
% 0.20/0.56  % (27537)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (27537)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (27537)Memory used [KB]: 10746
% 0.20/0.56  % (27537)Time elapsed: 0.149 s
% 0.20/0.56  % (27537)------------------------------
% 0.20/0.56  % (27537)------------------------------
% 0.20/0.56  % (27540)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.56  % (27526)Success in time 0.198 s
%------------------------------------------------------------------------------
