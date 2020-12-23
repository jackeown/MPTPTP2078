%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:39 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 310 expanded)
%              Number of leaves         :   20 ( 123 expanded)
%              Depth                    :   14
%              Number of atoms          :  299 (1611 expanded)
%              Number of equality atoms :   62 ( 120 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f162,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f90,f95,f100,f126,f139,f152,f155,f158,f161])).

fof(f161,plain,
    ( spl8_1
    | ~ spl8_7 ),
    inference(avatar_contradiction_clause,[],[f160])).

fof(f160,plain,
    ( $false
    | spl8_1
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f159,f116])).

fof(f116,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) ),
    inference(resolution,[],[f67,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f67,plain,(
    r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4)) ),
    inference(resolution,[],[f46,f41])).

fof(f46,plain,(
    r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f32,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f32,plain,(
    r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
      | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
      | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) )
    & r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5))
    & m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))
    & m1_subset_1(sK5,k1_zfmisc_1(sK2))
    & m1_subset_1(sK4,k1_zfmisc_1(sK1))
    & m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f14,f24,f23,f22,f21])).

fof(f21,plain,
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

fof(f22,plain,
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

fof(f23,plain,
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

fof(f24,plain,
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
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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

fof(f159,plain,
    ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)
    | spl8_1
    | ~ spl8_7 ),
    inference(backward_demodulation,[],[f54,f89])).

fof(f89,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl8_7
  <=> k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f54,plain,
    ( ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl8_1
  <=> r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f158,plain,
    ( spl8_2
    | ~ spl8_8 ),
    inference(avatar_contradiction_clause,[],[f157])).

fof(f157,plain,
    ( $false
    | spl8_2
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f156,f117])).

fof(f117,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) ),
    inference(resolution,[],[f67,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f156,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)
    | spl8_2
    | ~ spl8_8 ),
    inference(backward_demodulation,[],[f58,f94])).

fof(f94,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl8_8
  <=> k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f58,plain,
    ( ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl8_2
  <=> r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f155,plain,
    ( spl8_3
    | ~ spl8_9 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | spl8_3
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f153,f68])).

fof(f68,plain,(
    r2_hidden(k2_mcart_1(sK6),sK5) ),
    inference(resolution,[],[f46,f42])).

fof(f153,plain,
    ( ~ r2_hidden(k2_mcart_1(sK6),sK5)
    | spl8_3
    | ~ spl8_9 ),
    inference(backward_demodulation,[],[f62,f99])).

fof(f99,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl8_9
  <=> k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f62,plain,
    ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl8_3
  <=> r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f152,plain,(
    ~ spl8_6 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f150,f34])).

fof(f34,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f150,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f115,f85])).

fof(f85,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl8_6
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f115,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(resolution,[],[f114,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f114,plain,(
    r2_hidden(k2_mcart_1(sK6),sK2) ),
    inference(resolution,[],[f66,f68])).

fof(f66,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK5)
      | r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f30,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f30,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f25])).

fof(f139,plain,(
    ~ spl8_5 ),
    inference(avatar_contradiction_clause,[],[f138])).

fof(f138,plain,
    ( $false
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f137,f34])).

fof(f137,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl8_5 ),
    inference(backward_demodulation,[],[f122,f81])).

fof(f81,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl8_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f122,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(resolution,[],[f120,f35])).

fof(f120,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK1) ),
    inference(resolution,[],[f117,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK4)
      | r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f29,f36])).

fof(f29,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f126,plain,(
    ~ spl8_4 ),
    inference(avatar_contradiction_clause,[],[f125])).

fof(f125,plain,
    ( $false
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f124,f34])).

fof(f124,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl8_4 ),
    inference(resolution,[],[f123,f35])).

fof(f123,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),k1_xboole_0)
    | ~ spl8_4 ),
    inference(resolution,[],[f106,f116])).

fof(f106,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | r2_hidden(X0,k1_xboole_0) )
    | ~ spl8_4 ),
    inference(backward_demodulation,[],[f64,f77])).

fof(f77,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl8_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f64,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f28,f36])).

fof(f28,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f100,plain,
    ( spl8_4
    | spl8_5
    | spl8_6
    | spl8_9 ),
    inference(avatar_split_clause,[],[f73,f97,f83,f79,f75])).

fof(f73,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f47,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f45,f40])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f47,plain,(
    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f31,f40])).

fof(f31,plain,(
    m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f25])).

fof(f95,plain,
    ( spl8_4
    | spl8_5
    | spl8_6
    | spl8_8 ),
    inference(avatar_split_clause,[],[f72,f92,f83,f79,f75])).

fof(f72,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f47,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f44,f40])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f90,plain,
    ( spl8_4
    | spl8_5
    | spl8_6
    | spl8_7 ),
    inference(avatar_split_clause,[],[f71,f87,f83,f79,f75])).

fof(f71,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f47,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f43,f40])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f63,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f33,f60,f56,f52])).

fof(f33,plain,
    ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
    | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
    | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:45:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (24564)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.50  % (24558)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (24585)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.51  % (24564)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % (24577)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f162,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f63,f90,f95,f100,f126,f139,f152,f155,f158,f161])).
% 0.20/0.52  fof(f161,plain,(
% 0.20/0.52    spl8_1 | ~spl8_7),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f160])).
% 0.20/0.52  fof(f160,plain,(
% 0.20/0.52    $false | (spl8_1 | ~spl8_7)),
% 0.20/0.52    inference(subsumption_resolution,[],[f159,f116])).
% 0.20/0.52  fof(f116,plain,(
% 0.20/0.52    r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)),
% 0.20/0.52    inference(resolution,[],[f67,f41])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.20/0.52  fof(f67,plain,(
% 0.20/0.52    r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4))),
% 0.20/0.52    inference(resolution,[],[f46,f41])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 0.20/0.52    inference(definition_unfolding,[],[f32,f40])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5))),
% 0.20/0.52    inference(cnf_transformation,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ((((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)) & r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5)) & m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(sK5,k1_zfmisc_1(sK2))) & m1_subset_1(sK4,k1_zfmisc_1(sK1))) & m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f14,f24,f23,f22,f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) => (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),X4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(X5,k1_zfmisc_1(sK2))) & m1_subset_1(X4,k1_zfmisc_1(sK1))) & m1_subset_1(sK3,k1_zfmisc_1(sK0)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),X4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(X5,k1_zfmisc_1(sK2))) & m1_subset_1(X4,k1_zfmisc_1(sK1))) => (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(X5,k1_zfmisc_1(sK2))) & m1_subset_1(sK4,k1_zfmisc_1(sK1)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(X5,k1_zfmisc_1(sK2))) => (? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),sK5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,sK5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(sK5,k1_zfmisc_1(sK2)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),sK5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,sK5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) => ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)) & r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5)) & m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(flattening,[],[f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : (((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 0.20/0.52    inference(negated_conjecture,[],[f9])).
% 0.20/0.52  fof(f9,conjecture,(
% 0.20/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_mcart_1)).
% 0.20/0.52  fof(f159,plain,(
% 0.20/0.52    ~r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) | (spl8_1 | ~spl8_7)),
% 0.20/0.52    inference(backward_demodulation,[],[f54,f89])).
% 0.20/0.52  fof(f89,plain,(
% 0.20/0.52    k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6)) | ~spl8_7),
% 0.20/0.52    inference(avatar_component_clause,[],[f87])).
% 0.20/0.52  fof(f87,plain,(
% 0.20/0.52    spl8_7 <=> k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) | spl8_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f52])).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    spl8_1 <=> r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.20/0.52  fof(f158,plain,(
% 0.20/0.52    spl8_2 | ~spl8_8),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f157])).
% 0.20/0.52  fof(f157,plain,(
% 0.20/0.52    $false | (spl8_2 | ~spl8_8)),
% 0.20/0.52    inference(subsumption_resolution,[],[f156,f117])).
% 0.20/0.52  fof(f117,plain,(
% 0.20/0.52    r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)),
% 0.20/0.52    inference(resolution,[],[f67,f42])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f156,plain,(
% 0.20/0.52    ~r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) | (spl8_2 | ~spl8_8)),
% 0.20/0.52    inference(backward_demodulation,[],[f58,f94])).
% 0.20/0.52  fof(f94,plain,(
% 0.20/0.52    k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6)) | ~spl8_8),
% 0.20/0.52    inference(avatar_component_clause,[],[f92])).
% 0.20/0.52  fof(f92,plain,(
% 0.20/0.52    spl8_8 <=> k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) | spl8_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f56])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    spl8_2 <=> r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.20/0.52  fof(f155,plain,(
% 0.20/0.52    spl8_3 | ~spl8_9),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f154])).
% 0.20/0.52  fof(f154,plain,(
% 0.20/0.52    $false | (spl8_3 | ~spl8_9)),
% 0.20/0.52    inference(subsumption_resolution,[],[f153,f68])).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    r2_hidden(k2_mcart_1(sK6),sK5)),
% 0.20/0.52    inference(resolution,[],[f46,f42])).
% 0.20/0.52  fof(f153,plain,(
% 0.20/0.52    ~r2_hidden(k2_mcart_1(sK6),sK5) | (spl8_3 | ~spl8_9)),
% 0.20/0.52    inference(backward_demodulation,[],[f62,f99])).
% 0.20/0.52  fof(f99,plain,(
% 0.20/0.52    k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6) | ~spl8_9),
% 0.20/0.52    inference(avatar_component_clause,[],[f97])).
% 0.20/0.52  fof(f97,plain,(
% 0.20/0.52    spl8_9 <=> k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    ~r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) | spl8_3),
% 0.20/0.52    inference(avatar_component_clause,[],[f60])).
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    spl8_3 <=> r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.20/0.52  fof(f152,plain,(
% 0.20/0.52    ~spl8_6),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f151])).
% 0.20/0.52  fof(f151,plain,(
% 0.20/0.52    $false | ~spl8_6),
% 0.20/0.52    inference(subsumption_resolution,[],[f150,f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    v1_xboole_0(k1_xboole_0)),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    v1_xboole_0(k1_xboole_0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.52  fof(f150,plain,(
% 0.20/0.52    ~v1_xboole_0(k1_xboole_0) | ~spl8_6),
% 0.20/0.52    inference(backward_demodulation,[],[f115,f85])).
% 0.20/0.52  fof(f85,plain,(
% 0.20/0.52    k1_xboole_0 = sK2 | ~spl8_6),
% 0.20/0.52    inference(avatar_component_clause,[],[f83])).
% 0.20/0.52  fof(f83,plain,(
% 0.20/0.52    spl8_6 <=> k1_xboole_0 = sK2),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.20/0.52  fof(f115,plain,(
% 0.20/0.52    ~v1_xboole_0(sK2)),
% 0.20/0.52    inference(resolution,[],[f114,f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.52    inference(unused_predicate_definition_removal,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.52  fof(f114,plain,(
% 0.20/0.52    r2_hidden(k2_mcart_1(sK6),sK2)),
% 0.20/0.52    inference(resolution,[],[f66,f68])).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,sK5) | r2_hidden(X0,sK2)) )),
% 0.20/0.52    inference(resolution,[],[f30,f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 0.20/0.52    inference(cnf_transformation,[],[f25])).
% 0.20/0.52  fof(f139,plain,(
% 0.20/0.52    ~spl8_5),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f138])).
% 0.20/0.52  fof(f138,plain,(
% 0.20/0.52    $false | ~spl8_5),
% 0.20/0.52    inference(subsumption_resolution,[],[f137,f34])).
% 0.20/0.52  fof(f137,plain,(
% 0.20/0.52    ~v1_xboole_0(k1_xboole_0) | ~spl8_5),
% 0.20/0.52    inference(backward_demodulation,[],[f122,f81])).
% 0.20/0.52  fof(f81,plain,(
% 0.20/0.52    k1_xboole_0 = sK1 | ~spl8_5),
% 0.20/0.52    inference(avatar_component_clause,[],[f79])).
% 0.20/0.52  fof(f79,plain,(
% 0.20/0.52    spl8_5 <=> k1_xboole_0 = sK1),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.20/0.52  fof(f122,plain,(
% 0.20/0.52    ~v1_xboole_0(sK1)),
% 0.20/0.52    inference(resolution,[],[f120,f35])).
% 0.20/0.52  fof(f120,plain,(
% 0.20/0.52    r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK1)),
% 0.20/0.52    inference(resolution,[],[f117,f65])).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,sK4) | r2_hidden(X0,sK1)) )),
% 0.20/0.52    inference(resolution,[],[f29,f36])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 0.20/0.52    inference(cnf_transformation,[],[f25])).
% 0.20/0.52  fof(f126,plain,(
% 0.20/0.52    ~spl8_4),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f125])).
% 0.20/0.52  fof(f125,plain,(
% 0.20/0.52    $false | ~spl8_4),
% 0.20/0.52    inference(subsumption_resolution,[],[f124,f34])).
% 0.20/0.52  fof(f124,plain,(
% 0.20/0.52    ~v1_xboole_0(k1_xboole_0) | ~spl8_4),
% 0.20/0.52    inference(resolution,[],[f123,f35])).
% 0.20/0.52  fof(f123,plain,(
% 0.20/0.52    r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),k1_xboole_0) | ~spl8_4),
% 0.20/0.52    inference(resolution,[],[f106,f116])).
% 0.20/0.52  fof(f106,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,sK3) | r2_hidden(X0,k1_xboole_0)) ) | ~spl8_4),
% 0.20/0.52    inference(backward_demodulation,[],[f64,f77])).
% 0.20/0.52  fof(f77,plain,(
% 0.20/0.52    k1_xboole_0 = sK0 | ~spl8_4),
% 0.20/0.52    inference(avatar_component_clause,[],[f75])).
% 0.20/0.52  fof(f75,plain,(
% 0.20/0.52    spl8_4 <=> k1_xboole_0 = sK0),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.20/0.52  fof(f64,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,sK3) | r2_hidden(X0,sK0)) )),
% 0.20/0.52    inference(resolution,[],[f28,f36])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.20/0.52    inference(cnf_transformation,[],[f25])).
% 0.20/0.52  fof(f100,plain,(
% 0.20/0.52    spl8_4 | spl8_5 | spl8_6 | spl8_9),
% 0.20/0.52    inference(avatar_split_clause,[],[f73,f97,f83,f79,f75])).
% 0.20/0.52  fof(f73,plain,(
% 0.20/0.52    k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.20/0.52    inference(resolution,[],[f47,f48])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(definition_unfolding,[],[f45,f40])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.20/0.52    inference(definition_unfolding,[],[f31,f40])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.20/0.52    inference(cnf_transformation,[],[f25])).
% 0.20/0.52  fof(f95,plain,(
% 0.20/0.52    spl8_4 | spl8_5 | spl8_6 | spl8_8),
% 0.20/0.52    inference(avatar_split_clause,[],[f72,f92,f83,f79,f75])).
% 0.20/0.52  fof(f72,plain,(
% 0.20/0.52    k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.20/0.52    inference(resolution,[],[f47,f49])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(definition_unfolding,[],[f44,f40])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f90,plain,(
% 0.20/0.52    spl8_4 | spl8_5 | spl8_6 | spl8_7),
% 0.20/0.52    inference(avatar_split_clause,[],[f71,f87,f83,f79,f75])).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.20/0.52    inference(resolution,[],[f47,f50])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(definition_unfolding,[],[f43,f40])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    ~spl8_1 | ~spl8_2 | ~spl8_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f33,f60,f56,f52])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ~r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)),
% 0.20/0.52    inference(cnf_transformation,[],[f25])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (24564)------------------------------
% 0.20/0.52  % (24564)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (24564)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (24564)Memory used [KB]: 10746
% 0.20/0.52  % (24564)Time elapsed: 0.098 s
% 0.20/0.52  % (24564)------------------------------
% 0.20/0.52  % (24564)------------------------------
% 1.27/0.52  % (24555)Success in time 0.164 s
%------------------------------------------------------------------------------
