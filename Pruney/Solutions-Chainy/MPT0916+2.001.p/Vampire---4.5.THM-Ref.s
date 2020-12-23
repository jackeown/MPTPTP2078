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
% DateTime   : Thu Dec  3 12:59:37 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 322 expanded)
%              Number of leaves         :   28 ( 134 expanded)
%              Depth                    :   12
%              Number of atoms          :  354 (1520 expanded)
%              Number of equality atoms :   53 ( 105 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f183,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f114,f120,f126,f129,f135,f137,f140,f152,f156,f158,f160,f165,f170,f172,f180,f182])).

fof(f182,plain,(
    ~ spl8_9 ),
    inference(avatar_contradiction_clause,[],[f181])).

fof(f181,plain,
    ( $false
    | ~ spl8_9 ),
    inference(resolution,[],[f127,f87])).

fof(f87,plain,
    ( v1_xboole_0(sK5)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl8_9
  <=> v1_xboole_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f127,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(resolution,[],[f91,f31])).

fof(f31,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK7(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f20,f21])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK7(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
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

fof(f91,plain,(
    r2_hidden(k2_mcart_1(sK6),sK5) ),
    inference(resolution,[],[f35,f39])).

fof(f39,plain,(
    r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f27,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f27,plain,(
    r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
      | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
      | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) )
    & r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5))
    & m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))
    & m1_subset_1(sK5,k1_zfmisc_1(sK2))
    & m1_subset_1(sK4,k1_zfmisc_1(sK1))
    & m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f10,f17,f16,f15,f14])).

fof(f14,plain,
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

fof(f15,plain,
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

fof(f16,plain,
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

fof(f17,plain,
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

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
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
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
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

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f180,plain,
    ( ~ spl8_17
    | spl8_9
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f179,f103,f85,f147])).

fof(f147,plain,
    ( spl8_17
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f103,plain,
    ( spl8_12
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f179,plain,
    ( v1_xboole_0(sK5)
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ spl8_12 ),
    inference(resolution,[],[f173,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f173,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_12 ),
    inference(backward_demodulation,[],[f25,f105])).

fof(f105,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f103])).

fof(f25,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f172,plain,
    ( ~ spl8_6
    | spl8_7 ),
    inference(avatar_split_clause,[],[f171,f76,f72])).

fof(f72,plain,
    ( spl8_6
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f76,plain,
    ( spl8_7
  <=> v1_xboole_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f171,plain,
    ( v1_xboole_0(sK4)
    | ~ v1_xboole_0(sK1) ),
    inference(resolution,[],[f24,f30])).

fof(f24,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f170,plain,(
    ~ spl8_7 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | ~ spl8_7 ),
    inference(resolution,[],[f134,f78])).

fof(f78,plain,
    ( v1_xboole_0(sK4)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f76])).

fof(f134,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(resolution,[],[f130,f31])).

fof(f130,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) ),
    inference(resolution,[],[f89,f35])).

fof(f89,plain,(
    r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4)) ),
    inference(resolution,[],[f34,f39])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f165,plain,
    ( spl8_6
    | ~ spl8_11 ),
    inference(avatar_contradiction_clause,[],[f164])).

fof(f164,plain,
    ( $false
    | spl8_6
    | ~ spl8_11 ),
    inference(resolution,[],[f163,f29])).

fof(f29,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f163,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl8_6
    | ~ spl8_11 ),
    inference(backward_demodulation,[],[f74,f101])).

fof(f101,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl8_11
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f74,plain,
    ( ~ v1_xboole_0(sK1)
    | spl8_6 ),
    inference(avatar_component_clause,[],[f72])).

fof(f160,plain,
    ( ~ spl8_4
    | spl8_5 ),
    inference(avatar_split_clause,[],[f159,f67,f63])).

fof(f63,plain,
    ( spl8_4
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f67,plain,
    ( spl8_5
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f159,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(sK0) ),
    inference(resolution,[],[f23,f30])).

fof(f23,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f158,plain,(
    ~ spl8_5 ),
    inference(avatar_contradiction_clause,[],[f157])).

fof(f157,plain,
    ( $false
    | ~ spl8_5 ),
    inference(resolution,[],[f139,f69])).

fof(f69,plain,
    ( v1_xboole_0(sK3)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f67])).

fof(f139,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(resolution,[],[f131,f31])).

fof(f131,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) ),
    inference(resolution,[],[f89,f34])).

fof(f156,plain,(
    spl8_17 ),
    inference(avatar_contradiction_clause,[],[f155])).

fof(f155,plain,
    ( $false
    | spl8_17 ),
    inference(resolution,[],[f149,f29])).

fof(f149,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl8_17 ),
    inference(avatar_component_clause,[],[f147])).

fof(f152,plain,
    ( spl8_4
    | ~ spl8_10 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | spl8_4
    | ~ spl8_10 ),
    inference(resolution,[],[f144,f29])).

fof(f144,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl8_4
    | ~ spl8_10 ),
    inference(backward_demodulation,[],[f65,f97])).

fof(f97,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl8_10
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f65,plain,
    ( ~ v1_xboole_0(sK0)
    | spl8_4 ),
    inference(avatar_component_clause,[],[f63])).

fof(f140,plain,(
    spl8_16 ),
    inference(avatar_contradiction_clause,[],[f138])).

fof(f138,plain,
    ( $false
    | spl8_16 ),
    inference(resolution,[],[f131,f125])).

fof(f125,plain,
    ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)
    | spl8_16 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl8_16
  <=> r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f137,plain,(
    spl8_13 ),
    inference(avatar_contradiction_clause,[],[f136])).

fof(f136,plain,
    ( $false
    | spl8_13 ),
    inference(resolution,[],[f109,f40])).

fof(f40,plain,(
    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f26,f33])).

fof(f26,plain,(
    m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f109,plain,
    ( ~ m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | spl8_13 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl8_13
  <=> m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f135,plain,(
    spl8_15 ),
    inference(avatar_contradiction_clause,[],[f133])).

fof(f133,plain,
    ( $false
    | spl8_15 ),
    inference(resolution,[],[f130,f119])).

fof(f119,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)
    | spl8_15 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl8_15
  <=> r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f129,plain,(
    spl8_14 ),
    inference(avatar_contradiction_clause,[],[f128])).

fof(f128,plain,
    ( $false
    | spl8_14 ),
    inference(resolution,[],[f113,f91])).

fof(f113,plain,
    ( ~ r2_hidden(k2_mcart_1(sK6),sK5)
    | spl8_14 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl8_14
  <=> r2_hidden(k2_mcart_1(sK6),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f126,plain,
    ( spl8_10
    | spl8_11
    | spl8_12
    | ~ spl8_13
    | ~ spl8_16
    | spl8_1 ),
    inference(avatar_split_clause,[],[f121,f45,f123,f107,f103,f99,f95])).

fof(f45,plain,
    ( spl8_1
  <=> r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f121,plain,
    ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)
    | ~ m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl8_1 ),
    inference(superposition,[],[f47,f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f36,f33])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f47,plain,
    ( ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f120,plain,
    ( spl8_10
    | spl8_11
    | spl8_12
    | ~ spl8_13
    | ~ spl8_15
    | spl8_2 ),
    inference(avatar_split_clause,[],[f115,f49,f117,f107,f103,f99,f95])).

fof(f49,plain,
    ( spl8_2
  <=> r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f115,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)
    | ~ m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl8_2 ),
    inference(superposition,[],[f51,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f37,f33])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f51,plain,
    ( ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f114,plain,
    ( spl8_10
    | spl8_11
    | spl8_12
    | ~ spl8_13
    | ~ spl8_14
    | spl8_3 ),
    inference(avatar_split_clause,[],[f93,f53,f111,f107,f103,f99,f95])).

fof(f53,plain,
    ( spl8_3
  <=> r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f93,plain,
    ( ~ r2_hidden(k2_mcart_1(sK6),sK5)
    | ~ m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl8_3 ),
    inference(superposition,[],[f55,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f38,f33])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f55,plain,
    ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f56,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f28,f53,f49,f45])).

fof(f28,plain,
    ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
    | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
    | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:03:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.42  % (9168)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.43  % (9168)Refutation not found, incomplete strategy% (9168)------------------------------
% 0.20/0.43  % (9168)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (9168)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.43  
% 0.20/0.43  % (9168)Memory used [KB]: 10746
% 0.20/0.43  % (9168)Time elapsed: 0.005 s
% 0.20/0.43  % (9168)------------------------------
% 0.20/0.43  % (9168)------------------------------
% 0.20/0.47  % (9165)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.47  % (9163)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (9161)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (9160)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.48  % (9172)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.48  % (9161)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f183,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f56,f114,f120,f126,f129,f135,f137,f140,f152,f156,f158,f160,f165,f170,f172,f180,f182])).
% 0.20/0.48  fof(f182,plain,(
% 0.20/0.48    ~spl8_9),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f181])).
% 0.20/0.48  fof(f181,plain,(
% 0.20/0.48    $false | ~spl8_9),
% 0.20/0.48    inference(resolution,[],[f127,f87])).
% 0.20/0.48  fof(f87,plain,(
% 0.20/0.48    v1_xboole_0(sK5) | ~spl8_9),
% 0.20/0.48    inference(avatar_component_clause,[],[f85])).
% 0.20/0.48  fof(f85,plain,(
% 0.20/0.48    spl8_9 <=> v1_xboole_0(sK5)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.20/0.48  fof(f127,plain,(
% 0.20/0.48    ~v1_xboole_0(sK5)),
% 0.20/0.48    inference(resolution,[],[f91,f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK7(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f20,f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK7(X0),X0))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.48    inference(rectify,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.48    inference(nnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.48  fof(f91,plain,(
% 0.20/0.48    r2_hidden(k2_mcart_1(sK6),sK5)),
% 0.20/0.48    inference(resolution,[],[f35,f39])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 0.20/0.48    inference(definition_unfolding,[],[f27,f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5))),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ((((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)) & r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5)) & m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(sK5,k1_zfmisc_1(sK2))) & m1_subset_1(sK4,k1_zfmisc_1(sK1))) & m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f10,f17,f16,f15,f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) => (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),X4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(X5,k1_zfmisc_1(sK2))) & m1_subset_1(X4,k1_zfmisc_1(sK1))) & m1_subset_1(sK3,k1_zfmisc_1(sK0)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),X4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(X5,k1_zfmisc_1(sK2))) & m1_subset_1(X4,k1_zfmisc_1(sK1))) => (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(X5,k1_zfmisc_1(sK2))) & m1_subset_1(sK4,k1_zfmisc_1(sK1)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(X5,k1_zfmisc_1(sK2))) => (? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),sK5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,sK5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(sK5,k1_zfmisc_1(sK2)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),sK5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,sK5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) => ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)) & r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5)) & m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(flattening,[],[f9])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : (((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 0.20/0.48    inference(negated_conjecture,[],[f7])).
% 0.20/0.48  fof(f7,conjecture,(
% 0.20/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_mcart_1)).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.20/0.48  fof(f180,plain,(
% 0.20/0.48    ~spl8_17 | spl8_9 | ~spl8_12),
% 0.20/0.48    inference(avatar_split_clause,[],[f179,f103,f85,f147])).
% 0.20/0.48  fof(f147,plain,(
% 0.20/0.48    spl8_17 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.20/0.48  fof(f103,plain,(
% 0.20/0.48    spl8_12 <=> k1_xboole_0 = sK2),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.20/0.48  fof(f179,plain,(
% 0.20/0.48    v1_xboole_0(sK5) | ~v1_xboole_0(k1_xboole_0) | ~spl8_12),
% 0.20/0.48    inference(resolution,[],[f173,f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.20/0.48  fof(f173,plain,(
% 0.20/0.48    m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) | ~spl8_12),
% 0.20/0.48    inference(backward_demodulation,[],[f25,f105])).
% 0.20/0.48  fof(f105,plain,(
% 0.20/0.48    k1_xboole_0 = sK2 | ~spl8_12),
% 0.20/0.48    inference(avatar_component_clause,[],[f103])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f172,plain,(
% 0.20/0.48    ~spl8_6 | spl8_7),
% 0.20/0.48    inference(avatar_split_clause,[],[f171,f76,f72])).
% 0.20/0.48  fof(f72,plain,(
% 0.20/0.48    spl8_6 <=> v1_xboole_0(sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.20/0.48  fof(f76,plain,(
% 0.20/0.48    spl8_7 <=> v1_xboole_0(sK4)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.20/0.48  fof(f171,plain,(
% 0.20/0.48    v1_xboole_0(sK4) | ~v1_xboole_0(sK1)),
% 0.20/0.48    inference(resolution,[],[f24,f30])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f170,plain,(
% 0.20/0.48    ~spl8_7),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f169])).
% 0.20/0.48  fof(f169,plain,(
% 0.20/0.48    $false | ~spl8_7),
% 0.20/0.48    inference(resolution,[],[f134,f78])).
% 0.20/0.48  fof(f78,plain,(
% 0.20/0.48    v1_xboole_0(sK4) | ~spl8_7),
% 0.20/0.48    inference(avatar_component_clause,[],[f76])).
% 0.20/0.48  fof(f134,plain,(
% 0.20/0.48    ~v1_xboole_0(sK4)),
% 0.20/0.48    inference(resolution,[],[f130,f31])).
% 0.20/0.48  fof(f130,plain,(
% 0.20/0.48    r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)),
% 0.20/0.48    inference(resolution,[],[f89,f35])).
% 0.20/0.48  fof(f89,plain,(
% 0.20/0.48    r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4))),
% 0.20/0.48    inference(resolution,[],[f34,f39])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f165,plain,(
% 0.20/0.48    spl8_6 | ~spl8_11),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f164])).
% 0.20/0.48  fof(f164,plain,(
% 0.20/0.48    $false | (spl8_6 | ~spl8_11)),
% 0.20/0.48    inference(resolution,[],[f163,f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    v1_xboole_0(k1_xboole_0)),
% 0.20/0.48    inference(cnf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    v1_xboole_0(k1_xboole_0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.48  fof(f163,plain,(
% 0.20/0.48    ~v1_xboole_0(k1_xboole_0) | (spl8_6 | ~spl8_11)),
% 0.20/0.48    inference(backward_demodulation,[],[f74,f101])).
% 0.20/0.48  fof(f101,plain,(
% 0.20/0.48    k1_xboole_0 = sK1 | ~spl8_11),
% 0.20/0.48    inference(avatar_component_clause,[],[f99])).
% 0.20/0.48  fof(f99,plain,(
% 0.20/0.48    spl8_11 <=> k1_xboole_0 = sK1),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.20/0.48  fof(f74,plain,(
% 0.20/0.48    ~v1_xboole_0(sK1) | spl8_6),
% 0.20/0.48    inference(avatar_component_clause,[],[f72])).
% 0.20/0.48  fof(f160,plain,(
% 0.20/0.48    ~spl8_4 | spl8_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f159,f67,f63])).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    spl8_4 <=> v1_xboole_0(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    spl8_5 <=> v1_xboole_0(sK3)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.20/0.48  fof(f159,plain,(
% 0.20/0.48    v1_xboole_0(sK3) | ~v1_xboole_0(sK0)),
% 0.20/0.48    inference(resolution,[],[f23,f30])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f158,plain,(
% 0.20/0.48    ~spl8_5),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f157])).
% 0.20/0.48  fof(f157,plain,(
% 0.20/0.48    $false | ~spl8_5),
% 0.20/0.48    inference(resolution,[],[f139,f69])).
% 0.20/0.48  fof(f69,plain,(
% 0.20/0.48    v1_xboole_0(sK3) | ~spl8_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f67])).
% 0.20/0.48  fof(f139,plain,(
% 0.20/0.48    ~v1_xboole_0(sK3)),
% 0.20/0.48    inference(resolution,[],[f131,f31])).
% 0.20/0.48  fof(f131,plain,(
% 0.20/0.48    r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)),
% 0.20/0.48    inference(resolution,[],[f89,f34])).
% 0.20/0.48  fof(f156,plain,(
% 0.20/0.48    spl8_17),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f155])).
% 0.20/0.48  fof(f155,plain,(
% 0.20/0.48    $false | spl8_17),
% 0.20/0.48    inference(resolution,[],[f149,f29])).
% 0.20/0.48  fof(f149,plain,(
% 0.20/0.48    ~v1_xboole_0(k1_xboole_0) | spl8_17),
% 0.20/0.48    inference(avatar_component_clause,[],[f147])).
% 0.20/0.48  fof(f152,plain,(
% 0.20/0.48    spl8_4 | ~spl8_10),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f151])).
% 0.20/0.48  fof(f151,plain,(
% 0.20/0.48    $false | (spl8_4 | ~spl8_10)),
% 0.20/0.48    inference(resolution,[],[f144,f29])).
% 0.20/0.48  fof(f144,plain,(
% 0.20/0.48    ~v1_xboole_0(k1_xboole_0) | (spl8_4 | ~spl8_10)),
% 0.20/0.48    inference(backward_demodulation,[],[f65,f97])).
% 0.20/0.48  fof(f97,plain,(
% 0.20/0.48    k1_xboole_0 = sK0 | ~spl8_10),
% 0.20/0.48    inference(avatar_component_clause,[],[f95])).
% 0.20/0.48  fof(f95,plain,(
% 0.20/0.48    spl8_10 <=> k1_xboole_0 = sK0),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    ~v1_xboole_0(sK0) | spl8_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f63])).
% 0.20/0.48  fof(f140,plain,(
% 0.20/0.48    spl8_16),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f138])).
% 0.20/0.48  fof(f138,plain,(
% 0.20/0.48    $false | spl8_16),
% 0.20/0.48    inference(resolution,[],[f131,f125])).
% 0.20/0.48  fof(f125,plain,(
% 0.20/0.48    ~r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) | spl8_16),
% 0.20/0.48    inference(avatar_component_clause,[],[f123])).
% 0.20/0.48  fof(f123,plain,(
% 0.20/0.48    spl8_16 <=> r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.20/0.48  fof(f137,plain,(
% 0.20/0.48    spl8_13),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f136])).
% 0.20/0.48  fof(f136,plain,(
% 0.20/0.48    $false | spl8_13),
% 0.20/0.48    inference(resolution,[],[f109,f40])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.20/0.48    inference(definition_unfolding,[],[f26,f33])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f109,plain,(
% 0.20/0.48    ~m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | spl8_13),
% 0.20/0.48    inference(avatar_component_clause,[],[f107])).
% 0.20/0.48  fof(f107,plain,(
% 0.20/0.48    spl8_13 <=> m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.20/0.48  fof(f135,plain,(
% 0.20/0.48    spl8_15),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f133])).
% 0.20/0.48  fof(f133,plain,(
% 0.20/0.48    $false | spl8_15),
% 0.20/0.48    inference(resolution,[],[f130,f119])).
% 0.20/0.48  fof(f119,plain,(
% 0.20/0.48    ~r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) | spl8_15),
% 0.20/0.48    inference(avatar_component_clause,[],[f117])).
% 0.20/0.48  fof(f117,plain,(
% 0.20/0.48    spl8_15 <=> r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.20/0.48  fof(f129,plain,(
% 0.20/0.48    spl8_14),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f128])).
% 0.20/0.48  fof(f128,plain,(
% 0.20/0.48    $false | spl8_14),
% 0.20/0.48    inference(resolution,[],[f113,f91])).
% 0.20/0.48  fof(f113,plain,(
% 0.20/0.48    ~r2_hidden(k2_mcart_1(sK6),sK5) | spl8_14),
% 0.20/0.48    inference(avatar_component_clause,[],[f111])).
% 0.20/0.48  fof(f111,plain,(
% 0.20/0.48    spl8_14 <=> r2_hidden(k2_mcart_1(sK6),sK5)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.20/0.48  fof(f126,plain,(
% 0.20/0.48    spl8_10 | spl8_11 | spl8_12 | ~spl8_13 | ~spl8_16 | spl8_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f121,f45,f123,f107,f103,f99,f95])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    spl8_1 <=> r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.20/0.48  fof(f121,plain,(
% 0.20/0.48    ~r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) | ~m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl8_1),
% 0.20/0.48    inference(superposition,[],[f47,f43])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(definition_unfolding,[],[f36,f33])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) | spl8_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f45])).
% 0.20/0.48  fof(f120,plain,(
% 0.20/0.48    spl8_10 | spl8_11 | spl8_12 | ~spl8_13 | ~spl8_15 | spl8_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f115,f49,f117,f107,f103,f99,f95])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    spl8_2 <=> r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.20/0.48  fof(f115,plain,(
% 0.20/0.48    ~r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) | ~m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl8_2),
% 0.20/0.48    inference(superposition,[],[f51,f42])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(definition_unfolding,[],[f37,f33])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) | spl8_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f49])).
% 0.20/0.48  fof(f114,plain,(
% 0.20/0.48    spl8_10 | spl8_11 | spl8_12 | ~spl8_13 | ~spl8_14 | spl8_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f93,f53,f111,f107,f103,f99,f95])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    spl8_3 <=> r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.20/0.48  fof(f93,plain,(
% 0.20/0.48    ~r2_hidden(k2_mcart_1(sK6),sK5) | ~m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl8_3),
% 0.20/0.48    inference(superposition,[],[f55,f41])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(definition_unfolding,[],[f38,f33])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    ~r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) | spl8_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f53])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    ~spl8_1 | ~spl8_2 | ~spl8_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f28,f53,f49,f45])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ~r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (9161)------------------------------
% 0.20/0.48  % (9161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (9161)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (9161)Memory used [KB]: 6140
% 0.20/0.48  % (9161)Time elapsed: 0.058 s
% 0.20/0.48  % (9161)------------------------------
% 0.20/0.48  % (9161)------------------------------
% 0.20/0.48  % (9156)Success in time 0.119 s
%------------------------------------------------------------------------------
