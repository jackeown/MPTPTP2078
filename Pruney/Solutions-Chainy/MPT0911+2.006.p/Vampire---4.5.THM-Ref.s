%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:29 EST 2020

% Result     : Theorem 2.08s
% Output     : Refutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 533 expanded)
%              Number of leaves         :   27 ( 154 expanded)
%              Depth                    :   17
%              Number of atoms          :  566 (2546 expanded)
%              Number of equality atoms :  230 (1269 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3024,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f147,f190,f192,f412,f1140,f1159,f1163,f3001])).

fof(f3001,plain,
    ( ~ spl14_3
    | ~ spl14_5 ),
    inference(avatar_contradiction_clause,[],[f3000])).

fof(f3000,plain,
    ( $false
    | ~ spl14_3
    | ~ spl14_5 ),
    inference(subsumption_resolution,[],[f2864,f2689])).

fof(f2689,plain,
    ( ! [X3] : k1_xboole_0 = X3
    | ~ spl14_3 ),
    inference(subsumption_resolution,[],[f2688,f47])).

fof(f47,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f18,f26])).

fof(f26,plain,
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

fof(f2688,plain,
    ( ! [X3] :
        ( k1_xboole_0 = X3
        | k1_xboole_0 = sK0 )
    | ~ spl14_3 ),
    inference(subsumption_resolution,[],[f2687,f48])).

fof(f48,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f27])).

fof(f2687,plain,
    ( ! [X3] :
        ( k1_xboole_0 = X3
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0 )
    | ~ spl14_3 ),
    inference(subsumption_resolution,[],[f2686,f49])).

fof(f49,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f27])).

fof(f2686,plain,
    ( ! [X3] :
        ( k1_xboole_0 = X3
        | k1_xboole_0 = sK2
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0 )
    | ~ spl14_3 ),
    inference(subsumption_resolution,[],[f2662,f2029])).

fof(f2029,plain,(
    ! [X3] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X3) ),
    inference(forward_demodulation,[],[f2021,f2014])).

fof(f2014,plain,(
    k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f105,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X3
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f86,f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f81,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f81,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X3
      | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 )
      & ( k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 )
      & ( k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0
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
    <=> k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

fof(f2021,plain,(
    ! [X3] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),X3) ),
    inference(superposition,[],[f106,f105])).

fof(f106,plain,(
    ! [X0,X3,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f85,f87])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f2662,plain,
    ( ! [X3] :
        ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = sK2
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0 )
    | ~ spl14_3 ),
    inference(superposition,[],[f97,f2343])).

fof(f2343,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl14_3 ),
    inference(resolution,[],[f2002,f137])).

fof(f137,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl14_3 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl14_3
  <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_3])])).

fof(f2002,plain,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f55,f53])).

fof(f53,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK5(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
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

fof(f55,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK6(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK6(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f20,f32])).

fof(f32,plain,(
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

fof(f20,plain,(
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

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f82,f87])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f2864,plain,
    ( k1_xboole_0 != sK3
    | ~ spl14_3
    | ~ spl14_5 ),
    inference(backward_demodulation,[],[f2344,f2689])).

fof(f2344,plain,
    ( sK3 != k7_mcart_1(sK0,sK1,sK2,k1_xboole_0)
    | ~ spl14_5 ),
    inference(backward_demodulation,[],[f50,f2341])).

fof(f2341,plain,
    ( k1_xboole_0 = sK4
    | ~ spl14_5 ),
    inference(resolution,[],[f2002,f146])).

fof(f146,plain,
    ( v1_xboole_0(sK4)
    | ~ spl14_5 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl14_5
  <=> v1_xboole_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_5])])).

fof(f50,plain,(
    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f1163,plain,
    ( spl14_2
    | ~ spl14_4 ),
    inference(avatar_contradiction_clause,[],[f1162])).

fof(f1162,plain,
    ( $false
    | spl14_2
    | ~ spl14_4 ),
    inference(subsumption_resolution,[],[f131,f965])).

fof(f965,plain,
    ( sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))
    | ~ spl14_4 ),
    inference(backward_demodulation,[],[f964,f958])).

fof(f958,plain,
    ( k2_mcart_1(sK4) = sK11(k2_zfmisc_1(sK0,sK1),sK2,sK4)
    | ~ spl14_4 ),
    inference(superposition,[],[f59,f910])).

fof(f910,plain,
    ( sK4 = k4_tarski(sK10(k2_zfmisc_1(sK0,sK1),sK2,sK4),sK11(k2_zfmisc_1(sK0,sK1),sK2,sK4))
    | ~ spl14_4 ),
    inference(resolution,[],[f141,f102])).

fof(f102,plain,(
    ! [X0,X8,X1] :
      ( ~ r2_hidden(X8,k2_zfmisc_1(X0,X1))
      | k4_tarski(sK10(X0,X1,X8),sK11(X0,X1,X8)) = X8 ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X8,X1] :
      ( k4_tarski(sK10(X0,X1,X8),sK11(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK7(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( ( sK7(X0,X1,X2) = k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2))
              & r2_hidden(sK9(X0,X1,X2),X1)
              & r2_hidden(sK8(X0,X1,X2),X0) )
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK10(X0,X1,X8),sK11(X0,X1,X8)) = X8
                & r2_hidden(sK11(X0,X1,X8),X1)
                & r2_hidden(sK10(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10,sK11])],[f36,f39,f38,f37])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != X3
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k4_tarski(X6,X7) = X3
                & r2_hidden(X7,X1)
                & r2_hidden(X6,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k4_tarski(X4,X5) != sK7(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK7(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK7(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK7(X0,X1,X2) = k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2))
        & r2_hidden(sK9(X0,X1,X2),X1)
        & r2_hidden(sK8(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK10(X0,X1,X8),sK11(X0,X1,X8)) = X8
        & r2_hidden(sK11(X0,X1,X8),X1)
        & r2_hidden(sK10(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k4_tarski(X6,X7) = X3
                  & r2_hidden(X7,X1)
                  & r2_hidden(X6,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ? [X11,X12] :
                  ( k4_tarski(X11,X12) = X8
                  & r2_hidden(X12,X1)
                  & r2_hidden(X11,X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) ) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f141,plain,
    ( r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl14_4 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl14_4
  <=> r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_4])])).

fof(f59,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f964,plain,
    ( sK4 = k4_tarski(k1_mcart_1(sK4),sK11(k2_zfmisc_1(sK0,sK1),sK2,sK4))
    | ~ spl14_4 ),
    inference(backward_demodulation,[],[f910,f957])).

fof(f957,plain,
    ( k1_mcart_1(sK4) = sK10(k2_zfmisc_1(sK0,sK1),sK2,sK4)
    | ~ spl14_4 ),
    inference(superposition,[],[f58,f910])).

fof(f58,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f131,plain,
    ( sK4 != k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))
    | spl14_2 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl14_2
  <=> sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).

fof(f1159,plain,
    ( spl14_3
    | ~ spl14_24 ),
    inference(avatar_contradiction_clause,[],[f1158])).

fof(f1158,plain,
    ( $false
    | spl14_3
    | ~ spl14_24 ),
    inference(subsumption_resolution,[],[f348,f1122])).

fof(f1122,plain,
    ( ~ v1_xboole_0(sK0)
    | spl14_3 ),
    inference(resolution,[],[f1027,f53])).

fof(f1027,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK5(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)))),sK0)
    | spl14_3 ),
    inference(resolution,[],[f944,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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

fof(f944,plain,
    ( r2_hidden(k1_mcart_1(sK5(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),k2_zfmisc_1(sK0,sK1))
    | spl14_3 ),
    inference(resolution,[],[f904,f67])).

fof(f904,plain,
    ( r2_hidden(sK5(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | spl14_3 ),
    inference(resolution,[],[f136,f54])).

fof(f54,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK5(X0),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f136,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | spl14_3 ),
    inference(avatar_component_clause,[],[f135])).

fof(f348,plain,
    ( v1_xboole_0(sK0)
    | ~ spl14_24 ),
    inference(avatar_component_clause,[],[f346])).

fof(f346,plain,
    ( spl14_24
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_24])])).

fof(f1140,plain,
    ( ~ spl14_2
    | ~ spl14_4
    | ~ spl14_10
    | spl14_24 ),
    inference(avatar_contradiction_clause,[],[f1139])).

fof(f1139,plain,
    ( $false
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_10
    | spl14_24 ),
    inference(subsumption_resolution,[],[f1138,f189])).

fof(f189,plain,
    ( m1_subset_1(k2_mcart_1(sK4),sK2)
    | ~ spl14_10 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl14_10
  <=> m1_subset_1(k2_mcart_1(sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_10])])).

fof(f1138,plain,
    ( ~ m1_subset_1(k2_mcart_1(sK4),sK2)
    | ~ spl14_2
    | ~ spl14_4
    | spl14_24 ),
    inference(subsumption_resolution,[],[f1137,f179])).

fof(f179,plain,(
    sK3 != k2_mcart_1(sK4) ),
    inference(superposition,[],[f50,f123])).

fof(f123,plain,(
    k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) ),
    inference(subsumption_resolution,[],[f122,f47])).

fof(f122,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f121,f48])).

fof(f121,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f111,f49])).

fof(f111,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f89,f90])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f79,f66])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

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

fof(f89,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f45,f66])).

fof(f45,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f1137,plain,
    ( sK3 = k2_mcart_1(sK4)
    | ~ m1_subset_1(k2_mcart_1(sK4),sK2)
    | ~ spl14_2
    | ~ spl14_4
    | spl14_24 ),
    inference(trivial_inequality_removal,[],[f1136])).

fof(f1136,plain,
    ( sK4 != sK4
    | sK3 = k2_mcart_1(sK4)
    | ~ m1_subset_1(k2_mcart_1(sK4),sK2)
    | ~ spl14_2
    | ~ spl14_4
    | spl14_24 ),
    inference(superposition,[],[f1022,f132])).

fof(f132,plain,
    ( sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))
    | ~ spl14_2 ),
    inference(avatar_component_clause,[],[f130])).

fof(f1022,plain,
    ( ! [X3] :
        ( sK4 != k4_tarski(k1_mcart_1(sK4),X3)
        | sK3 = X3
        | ~ m1_subset_1(X3,sK2) )
    | ~ spl14_4
    | spl14_24 ),
    inference(subsumption_resolution,[],[f1021,f951])).

fof(f951,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)
    | ~ spl14_4
    | spl14_24 ),
    inference(subsumption_resolution,[],[f949,f347])).

fof(f347,plain,
    ( ~ v1_xboole_0(sK0)
    | spl14_24 ),
    inference(avatar_component_clause,[],[f346])).

fof(f949,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)
    | v1_xboole_0(sK0)
    | ~ spl14_4 ),
    inference(resolution,[],[f928,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f928,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0)
    | ~ spl14_4 ),
    inference(resolution,[],[f911,f67])).

fof(f911,plain,
    ( r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1))
    | ~ spl14_4 ),
    inference(resolution,[],[f141,f67])).

fof(f1021,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)
        | sK4 != k4_tarski(k1_mcart_1(sK4),X3)
        | sK3 = X3
        | ~ m1_subset_1(X3,sK2) )
    | ~ spl14_4 ),
    inference(forward_demodulation,[],[f1020,f1007])).

fof(f1007,plain,
    ( k1_mcart_1(k1_mcart_1(sK4)) = sK12(k1_mcart_1(sK4))
    | ~ spl14_4 ),
    inference(superposition,[],[f58,f926])).

fof(f926,plain,
    ( k1_mcart_1(sK4) = k4_tarski(sK12(k1_mcart_1(sK4)),sK13(k1_mcart_1(sK4)))
    | ~ spl14_4 ),
    inference(resolution,[],[f911,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | k4_tarski(sK12(X0),sK13(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k4_tarski(sK12(X0),sK13(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13])],[f25,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
     => k4_tarski(sK12(X0),sK13(X0)) = X0 ) ),
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

fof(f1020,plain,
    ( ! [X3] :
        ( sK4 != k4_tarski(k1_mcart_1(sK4),X3)
        | sK3 = X3
        | ~ m1_subset_1(X3,sK2)
        | ~ m1_subset_1(sK12(k1_mcart_1(sK4)),sK0) )
    | ~ spl14_4 ),
    inference(subsumption_resolution,[],[f1019,f956])).

fof(f956,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | ~ spl14_4 ),
    inference(subsumption_resolution,[],[f952,f953])).

fof(f953,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl14_4 ),
    inference(resolution,[],[f929,f53])).

fof(f929,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | ~ spl14_4 ),
    inference(resolution,[],[f911,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f952,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | v1_xboole_0(sK1)
    | ~ spl14_4 ),
    inference(resolution,[],[f929,f61])).

fof(f1019,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)
        | sK4 != k4_tarski(k1_mcart_1(sK4),X3)
        | sK3 = X3
        | ~ m1_subset_1(X3,sK2)
        | ~ m1_subset_1(sK12(k1_mcart_1(sK4)),sK0) )
    | ~ spl14_4 ),
    inference(forward_demodulation,[],[f1010,f1008])).

fof(f1008,plain,
    ( k2_mcart_1(k1_mcart_1(sK4)) = sK13(k1_mcart_1(sK4))
    | ~ spl14_4 ),
    inference(superposition,[],[f59,f926])).

fof(f1010,plain,
    ( ! [X3] :
        ( sK4 != k4_tarski(k1_mcart_1(sK4),X3)
        | sK3 = X3
        | ~ m1_subset_1(X3,sK2)
        | ~ m1_subset_1(sK13(k1_mcart_1(sK4)),sK1)
        | ~ m1_subset_1(sK12(k1_mcart_1(sK4)),sK0) )
    | ~ spl14_4 ),
    inference(superposition,[],[f88,f926])).

fof(f88,plain,(
    ! [X6,X7,X5] :
      ( sK4 != k4_tarski(k4_tarski(X5,X6),X7)
      | sK3 = X7
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(definition_unfolding,[],[f46,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f46,plain,(
    ! [X6,X7,X5] :
      ( sK3 = X7
      | k3_mcart_1(X5,X6,X7) != sK4
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f412,plain,
    ( spl14_3
    | spl14_4 ),
    inference(avatar_split_clause,[],[f362,f139,f135])).

fof(f362,plain,
    ( r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f89,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f192,plain,
    ( ~ spl14_4
    | ~ spl14_9 ),
    inference(avatar_contradiction_clause,[],[f191])).

fof(f191,plain,
    ( $false
    | ~ spl14_4
    | ~ spl14_9 ),
    inference(subsumption_resolution,[],[f185,f181])).

fof(f181,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl14_4 ),
    inference(resolution,[],[f176,f53])).

fof(f176,plain,
    ( r2_hidden(k2_mcart_1(sK4),sK2)
    | ~ spl14_4 ),
    inference(resolution,[],[f141,f68])).

fof(f185,plain,
    ( v1_xboole_0(sK2)
    | ~ spl14_9 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl14_9
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_9])])).

fof(f190,plain,
    ( spl14_9
    | spl14_10
    | ~ spl14_4 ),
    inference(avatar_split_clause,[],[f180,f139,f187,f183])).

fof(f180,plain,
    ( m1_subset_1(k2_mcart_1(sK4),sK2)
    | v1_xboole_0(sK2)
    | ~ spl14_4 ),
    inference(resolution,[],[f176,f61])).

fof(f147,plain,
    ( ~ spl14_3
    | spl14_5 ),
    inference(avatar_split_clause,[],[f114,f144,f135])).

fof(f114,plain,
    ( v1_xboole_0(sK4)
    | ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f89,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:06:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.53  % (9541)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (9539)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (9549)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (9556)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (9561)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (9547)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (9548)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (9541)Refutation not found, incomplete strategy% (9541)------------------------------
% 0.21/0.55  % (9541)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (9556)Refutation not found, incomplete strategy% (9556)------------------------------
% 0.21/0.55  % (9556)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (9556)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (9556)Memory used [KB]: 10618
% 0.21/0.55  % (9556)Time elapsed: 0.133 s
% 0.21/0.55  % (9556)------------------------------
% 0.21/0.55  % (9556)------------------------------
% 0.21/0.55  % (9549)Refutation not found, incomplete strategy% (9549)------------------------------
% 0.21/0.55  % (9549)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (9549)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (9549)Memory used [KB]: 10618
% 0.21/0.55  % (9549)Time elapsed: 0.134 s
% 0.21/0.55  % (9549)------------------------------
% 0.21/0.55  % (9549)------------------------------
% 0.21/0.55  % (9542)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.55  % (9541)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (9541)Memory used [KB]: 11001
% 0.21/0.55  % (9541)Time elapsed: 0.126 s
% 0.21/0.55  % (9541)------------------------------
% 0.21/0.55  % (9541)------------------------------
% 0.21/0.56  % (9540)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.56  % (9544)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.56  % (9554)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.56  % (9557)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.56  % (9545)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.57  % (9550)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.57  % (9543)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.57  % (9567)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.57  % (9559)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.57  % (9552)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.57  % (9568)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.57  % (9560)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.57  % (9562)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.58  % (9558)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.58  % (9559)Refutation not found, incomplete strategy% (9559)------------------------------
% 0.21/0.58  % (9559)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (9551)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.58  % (9546)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.58  % (9566)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.59  % (9555)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.59  % (9564)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.59  % (9553)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.59  % (9565)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.59  % (9563)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.60  % (9559)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.60  
% 0.21/0.60  % (9559)Memory used [KB]: 10746
% 0.21/0.60  % (9559)Time elapsed: 0.166 s
% 0.21/0.60  % (9559)------------------------------
% 0.21/0.60  % (9559)------------------------------
% 2.08/0.65  % (9598)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.08/0.65  % (9599)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.08/0.65  % (9601)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.08/0.67  % (9547)Refutation found. Thanks to Tanya!
% 2.08/0.67  % SZS status Theorem for theBenchmark
% 2.08/0.69  % SZS output start Proof for theBenchmark
% 2.08/0.69  fof(f3024,plain,(
% 2.08/0.69    $false),
% 2.08/0.69    inference(avatar_sat_refutation,[],[f147,f190,f192,f412,f1140,f1159,f1163,f3001])).
% 2.08/0.69  fof(f3001,plain,(
% 2.08/0.69    ~spl14_3 | ~spl14_5),
% 2.08/0.69    inference(avatar_contradiction_clause,[],[f3000])).
% 2.08/0.69  fof(f3000,plain,(
% 2.08/0.69    $false | (~spl14_3 | ~spl14_5)),
% 2.08/0.69    inference(subsumption_resolution,[],[f2864,f2689])).
% 2.08/0.69  fof(f2689,plain,(
% 2.08/0.69    ( ! [X3] : (k1_xboole_0 = X3) ) | ~spl14_3),
% 2.08/0.69    inference(subsumption_resolution,[],[f2688,f47])).
% 2.08/0.69  fof(f47,plain,(
% 2.08/0.69    k1_xboole_0 != sK0),
% 2.08/0.69    inference(cnf_transformation,[],[f27])).
% 2.08/0.69  fof(f27,plain,(
% 2.08/0.69    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 2.08/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f18,f26])).
% 2.08/0.69  fof(f26,plain,(
% 2.08/0.69    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)))),
% 2.08/0.69    introduced(choice_axiom,[])).
% 2.08/0.69  fof(f18,plain,(
% 2.08/0.69    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 2.08/0.69    inference(flattening,[],[f17])).
% 2.08/0.69  fof(f17,plain,(
% 2.08/0.69    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 2.08/0.69    inference(ennf_transformation,[],[f16])).
% 2.08/0.69  fof(f16,negated_conjecture,(
% 2.08/0.69    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.08/0.69    inference(negated_conjecture,[],[f15])).
% 2.08/0.69  fof(f15,conjecture,(
% 2.08/0.69    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.08/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).
% 2.08/0.69  fof(f2688,plain,(
% 2.08/0.69    ( ! [X3] : (k1_xboole_0 = X3 | k1_xboole_0 = sK0) ) | ~spl14_3),
% 2.08/0.69    inference(subsumption_resolution,[],[f2687,f48])).
% 2.08/0.69  fof(f48,plain,(
% 2.08/0.69    k1_xboole_0 != sK1),
% 2.08/0.69    inference(cnf_transformation,[],[f27])).
% 2.08/0.69  fof(f2687,plain,(
% 2.08/0.69    ( ! [X3] : (k1_xboole_0 = X3 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) ) | ~spl14_3),
% 2.08/0.69    inference(subsumption_resolution,[],[f2686,f49])).
% 2.08/0.69  fof(f49,plain,(
% 2.08/0.69    k1_xboole_0 != sK2),
% 2.08/0.69    inference(cnf_transformation,[],[f27])).
% 2.08/0.69  fof(f2686,plain,(
% 2.08/0.69    ( ! [X3] : (k1_xboole_0 = X3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) ) | ~spl14_3),
% 2.08/0.69    inference(subsumption_resolution,[],[f2662,f2029])).
% 2.08/0.69  fof(f2029,plain,(
% 2.08/0.69    ( ! [X3] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X3)) )),
% 2.08/0.69    inference(forward_demodulation,[],[f2021,f2014])).
% 2.08/0.69  fof(f2014,plain,(
% 2.08/0.69    k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),
% 2.08/0.69    inference(superposition,[],[f105,f105])).
% 2.08/0.69  fof(f105,plain,(
% 2.08/0.69    ( ! [X2,X0,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0)) )),
% 2.08/0.69    inference(equality_resolution,[],[f93])).
% 2.08/0.69  fof(f93,plain,(
% 2.08/0.69    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 2.08/0.69    inference(definition_unfolding,[],[f86,f87])).
% 2.08/0.69  fof(f87,plain,(
% 2.08/0.69    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 2.08/0.69    inference(definition_unfolding,[],[f81,f66])).
% 2.08/0.69  fof(f66,plain,(
% 2.08/0.69    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 2.08/0.69    inference(cnf_transformation,[],[f6])).
% 2.08/0.69  fof(f6,axiom,(
% 2.08/0.69    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 2.08/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 2.08/0.69  fof(f81,plain,(
% 2.08/0.69    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 2.08/0.69    inference(cnf_transformation,[],[f7])).
% 2.08/0.69  fof(f7,axiom,(
% 2.08/0.69    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 2.08/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 2.08/0.69  fof(f86,plain,(
% 2.08/0.69    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X3 | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0) )),
% 2.08/0.69    inference(cnf_transformation,[],[f44])).
% 2.08/0.69  fof(f44,plain,(
% 2.08/0.69    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0) & (k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.08/0.69    inference(flattening,[],[f43])).
% 2.08/0.69  fof(f43,plain,(
% 2.08/0.69    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0) & (k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 | (k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.08/0.69    inference(nnf_transformation,[],[f13])).
% 2.08/0.69  fof(f13,axiom,(
% 2.08/0.69    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0)),
% 2.08/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).
% 2.08/0.69  fof(f2021,plain,(
% 2.08/0.69    ( ! [X3] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),X3)) )),
% 2.08/0.69    inference(superposition,[],[f106,f105])).
% 2.08/0.69  fof(f106,plain,(
% 2.08/0.69    ( ! [X0,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3)) )),
% 2.08/0.69    inference(equality_resolution,[],[f94])).
% 2.08/0.69  fof(f94,plain,(
% 2.08/0.69    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X2 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 2.08/0.69    inference(definition_unfolding,[],[f85,f87])).
% 2.08/0.69  fof(f85,plain,(
% 2.08/0.69    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X2 | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0) )),
% 2.08/0.69    inference(cnf_transformation,[],[f44])).
% 2.08/0.69  fof(f2662,plain,(
% 2.08/0.69    ( ! [X3] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X3) | k1_xboole_0 = X3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) ) | ~spl14_3),
% 2.08/0.69    inference(superposition,[],[f97,f2343])).
% 2.08/0.69  fof(f2343,plain,(
% 2.08/0.69    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl14_3),
% 2.08/0.69    inference(resolution,[],[f2002,f137])).
% 2.08/0.69  fof(f137,plain,(
% 2.08/0.69    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl14_3),
% 2.08/0.69    inference(avatar_component_clause,[],[f135])).
% 2.08/0.69  fof(f135,plain,(
% 2.08/0.69    spl14_3 <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 2.08/0.69    introduced(avatar_definition,[new_symbols(naming,[spl14_3])])).
% 2.08/0.69  fof(f2002,plain,(
% 2.08/0.69    ( ! [X1] : (~v1_xboole_0(X1) | k1_xboole_0 = X1) )),
% 2.08/0.69    inference(resolution,[],[f55,f53])).
% 2.08/0.69  fof(f53,plain,(
% 2.08/0.69    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.08/0.69    inference(cnf_transformation,[],[f31])).
% 2.08/0.69  fof(f31,plain,(
% 2.08/0.69    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK5(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.08/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f30])).
% 2.08/0.69  fof(f30,plain,(
% 2.08/0.69    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK5(X0),X0))),
% 2.08/0.69    introduced(choice_axiom,[])).
% 2.08/0.69  fof(f29,plain,(
% 2.08/0.69    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.08/0.69    inference(rectify,[],[f28])).
% 2.08/0.69  fof(f28,plain,(
% 2.08/0.69    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.08/0.69    inference(nnf_transformation,[],[f1])).
% 2.08/0.69  fof(f1,axiom,(
% 2.08/0.69    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.08/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.08/0.69  fof(f55,plain,(
% 2.08/0.69    ( ! [X0] : (r2_hidden(sK6(X0),X0) | k1_xboole_0 = X0) )),
% 2.08/0.69    inference(cnf_transformation,[],[f33])).
% 2.08/0.69  fof(f33,plain,(
% 2.08/0.69    ! [X0] : ((! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != sK6(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK6(X0),X0)) | k1_xboole_0 = X0)),
% 2.08/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f20,f32])).
% 2.08/0.69  fof(f32,plain,(
% 2.08/0.69    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X5,X4,X3,X2] : (k4_mcart_1(X2,X3,X4,X5) != sK6(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK6(X0),X0)))),
% 2.08/0.69    introduced(choice_axiom,[])).
% 2.08/0.69  fof(f20,plain,(
% 2.08/0.69    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 2.08/0.69    inference(ennf_transformation,[],[f11])).
% 2.08/0.69  fof(f11,axiom,(
% 2.08/0.69    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.08/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).
% 2.08/0.69  fof(f97,plain,(
% 2.08/0.69    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.08/0.69    inference(definition_unfolding,[],[f82,f87])).
% 2.08/0.69  fof(f82,plain,(
% 2.08/0.69    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.08/0.69    inference(cnf_transformation,[],[f44])).
% 2.08/0.69  fof(f2864,plain,(
% 2.08/0.69    k1_xboole_0 != sK3 | (~spl14_3 | ~spl14_5)),
% 2.08/0.69    inference(backward_demodulation,[],[f2344,f2689])).
% 2.08/0.69  fof(f2344,plain,(
% 2.08/0.69    sK3 != k7_mcart_1(sK0,sK1,sK2,k1_xboole_0) | ~spl14_5),
% 2.08/0.69    inference(backward_demodulation,[],[f50,f2341])).
% 2.08/0.69  fof(f2341,plain,(
% 2.08/0.69    k1_xboole_0 = sK4 | ~spl14_5),
% 2.08/0.69    inference(resolution,[],[f2002,f146])).
% 2.08/0.69  fof(f146,plain,(
% 2.08/0.69    v1_xboole_0(sK4) | ~spl14_5),
% 2.08/0.69    inference(avatar_component_clause,[],[f144])).
% 2.08/0.69  fof(f144,plain,(
% 2.08/0.69    spl14_5 <=> v1_xboole_0(sK4)),
% 2.08/0.69    introduced(avatar_definition,[new_symbols(naming,[spl14_5])])).
% 2.08/0.69  fof(f50,plain,(
% 2.08/0.69    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)),
% 2.08/0.69    inference(cnf_transformation,[],[f27])).
% 2.08/0.69  fof(f1163,plain,(
% 2.08/0.69    spl14_2 | ~spl14_4),
% 2.08/0.69    inference(avatar_contradiction_clause,[],[f1162])).
% 2.08/0.69  fof(f1162,plain,(
% 2.08/0.69    $false | (spl14_2 | ~spl14_4)),
% 2.08/0.69    inference(subsumption_resolution,[],[f131,f965])).
% 2.08/0.69  fof(f965,plain,(
% 2.08/0.69    sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) | ~spl14_4),
% 2.08/0.69    inference(backward_demodulation,[],[f964,f958])).
% 2.08/0.69  fof(f958,plain,(
% 2.08/0.69    k2_mcart_1(sK4) = sK11(k2_zfmisc_1(sK0,sK1),sK2,sK4) | ~spl14_4),
% 2.08/0.69    inference(superposition,[],[f59,f910])).
% 2.08/0.69  fof(f910,plain,(
% 2.08/0.69    sK4 = k4_tarski(sK10(k2_zfmisc_1(sK0,sK1),sK2,sK4),sK11(k2_zfmisc_1(sK0,sK1),sK2,sK4)) | ~spl14_4),
% 2.08/0.69    inference(resolution,[],[f141,f102])).
% 2.08/0.69  fof(f102,plain,(
% 2.08/0.69    ( ! [X0,X8,X1] : (~r2_hidden(X8,k2_zfmisc_1(X0,X1)) | k4_tarski(sK10(X0,X1,X8),sK11(X0,X1,X8)) = X8) )),
% 2.08/0.69    inference(equality_resolution,[],[f71])).
% 2.08/0.69  fof(f71,plain,(
% 2.08/0.69    ( ! [X2,X0,X8,X1] : (k4_tarski(sK10(X0,X1,X8),sK11(X0,X1,X8)) = X8 | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 2.08/0.69    inference(cnf_transformation,[],[f40])).
% 2.08/0.69  fof(f40,plain,(
% 2.08/0.69    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK7(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK7(X0,X1,X2),X2)) & ((sK7(X0,X1,X2) = k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)) & r2_hidden(sK9(X0,X1,X2),X1) & r2_hidden(sK8(X0,X1,X2),X0)) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK10(X0,X1,X8),sK11(X0,X1,X8)) = X8 & r2_hidden(sK11(X0,X1,X8),X1) & r2_hidden(sK10(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 2.08/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10,sK11])],[f36,f39,f38,f37])).
% 2.08/0.69  fof(f37,plain,(
% 2.08/0.69    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK7(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK7(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 2.08/0.69    introduced(choice_axiom,[])).
% 2.08/0.69  fof(f38,plain,(
% 2.08/0.69    ! [X2,X1,X0] : (? [X7,X6] : (k4_tarski(X6,X7) = sK7(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (sK7(X0,X1,X2) = k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)) & r2_hidden(sK9(X0,X1,X2),X1) & r2_hidden(sK8(X0,X1,X2),X0)))),
% 2.08/0.69    introduced(choice_axiom,[])).
% 2.08/0.69  fof(f39,plain,(
% 2.08/0.69    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK10(X0,X1,X8),sK11(X0,X1,X8)) = X8 & r2_hidden(sK11(X0,X1,X8),X1) & r2_hidden(sK10(X0,X1,X8),X0)))),
% 2.08/0.69    introduced(choice_axiom,[])).
% 2.08/0.69  fof(f36,plain,(
% 2.08/0.69    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 2.08/0.69    inference(rectify,[],[f35])).
% 2.08/0.69  fof(f35,plain,(
% 2.08/0.69    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 2.08/0.69    inference(nnf_transformation,[],[f2])).
% 2.08/0.69  fof(f2,axiom,(
% 2.08/0.69    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 2.08/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 2.08/0.69  fof(f141,plain,(
% 2.08/0.69    r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl14_4),
% 2.08/0.69    inference(avatar_component_clause,[],[f139])).
% 2.08/0.69  fof(f139,plain,(
% 2.08/0.69    spl14_4 <=> r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 2.08/0.69    introduced(avatar_definition,[new_symbols(naming,[spl14_4])])).
% 2.08/0.69  fof(f59,plain,(
% 2.08/0.69    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 2.08/0.69    inference(cnf_transformation,[],[f14])).
% 2.08/0.69  fof(f14,axiom,(
% 2.08/0.69    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 2.08/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 2.08/0.69  fof(f964,plain,(
% 2.08/0.69    sK4 = k4_tarski(k1_mcart_1(sK4),sK11(k2_zfmisc_1(sK0,sK1),sK2,sK4)) | ~spl14_4),
% 2.08/0.69    inference(backward_demodulation,[],[f910,f957])).
% 2.08/0.69  fof(f957,plain,(
% 2.08/0.69    k1_mcart_1(sK4) = sK10(k2_zfmisc_1(sK0,sK1),sK2,sK4) | ~spl14_4),
% 2.08/0.69    inference(superposition,[],[f58,f910])).
% 2.08/0.69  fof(f58,plain,(
% 2.08/0.69    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 2.08/0.69    inference(cnf_transformation,[],[f14])).
% 2.08/0.69  fof(f131,plain,(
% 2.08/0.69    sK4 != k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) | spl14_2),
% 2.08/0.69    inference(avatar_component_clause,[],[f130])).
% 2.08/0.69  fof(f130,plain,(
% 2.08/0.69    spl14_2 <=> sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))),
% 2.08/0.69    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).
% 2.08/0.69  fof(f1159,plain,(
% 2.08/0.69    spl14_3 | ~spl14_24),
% 2.08/0.69    inference(avatar_contradiction_clause,[],[f1158])).
% 2.08/0.69  fof(f1158,plain,(
% 2.08/0.69    $false | (spl14_3 | ~spl14_24)),
% 2.08/0.69    inference(subsumption_resolution,[],[f348,f1122])).
% 2.08/0.69  fof(f1122,plain,(
% 2.08/0.69    ~v1_xboole_0(sK0) | spl14_3),
% 2.08/0.69    inference(resolution,[],[f1027,f53])).
% 2.08/0.69  fof(f1027,plain,(
% 2.08/0.69    r2_hidden(k1_mcart_1(k1_mcart_1(sK5(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)))),sK0) | spl14_3),
% 2.08/0.69    inference(resolution,[],[f944,f67])).
% 2.08/0.69  fof(f67,plain,(
% 2.08/0.69    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 2.08/0.69    inference(cnf_transformation,[],[f23])).
% 2.08/0.69  fof(f23,plain,(
% 2.08/0.69    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 2.08/0.69    inference(ennf_transformation,[],[f8])).
% 2.08/0.69  fof(f8,axiom,(
% 2.08/0.69    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 2.08/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 2.08/0.69  fof(f944,plain,(
% 2.08/0.69    r2_hidden(k1_mcart_1(sK5(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),k2_zfmisc_1(sK0,sK1)) | spl14_3),
% 2.08/0.69    inference(resolution,[],[f904,f67])).
% 2.08/0.69  fof(f904,plain,(
% 2.08/0.69    r2_hidden(sK5(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | spl14_3),
% 2.08/0.69    inference(resolution,[],[f136,f54])).
% 2.08/0.69  fof(f54,plain,(
% 2.08/0.69    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK5(X0),X0)) )),
% 2.08/0.69    inference(cnf_transformation,[],[f31])).
% 2.08/0.69  fof(f136,plain,(
% 2.08/0.69    ~v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | spl14_3),
% 2.08/0.69    inference(avatar_component_clause,[],[f135])).
% 2.08/0.69  fof(f348,plain,(
% 2.08/0.69    v1_xboole_0(sK0) | ~spl14_24),
% 2.08/0.69    inference(avatar_component_clause,[],[f346])).
% 2.08/0.69  fof(f346,plain,(
% 2.08/0.69    spl14_24 <=> v1_xboole_0(sK0)),
% 2.08/0.69    introduced(avatar_definition,[new_symbols(naming,[spl14_24])])).
% 2.08/0.69  fof(f1140,plain,(
% 2.08/0.69    ~spl14_2 | ~spl14_4 | ~spl14_10 | spl14_24),
% 2.08/0.69    inference(avatar_contradiction_clause,[],[f1139])).
% 2.08/0.69  fof(f1139,plain,(
% 2.08/0.69    $false | (~spl14_2 | ~spl14_4 | ~spl14_10 | spl14_24)),
% 2.08/0.69    inference(subsumption_resolution,[],[f1138,f189])).
% 2.08/0.69  fof(f189,plain,(
% 2.08/0.69    m1_subset_1(k2_mcart_1(sK4),sK2) | ~spl14_10),
% 2.08/0.69    inference(avatar_component_clause,[],[f187])).
% 2.08/0.69  fof(f187,plain,(
% 2.08/0.69    spl14_10 <=> m1_subset_1(k2_mcart_1(sK4),sK2)),
% 2.08/0.69    introduced(avatar_definition,[new_symbols(naming,[spl14_10])])).
% 2.08/0.69  fof(f1138,plain,(
% 2.08/0.69    ~m1_subset_1(k2_mcart_1(sK4),sK2) | (~spl14_2 | ~spl14_4 | spl14_24)),
% 2.08/0.69    inference(subsumption_resolution,[],[f1137,f179])).
% 2.08/0.69  fof(f179,plain,(
% 2.08/0.69    sK3 != k2_mcart_1(sK4)),
% 2.08/0.69    inference(superposition,[],[f50,f123])).
% 2.08/0.69  fof(f123,plain,(
% 2.08/0.69    k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)),
% 2.08/0.69    inference(subsumption_resolution,[],[f122,f47])).
% 2.08/0.69  fof(f122,plain,(
% 2.08/0.69    k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) | k1_xboole_0 = sK0),
% 2.08/0.69    inference(subsumption_resolution,[],[f121,f48])).
% 2.08/0.69  fof(f121,plain,(
% 2.08/0.69    k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 2.08/0.69    inference(subsumption_resolution,[],[f111,f49])).
% 2.08/0.69  fof(f111,plain,(
% 2.08/0.69    k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 2.08/0.69    inference(resolution,[],[f89,f90])).
% 2.08/0.69  fof(f90,plain,(
% 2.08/0.69    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.08/0.69    inference(definition_unfolding,[],[f79,f66])).
% 2.08/0.69  fof(f79,plain,(
% 2.08/0.69    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.08/0.69    inference(cnf_transformation,[],[f24])).
% 2.08/0.69  fof(f24,plain,(
% 2.08/0.69    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.08/0.69    inference(ennf_transformation,[],[f12])).
% 2.08/0.69  fof(f12,axiom,(
% 2.08/0.69    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.08/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).
% 2.08/0.69  fof(f89,plain,(
% 2.08/0.69    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 2.08/0.69    inference(definition_unfolding,[],[f45,f66])).
% 2.08/0.69  fof(f45,plain,(
% 2.08/0.69    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 2.08/0.69    inference(cnf_transformation,[],[f27])).
% 2.08/0.69  fof(f1137,plain,(
% 2.08/0.69    sK3 = k2_mcart_1(sK4) | ~m1_subset_1(k2_mcart_1(sK4),sK2) | (~spl14_2 | ~spl14_4 | spl14_24)),
% 2.08/0.69    inference(trivial_inequality_removal,[],[f1136])).
% 2.08/0.69  fof(f1136,plain,(
% 2.08/0.69    sK4 != sK4 | sK3 = k2_mcart_1(sK4) | ~m1_subset_1(k2_mcart_1(sK4),sK2) | (~spl14_2 | ~spl14_4 | spl14_24)),
% 2.08/0.69    inference(superposition,[],[f1022,f132])).
% 2.08/0.69  fof(f132,plain,(
% 2.08/0.69    sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) | ~spl14_2),
% 2.08/0.69    inference(avatar_component_clause,[],[f130])).
% 2.08/0.69  fof(f1022,plain,(
% 2.08/0.69    ( ! [X3] : (sK4 != k4_tarski(k1_mcart_1(sK4),X3) | sK3 = X3 | ~m1_subset_1(X3,sK2)) ) | (~spl14_4 | spl14_24)),
% 2.08/0.69    inference(subsumption_resolution,[],[f1021,f951])).
% 2.08/0.69  fof(f951,plain,(
% 2.08/0.69    m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) | (~spl14_4 | spl14_24)),
% 2.08/0.69    inference(subsumption_resolution,[],[f949,f347])).
% 2.08/0.69  fof(f347,plain,(
% 2.08/0.69    ~v1_xboole_0(sK0) | spl14_24),
% 2.08/0.69    inference(avatar_component_clause,[],[f346])).
% 2.08/0.69  fof(f949,plain,(
% 2.08/0.69    m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) | v1_xboole_0(sK0) | ~spl14_4),
% 2.08/0.69    inference(resolution,[],[f928,f61])).
% 2.08/0.69  fof(f61,plain,(
% 2.08/0.69    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.08/0.69    inference(cnf_transformation,[],[f34])).
% 2.08/0.69  fof(f34,plain,(
% 2.08/0.69    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.08/0.69    inference(nnf_transformation,[],[f21])).
% 2.08/0.69  fof(f21,plain,(
% 2.08/0.69    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.08/0.69    inference(ennf_transformation,[],[f4])).
% 2.08/0.69  fof(f4,axiom,(
% 2.08/0.69    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.08/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 2.08/0.69  fof(f928,plain,(
% 2.08/0.69    r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0) | ~spl14_4),
% 2.08/0.69    inference(resolution,[],[f911,f67])).
% 2.08/0.69  fof(f911,plain,(
% 2.08/0.69    r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1)) | ~spl14_4),
% 2.08/0.69    inference(resolution,[],[f141,f67])).
% 2.08/0.69  fof(f1021,plain,(
% 2.08/0.69    ( ! [X3] : (~m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) | sK4 != k4_tarski(k1_mcart_1(sK4),X3) | sK3 = X3 | ~m1_subset_1(X3,sK2)) ) | ~spl14_4),
% 2.08/0.69    inference(forward_demodulation,[],[f1020,f1007])).
% 2.08/0.69  fof(f1007,plain,(
% 2.08/0.69    k1_mcart_1(k1_mcart_1(sK4)) = sK12(k1_mcart_1(sK4)) | ~spl14_4),
% 2.08/0.69    inference(superposition,[],[f58,f926])).
% 2.08/0.69  fof(f926,plain,(
% 2.08/0.69    k1_mcart_1(sK4) = k4_tarski(sK12(k1_mcart_1(sK4)),sK13(k1_mcart_1(sK4))) | ~spl14_4),
% 2.08/0.69    inference(resolution,[],[f911,f80])).
% 2.08/0.69  fof(f80,plain,(
% 2.08/0.69    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | k4_tarski(sK12(X0),sK13(X0)) = X0) )),
% 2.08/0.69    inference(cnf_transformation,[],[f42])).
% 2.08/0.69  fof(f42,plain,(
% 2.08/0.69    ! [X0,X1,X2] : (k4_tarski(sK12(X0),sK13(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 2.08/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13])],[f25,f41])).
% 2.08/0.69  fof(f41,plain,(
% 2.08/0.69    ! [X0] : (? [X3,X4] : k4_tarski(X3,X4) = X0 => k4_tarski(sK12(X0),sK13(X0)) = X0)),
% 2.08/0.69    introduced(choice_axiom,[])).
% 2.08/0.69  fof(f25,plain,(
% 2.08/0.69    ! [X0,X1,X2] : (? [X3,X4] : k4_tarski(X3,X4) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 2.08/0.69    inference(ennf_transformation,[],[f3])).
% 2.08/0.69  fof(f3,axiom,(
% 2.08/0.69    ! [X0,X1,X2] : ~(! [X3,X4] : k4_tarski(X3,X4) != X0 & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 2.08/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).
% 2.08/0.69  fof(f1020,plain,(
% 2.08/0.69    ( ! [X3] : (sK4 != k4_tarski(k1_mcart_1(sK4),X3) | sK3 = X3 | ~m1_subset_1(X3,sK2) | ~m1_subset_1(sK12(k1_mcart_1(sK4)),sK0)) ) | ~spl14_4),
% 2.08/0.69    inference(subsumption_resolution,[],[f1019,f956])).
% 2.08/0.69  fof(f956,plain,(
% 2.08/0.69    m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) | ~spl14_4),
% 2.08/0.69    inference(subsumption_resolution,[],[f952,f953])).
% 2.08/0.69  fof(f953,plain,(
% 2.08/0.69    ~v1_xboole_0(sK1) | ~spl14_4),
% 2.08/0.69    inference(resolution,[],[f929,f53])).
% 2.08/0.69  fof(f929,plain,(
% 2.08/0.69    r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1) | ~spl14_4),
% 2.08/0.69    inference(resolution,[],[f911,f68])).
% 2.08/0.69  fof(f68,plain,(
% 2.08/0.69    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 2.08/0.69    inference(cnf_transformation,[],[f23])).
% 2.08/0.69  fof(f952,plain,(
% 2.08/0.69    m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) | v1_xboole_0(sK1) | ~spl14_4),
% 2.08/0.69    inference(resolution,[],[f929,f61])).
% 2.08/0.69  fof(f1019,plain,(
% 2.08/0.69    ( ! [X3] : (~m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) | sK4 != k4_tarski(k1_mcart_1(sK4),X3) | sK3 = X3 | ~m1_subset_1(X3,sK2) | ~m1_subset_1(sK12(k1_mcart_1(sK4)),sK0)) ) | ~spl14_4),
% 2.08/0.69    inference(forward_demodulation,[],[f1010,f1008])).
% 2.08/0.69  fof(f1008,plain,(
% 2.08/0.69    k2_mcart_1(k1_mcart_1(sK4)) = sK13(k1_mcart_1(sK4)) | ~spl14_4),
% 2.08/0.69    inference(superposition,[],[f59,f926])).
% 2.08/0.69  fof(f1010,plain,(
% 2.08/0.69    ( ! [X3] : (sK4 != k4_tarski(k1_mcart_1(sK4),X3) | sK3 = X3 | ~m1_subset_1(X3,sK2) | ~m1_subset_1(sK13(k1_mcart_1(sK4)),sK1) | ~m1_subset_1(sK12(k1_mcart_1(sK4)),sK0)) ) | ~spl14_4),
% 2.08/0.69    inference(superposition,[],[f88,f926])).
% 2.08/0.69  fof(f88,plain,(
% 2.08/0.69    ( ! [X6,X7,X5] : (sK4 != k4_tarski(k4_tarski(X5,X6),X7) | sK3 = X7 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 2.08/0.69    inference(definition_unfolding,[],[f46,f65])).
% 2.08/0.69  fof(f65,plain,(
% 2.08/0.69    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 2.08/0.69    inference(cnf_transformation,[],[f5])).
% 2.08/0.69  fof(f5,axiom,(
% 2.08/0.69    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 2.08/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 2.08/0.69  fof(f46,plain,(
% 2.08/0.69    ( ! [X6,X7,X5] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 2.08/0.69    inference(cnf_transformation,[],[f27])).
% 2.08/0.69  fof(f412,plain,(
% 2.08/0.69    spl14_3 | spl14_4),
% 2.08/0.69    inference(avatar_split_clause,[],[f362,f139,f135])).
% 2.08/0.69  fof(f362,plain,(
% 2.08/0.69    r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 2.08/0.69    inference(resolution,[],[f89,f60])).
% 2.08/0.69  fof(f60,plain,(
% 2.08/0.69    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.08/0.69    inference(cnf_transformation,[],[f34])).
% 2.08/0.69  fof(f192,plain,(
% 2.08/0.69    ~spl14_4 | ~spl14_9),
% 2.08/0.69    inference(avatar_contradiction_clause,[],[f191])).
% 2.08/0.69  fof(f191,plain,(
% 2.08/0.69    $false | (~spl14_4 | ~spl14_9)),
% 2.08/0.69    inference(subsumption_resolution,[],[f185,f181])).
% 2.08/0.69  fof(f181,plain,(
% 2.08/0.69    ~v1_xboole_0(sK2) | ~spl14_4),
% 2.08/0.69    inference(resolution,[],[f176,f53])).
% 2.08/0.69  fof(f176,plain,(
% 2.08/0.69    r2_hidden(k2_mcart_1(sK4),sK2) | ~spl14_4),
% 2.08/0.69    inference(resolution,[],[f141,f68])).
% 2.08/0.69  fof(f185,plain,(
% 2.08/0.69    v1_xboole_0(sK2) | ~spl14_9),
% 2.08/0.69    inference(avatar_component_clause,[],[f183])).
% 2.08/0.69  fof(f183,plain,(
% 2.08/0.69    spl14_9 <=> v1_xboole_0(sK2)),
% 2.08/0.69    introduced(avatar_definition,[new_symbols(naming,[spl14_9])])).
% 2.08/0.69  fof(f190,plain,(
% 2.08/0.69    spl14_9 | spl14_10 | ~spl14_4),
% 2.08/0.69    inference(avatar_split_clause,[],[f180,f139,f187,f183])).
% 2.08/0.69  fof(f180,plain,(
% 2.08/0.69    m1_subset_1(k2_mcart_1(sK4),sK2) | v1_xboole_0(sK2) | ~spl14_4),
% 2.08/0.69    inference(resolution,[],[f176,f61])).
% 2.08/0.69  fof(f147,plain,(
% 2.08/0.69    ~spl14_3 | spl14_5),
% 2.08/0.69    inference(avatar_split_clause,[],[f114,f144,f135])).
% 2.08/0.69  fof(f114,plain,(
% 2.08/0.69    v1_xboole_0(sK4) | ~v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 2.08/0.69    inference(resolution,[],[f89,f62])).
% 2.08/0.69  fof(f62,plain,(
% 2.08/0.69    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 2.08/0.69    inference(cnf_transformation,[],[f34])).
% 2.08/0.69  % SZS output end Proof for theBenchmark
% 2.08/0.69  % (9547)------------------------------
% 2.08/0.69  % (9547)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.08/0.69  % (9547)Termination reason: Refutation
% 2.08/0.69  
% 2.08/0.69  % (9547)Memory used [KB]: 11897
% 2.08/0.69  % (9547)Time elapsed: 0.228 s
% 2.08/0.69  % (9547)------------------------------
% 2.08/0.69  % (9547)------------------------------
% 2.08/0.69  % (9538)Success in time 0.327 s
%------------------------------------------------------------------------------
