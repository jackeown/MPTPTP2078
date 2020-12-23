%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 234 expanded)
%              Number of leaves         :   23 ( 116 expanded)
%              Depth                    :   10
%              Number of atoms          :  422 (1290 expanded)
%              Number of equality atoms :  213 ( 665 expanded)
%              Maximal formula depth    :   24 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (2785)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% (2781)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% (2784)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f140,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f61,f65,f69,f73,f77,f90,f112,f115,f117,f119,f121,f139])).

fof(f139,plain,
    ( spl10_5
    | spl10_4
    | spl10_3
    | spl10_2
    | spl10_1
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f137,f110,f88,f75,f55,f59,f63,f67,f71])).

fof(f71,plain,
    ( spl10_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f67,plain,
    ( spl10_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f63,plain,
    ( spl10_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f59,plain,
    ( spl10_2
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f55,plain,
    ( spl10_1
  <=> sK4 = k8_mcart_1(sK0,sK1,sK2,sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f75,plain,
    ( spl10_6
  <=> m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f88,plain,
    ( spl10_7
  <=> sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5)),sK9(sK0,sK1,sK2,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

% (2776)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f110,plain,
    ( spl10_12
  <=> sK4 = sK6(sK0,sK1,sK2,sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f137,plain,
    ( sK4 = k8_mcart_1(sK0,sK1,sK2,sK3,sK5)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_12 ),
    inference(forward_demodulation,[],[f136,f111])).

fof(f111,plain,
    ( sK4 = sK6(sK0,sK1,sK2,sK3,sK5)
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f110])).

fof(f136,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = sK6(sK0,sK1,sK2,sK3,sK5)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(resolution,[],[f91,f76])).

fof(f76,plain,
    ( m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f75])).

fof(f91,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
        | sK6(sK0,sK1,sK2,sK3,sK5) = k8_mcart_1(X0,X1,X2,X3,sK5)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | ~ spl10_7 ),
    inference(superposition,[],[f53,f89])).

fof(f89,plain,
    ( sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5)),sK9(sK0,sK1,sK2,sK3,sK5))
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f88])).

fof(f53,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(k4_tarski(k3_mcart_1(X5,X6,X7),X8),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k8_mcart_1(X0,X1,X2,X3,k4_tarski(k3_mcart_1(X5,X6,X7),X8)) = X5
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
      | k4_tarski(k3_mcart_1(X5,X6,X7),X8) != X4
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f34,f27,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f28,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f34,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5,X6,X7,X8] :
              ( ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
                & k10_mcart_1(X0,X1,X2,X3,X4) = X7
                & k9_mcart_1(X0,X1,X2,X3,X4) = X6
                & k8_mcart_1(X0,X1,X2,X3,X4) = X5 )
              | k4_mcart_1(X5,X6,X7,X8) != X4 )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_mcart_1)).

fof(f121,plain,
    ( spl10_5
    | spl10_4
    | spl10_3
    | spl10_2
    | ~ spl10_6
    | spl10_11 ),
    inference(avatar_split_clause,[],[f120,f107,f75,f59,f63,f67,f71])).

fof(f107,plain,
    ( spl10_11
  <=> m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f120,plain,
    ( ~ m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl10_11 ),
    inference(resolution,[],[f108,f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK9(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f32,f38])).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK9(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X4
            & m1_subset_1(sK9(X0,X1,X2,X3,X4),X3)
            & m1_subset_1(sK8(X0,X1,X2,X3,X4),X2)
            & m1_subset_1(sK7(X0,X1,X2,X3,X4),X1)
            & m1_subset_1(sK6(X0,X1,X2,X3,X4),X0) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f10,f17,f16,f15,f14])).

fof(f14,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ? [X8] :
                      ( k4_mcart_1(X5,X6,X7,X8) = X4
                      & m1_subset_1(X8,X3) )
                  & m1_subset_1(X7,X2) )
              & m1_subset_1(X6,X1) )
          & m1_subset_1(X5,X0) )
     => ( ? [X6] :
            ( ? [X7] :
                ( ? [X8] :
                    ( k4_mcart_1(sK6(X0,X1,X2,X3,X4),X6,X7,X8) = X4
                    & m1_subset_1(X8,X3) )
                & m1_subset_1(X7,X2) )
            & m1_subset_1(X6,X1) )
        & m1_subset_1(sK6(X0,X1,X2,X3,X4),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( ? [X7] :
              ( ? [X8] :
                  ( k4_mcart_1(sK6(X0,X1,X2,X3,X4),X6,X7,X8) = X4
                  & m1_subset_1(X8,X3) )
              & m1_subset_1(X7,X2) )
          & m1_subset_1(X6,X1) )
     => ( ? [X7] :
            ( ? [X8] :
                ( k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),X7,X8) = X4
                & m1_subset_1(X8,X3) )
            & m1_subset_1(X7,X2) )
        & m1_subset_1(sK7(X0,X1,X2,X3,X4),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X7] :
          ( ? [X8] :
              ( k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),X7,X8) = X4
              & m1_subset_1(X8,X3) )
          & m1_subset_1(X7,X2) )
     => ( ? [X8] :
            ( k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),X8) = X4
            & m1_subset_1(X8,X3) )
        & m1_subset_1(sK8(X0,X1,X2,X3,X4),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X8] :
          ( k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),X8) = X4
          & m1_subset_1(X8,X3) )
     => ( k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X4
        & m1_subset_1(sK9(X0,X1,X2,X3,X4),X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ? [X7] :
                      ( ? [X8] :
                          ( k4_mcart_1(X5,X6,X7,X8) = X4
                          & m1_subset_1(X8,X3) )
                      & m1_subset_1(X7,X2) )
                  & m1_subset_1(X6,X1) )
              & m1_subset_1(X5,X0) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ? [X4] :
            ( ! [X5] :
                ( m1_subset_1(X5,X0)
               => ! [X6] :
                    ( m1_subset_1(X6,X1)
                   => ! [X7] :
                        ( m1_subset_1(X7,X2)
                       => ! [X8] :
                            ( m1_subset_1(X8,X3)
                           => k4_mcart_1(X5,X6,X7,X8) != X4 ) ) ) )
            & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_mcart_1)).

fof(f108,plain,
    ( ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)
    | spl10_11 ),
    inference(avatar_component_clause,[],[f107])).

fof(f119,plain,
    ( spl10_5
    | spl10_4
    | spl10_3
    | spl10_2
    | ~ spl10_6
    | spl10_10 ),
    inference(avatar_split_clause,[],[f118,f104,f75,f59,f63,f67,f71])).

fof(f104,plain,
    ( spl10_10
  <=> m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f118,plain,
    ( ~ m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl10_10 ),
    inference(resolution,[],[f105,f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK8(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f31,f38])).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK8(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f105,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)
    | spl10_10 ),
    inference(avatar_component_clause,[],[f104])).

fof(f117,plain,
    ( spl10_5
    | spl10_4
    | spl10_3
    | spl10_2
    | ~ spl10_6
    | spl10_9 ),
    inference(avatar_split_clause,[],[f116,f101,f75,f59,f63,f67,f71])).

fof(f101,plain,
    ( spl10_9
  <=> m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f116,plain,
    ( ~ m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl10_9 ),
    inference(resolution,[],[f102,f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK7(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f30,f38])).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK7(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f102,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1)
    | spl10_9 ),
    inference(avatar_component_clause,[],[f101])).

fof(f115,plain,
    ( spl10_5
    | spl10_4
    | spl10_3
    | spl10_2
    | ~ spl10_6
    | spl10_8 ),
    inference(avatar_split_clause,[],[f113,f98,f75,f59,f63,f67,f71])).

fof(f98,plain,
    ( spl10_8
  <=> m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f113,plain,
    ( ~ m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl10_8 ),
    inference(resolution,[],[f99,f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK6(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f29,f38])).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK6(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f99,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)
    | spl10_8 ),
    inference(avatar_component_clause,[],[f98])).

fof(f112,plain,
    ( ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | spl10_12
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f96,f88,f110,f107,f104,f101,f98])).

fof(f96,plain,
    ( sK4 = sK6(sK0,sK1,sK2,sK3,sK5)
    | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)
    | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)
    | ~ spl10_7 ),
    inference(trivial_inequality_removal,[],[f95])).

fof(f95,plain,
    ( sK5 != sK5
    | sK4 = sK6(sK0,sK1,sK2,sK3,sK5)
    | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)
    | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)
    | ~ spl10_7 ),
    inference(superposition,[],[f39,f89])).

fof(f39,plain,(
    ! [X6,X8,X7,X9] :
      ( sK5 != k4_tarski(k3_mcart_1(X6,X7,X8),X9)
      | sK4 = X6
      | ~ m1_subset_1(X9,sK3)
      | ~ m1_subset_1(X8,sK2)
      | ~ m1_subset_1(X7,sK1)
      | ~ m1_subset_1(X6,sK0) ) ),
    inference(definition_unfolding,[],[f20,f27])).

fof(f20,plain,(
    ! [X6,X8,X7,X9] :
      ( sK4 = X6
      | k4_mcart_1(X6,X7,X8,X9) != sK5
      | ~ m1_subset_1(X9,sK3)
      | ~ m1_subset_1(X8,sK2)
      | ~ m1_subset_1(X7,sK1)
      | ~ m1_subset_1(X6,sK0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( sK4 != k8_mcart_1(sK0,sK1,sK2,sK3,sK5)
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & ! [X6] :
        ( ! [X7] :
            ( ! [X8] :
                ( ! [X9] :
                    ( sK4 = X6
                    | k4_mcart_1(X6,X7,X8,X9) != sK5
                    | ~ m1_subset_1(X9,sK3) )
                | ~ m1_subset_1(X8,sK2) )
            | ~ m1_subset_1(X7,sK1) )
        | ~ m1_subset_1(X6,sK0) )
    & m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f9,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( k8_mcart_1(X0,X1,X2,X3,X5) != X4
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X6] :
            ( ! [X7] :
                ( ! [X8] :
                    ( ! [X9] :
                        ( X4 = X6
                        | k4_mcart_1(X6,X7,X8,X9) != X5
                        | ~ m1_subset_1(X9,X3) )
                    | ~ m1_subset_1(X8,X2) )
                | ~ m1_subset_1(X7,X1) )
            | ~ m1_subset_1(X6,X0) )
        & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) )
   => ( sK4 != k8_mcart_1(sK0,sK1,sK2,sK3,sK5)
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( sK4 = X6
                      | k4_mcart_1(X6,X7,X8,X9) != sK5
                      | ~ m1_subset_1(X9,sK3) )
                  | ~ m1_subset_1(X8,sK2) )
              | ~ m1_subset_1(X7,sK1) )
          | ~ m1_subset_1(X6,sK0) )
      & m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k8_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X6
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k8_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X6
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
       => ( ! [X6] :
              ( m1_subset_1(X6,X0)
             => ! [X7] :
                  ( m1_subset_1(X7,X1)
                 => ! [X8] :
                      ( m1_subset_1(X8,X2)
                     => ! [X9] :
                          ( m1_subset_1(X9,X3)
                         => ( k4_mcart_1(X6,X7,X8,X9) = X5
                           => X4 = X6 ) ) ) ) )
         => ( k8_mcart_1(X0,X1,X2,X3,X5) = X4
            | k1_xboole_0 = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
     => ( ! [X6] :
            ( m1_subset_1(X6,X0)
           => ! [X7] :
                ( m1_subset_1(X7,X1)
               => ! [X8] :
                    ( m1_subset_1(X8,X2)
                   => ! [X9] :
                        ( m1_subset_1(X9,X3)
                       => ( k4_mcart_1(X6,X7,X8,X9) = X5
                         => X4 = X6 ) ) ) ) )
       => ( k8_mcart_1(X0,X1,X2,X3,X5) = X4
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_mcart_1)).

fof(f90,plain,
    ( spl10_5
    | spl10_4
    | spl10_3
    | spl10_2
    | spl10_7
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f78,f75,f88,f59,f63,f67,f71])).

fof(f78,plain,
    ( sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5)),sK9(sK0,sK1,sK2,sK3,sK5))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl10_6 ),
    inference(resolution,[],[f41,f76])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k4_tarski(k3_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4)),sK9(X0,X1,X2,X3,X4)) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f33,f27,f38])).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X4
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f77,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f40,f75])).

fof(f40,plain,(
    m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) ),
    inference(definition_unfolding,[],[f19,f38])).

fof(f19,plain,(
    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f13])).

fof(f73,plain,(
    ~ spl10_5 ),
    inference(avatar_split_clause,[],[f21,f71])).

fof(f21,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f13])).

fof(f69,plain,(
    ~ spl10_4 ),
    inference(avatar_split_clause,[],[f22,f67])).

fof(f22,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f13])).

fof(f65,plain,(
    ~ spl10_3 ),
    inference(avatar_split_clause,[],[f23,f63])).

fof(f23,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f13])).

fof(f61,plain,(
    ~ spl10_2 ),
    inference(avatar_split_clause,[],[f24,f59])).

fof(f24,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f13])).

fof(f57,plain,(
    ~ spl10_1 ),
    inference(avatar_split_clause,[],[f25,f55])).

fof(f25,plain,(
    sK4 != k8_mcart_1(sK0,sK1,sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:56:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.49  % (2778)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (2793)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.50  % (2793)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.51  % (2785)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (2781)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (2784)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  fof(f140,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f57,f61,f65,f69,f73,f77,f90,f112,f115,f117,f119,f121,f139])).
% 0.21/0.52  fof(f139,plain,(
% 0.21/0.52    spl10_5 | spl10_4 | spl10_3 | spl10_2 | spl10_1 | ~spl10_6 | ~spl10_7 | ~spl10_12),
% 0.21/0.52    inference(avatar_split_clause,[],[f137,f110,f88,f75,f55,f59,f63,f67,f71])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    spl10_5 <=> k1_xboole_0 = sK0),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    spl10_4 <=> k1_xboole_0 = sK1),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    spl10_3 <=> k1_xboole_0 = sK2),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    spl10_2 <=> k1_xboole_0 = sK3),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    spl10_1 <=> sK4 = k8_mcart_1(sK0,sK1,sK2,sK3,sK5)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    spl10_6 <=> m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    spl10_7 <=> sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5)),sK9(sK0,sK1,sK2,sK3,sK5))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.21/0.52  % (2776)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    spl10_12 <=> sK4 = sK6(sK0,sK1,sK2,sK3,sK5)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 0.21/0.52  fof(f137,plain,(
% 0.21/0.52    sK4 = k8_mcart_1(sK0,sK1,sK2,sK3,sK5) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl10_6 | ~spl10_7 | ~spl10_12)),
% 0.21/0.52    inference(forward_demodulation,[],[f136,f111])).
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    sK4 = sK6(sK0,sK1,sK2,sK3,sK5) | ~spl10_12),
% 0.21/0.52    inference(avatar_component_clause,[],[f110])).
% 0.21/0.52  fof(f136,plain,(
% 0.21/0.52    k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = sK6(sK0,sK1,sK2,sK3,sK5) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl10_6 | ~spl10_7)),
% 0.21/0.52    inference(resolution,[],[f91,f76])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | ~spl10_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f75])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | sK6(sK0,sK1,sK2,sK3,sK5) = k8_mcart_1(X0,X1,X2,X3,sK5) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) ) | ~spl10_7),
% 0.21/0.52    inference(superposition,[],[f53,f89])).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5)),sK9(sK0,sK1,sK2,sK3,sK5)) | ~spl10_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f88])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(k4_tarski(k3_mcart_1(X5,X6,X7),X8),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k8_mcart_1(X0,X1,X2,X3,k4_tarski(k3_mcart_1(X5,X6,X7),X8)) = X5 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(equality_resolution,[],[f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k8_mcart_1(X0,X1,X2,X3,X4) = X5 | k4_tarski(k3_mcart_1(X5,X6,X7),X8) != X4 | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(definition_unfolding,[],[f34,f27,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f28,f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k8_mcart_1(X0,X1,X2,X3,X4) = X5 | k4_mcart_1(X5,X6,X7,X8) != X4 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (! [X4] : (! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ~(? [X4] : (? [X5,X6,X7,X8] : (~(k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_mcart_1)).
% 0.21/0.52  fof(f121,plain,(
% 0.21/0.52    spl10_5 | spl10_4 | spl10_3 | spl10_2 | ~spl10_6 | spl10_11),
% 0.21/0.52    inference(avatar_split_clause,[],[f120,f107,f75,f59,f63,f67,f71])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    spl10_11 <=> m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 0.21/0.52  fof(f120,plain,(
% 0.21/0.52    ~m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl10_11),
% 0.21/0.52    inference(resolution,[],[f108,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK9(X0,X1,X2,X3,X4),X3) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(definition_unfolding,[],[f32,f38])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK9(X0,X1,X2,X3,X4),X3) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (! [X4] : (((((k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X4 & m1_subset_1(sK9(X0,X1,X2,X3,X4),X3)) & m1_subset_1(sK8(X0,X1,X2,X3,X4),X2)) & m1_subset_1(sK7(X0,X1,X2,X3,X4),X1)) & m1_subset_1(sK6(X0,X1,X2,X3,X4),X0)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f10,f17,f16,f15,f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X4,X3,X2,X1,X0] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(X5,X0)) => (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(sK6(X0,X1,X2,X3,X4),X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(sK6(X0,X1,X2,X3,X4),X0)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X4,X3,X2,X1,X0] : (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(sK6(X0,X1,X2,X3,X4),X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) => (? [X7] : (? [X8] : (k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(sK7(X0,X1,X2,X3,X4),X1)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X4,X3,X2,X1,X0] : (? [X7] : (? [X8] : (k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) => (? [X8] : (k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(sK8(X0,X1,X2,X3,X4),X2)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X4,X3,X2,X1,X0] : (? [X8] : (k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),X8) = X4 & m1_subset_1(X8,X3)) => (k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X4 & m1_subset_1(sK9(X0,X1,X2,X3,X4),X3)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (! [X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(X5,X0)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ~(? [X4] : (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => ! [X8] : (m1_subset_1(X8,X3) => k4_mcart_1(X5,X6,X7,X8) != X4)))) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_mcart_1)).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    ~m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) | spl10_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f107])).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    spl10_5 | spl10_4 | spl10_3 | spl10_2 | ~spl10_6 | spl10_10),
% 0.21/0.52    inference(avatar_split_clause,[],[f118,f104,f75,f59,f63,f67,f71])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    spl10_10 <=> m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 0.21/0.52  fof(f118,plain,(
% 0.21/0.52    ~m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl10_10),
% 0.21/0.52    inference(resolution,[],[f105,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK8(X0,X1,X2,X3,X4),X2) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(definition_unfolding,[],[f31,f38])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK8(X0,X1,X2,X3,X4),X2) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    ~m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) | spl10_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f104])).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    spl10_5 | spl10_4 | spl10_3 | spl10_2 | ~spl10_6 | spl10_9),
% 0.21/0.52    inference(avatar_split_clause,[],[f116,f101,f75,f59,f63,f67,f71])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    spl10_9 <=> m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 0.21/0.52  fof(f116,plain,(
% 0.21/0.52    ~m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl10_9),
% 0.21/0.52    inference(resolution,[],[f102,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK7(X0,X1,X2,X3,X4),X1) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(definition_unfolding,[],[f30,f38])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK7(X0,X1,X2,X3,X4),X1) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f102,plain,(
% 0.21/0.52    ~m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1) | spl10_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f101])).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    spl10_5 | spl10_4 | spl10_3 | spl10_2 | ~spl10_6 | spl10_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f113,f98,f75,f59,f63,f67,f71])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    spl10_8 <=> m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    ~m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl10_8),
% 0.21/0.52    inference(resolution,[],[f99,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK6(X0,X1,X2,X3,X4),X0) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(definition_unfolding,[],[f29,f38])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK6(X0,X1,X2,X3,X4),X0) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) | spl10_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f98])).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    ~spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_11 | spl10_12 | ~spl10_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f96,f88,f110,f107,f104,f101,f98])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    sK4 = sK6(sK0,sK1,sK2,sK3,sK5) | ~m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) | ~m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) | ~m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) | ~spl10_7),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f95])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    sK5 != sK5 | sK4 = sK6(sK0,sK1,sK2,sK3,sK5) | ~m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) | ~m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) | ~m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) | ~spl10_7),
% 0.21/0.52    inference(superposition,[],[f39,f89])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X6,X8,X7,X9] : (sK5 != k4_tarski(k3_mcart_1(X6,X7,X8),X9) | sK4 = X6 | ~m1_subset_1(X9,sK3) | ~m1_subset_1(X8,sK2) | ~m1_subset_1(X7,sK1) | ~m1_subset_1(X6,sK0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f20,f27])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ( ! [X6,X8,X7,X9] : (sK4 = X6 | k4_mcart_1(X6,X7,X8,X9) != sK5 | ~m1_subset_1(X9,sK3) | ~m1_subset_1(X8,sK2) | ~m1_subset_1(X7,sK1) | ~m1_subset_1(X6,sK0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    sK4 != k8_mcart_1(sK0,sK1,sK2,sK3,sK5) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (sK4 = X6 | k4_mcart_1(X6,X7,X8,X9) != sK5 | ~m1_subset_1(X9,sK3)) | ~m1_subset_1(X8,sK2)) | ~m1_subset_1(X7,sK1)) | ~m1_subset_1(X6,sK0)) & m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f9,f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3,X4,X5] : (k8_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X6 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))) => (sK4 != k8_mcart_1(sK0,sK1,sK2,sK3,sK5) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (sK4 = X6 | k4_mcart_1(X6,X7,X8,X9) != sK5 | ~m1_subset_1(X9,sK3)) | ~m1_subset_1(X8,sK2)) | ~m1_subset_1(X7,sK1)) | ~m1_subset_1(X6,sK0)) & m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3,X4,X5] : (k8_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X6 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.52    inference(flattening,[],[f8])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3,X4,X5] : (((k8_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X6] : (! [X7] : (! [X8] : (! [X9] : ((X4 = X6 | k4_mcart_1(X6,X7,X8,X9) != X5) | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0))) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X6))))) => (k8_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.52    inference(negated_conjecture,[],[f6])).
% 0.21/0.52  fof(f6,conjecture,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X6))))) => (k8_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_mcart_1)).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    spl10_5 | spl10_4 | spl10_3 | spl10_2 | spl10_7 | ~spl10_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f78,f75,f88,f59,f63,f67,f71])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5)),sK9(sK0,sK1,sK2,sK3,sK5)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl10_6),
% 0.21/0.52    inference(resolution,[],[f41,f76])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k4_tarski(k3_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4)),sK9(X0,X1,X2,X3,X4)) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(definition_unfolding,[],[f33,f27,f38])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X4 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    spl10_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f40,f75])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))),
% 0.21/0.52    inference(definition_unfolding,[],[f19,f38])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    ~spl10_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f21,f71])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    k1_xboole_0 != sK0),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    ~spl10_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f22,f67])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    k1_xboole_0 != sK1),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    ~spl10_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f23,f63])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    k1_xboole_0 != sK2),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ~spl10_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f24,f59])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    k1_xboole_0 != sK3),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ~spl10_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f25,f55])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    sK4 != k8_mcart_1(sK0,sK1,sK2,sK3,sK5)),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (2793)------------------------------
% 0.21/0.52  % (2793)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (2793)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (2793)Memory used [KB]: 11001
% 0.21/0.52  % (2793)Time elapsed: 0.113 s
% 0.21/0.52  % (2793)------------------------------
% 0.21/0.52  % (2793)------------------------------
% 0.21/0.52  % (2803)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.52  % (2774)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (2787)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (2789)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (2774)Refutation not found, incomplete strategy% (2774)------------------------------
% 0.21/0.52  % (2774)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (2774)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (2774)Memory used [KB]: 1791
% 0.21/0.52  % (2774)Time elapsed: 0.113 s
% 0.21/0.52  % (2774)------------------------------
% 0.21/0.52  % (2774)------------------------------
% 0.21/0.52  % (2773)Success in time 0.164 s
%------------------------------------------------------------------------------
