%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 159 expanded)
%              Number of leaves         :   23 (  65 expanded)
%              Depth                    :    9
%              Number of atoms          :  240 ( 469 expanded)
%              Number of equality atoms :   99 ( 216 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f178,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f53,f57,f61,f76,f84,f88,f95,f105,f121,f138,f150,f173])).

fof(f173,plain,
    ( spl3_4
    | spl3_5
    | ~ spl3_9
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f172,f136,f86,f59,f55])).

fof(f55,plain,
    ( spl3_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f59,plain,
    ( spl3_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f86,plain,
    ( spl3_9
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f136,plain,
    ( spl3_15
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f172,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ spl3_9
    | ~ spl3_15 ),
    inference(duplicate_literal_removal,[],[f171])).

fof(f171,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl3_9
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f159,f137])).

fof(f137,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f136])).

fof(f159,plain,
    ( sK0 = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl3_9 ),
    inference(superposition,[],[f39,f87])).

fof(f87,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f86])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

fof(f150,plain,(
    ~ spl3_13 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | ~ spl3_13 ),
    inference(trivial_inequality_removal,[],[f144])).

fof(f144,plain,
    ( sK2 != sK2
    | ~ spl3_13 ),
    inference(superposition,[],[f63,f120])).

fof(f120,plain,
    ( sK2 = k4_tarski(sK2,k2_mcart_1(sK2))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl3_13
  <=> sK2 = k4_tarski(sK2,k2_mcart_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f63,plain,(
    ! [X0,X1] : k4_tarski(X0,X1) != X0 ),
    inference(superposition,[],[f42,f32])).

fof(f32,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f42,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k1_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f138,plain,
    ( spl3_15
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f130,f103,f136])).

fof(f103,plain,
    ( spl3_10
  <=> v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f130,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl3_10 ),
    inference(resolution,[],[f104,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f104,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f103])).

fof(f121,plain,
    ( spl3_6
    | spl3_13
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f117,f51,f44,f119,f71])).

fof(f71,plain,
    ( spl3_6
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f44,plain,
    ( spl3_1
  <=> sK2 = k1_mcart_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f51,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f117,plain,
    ( sK2 = k4_tarski(sK2,k2_mcart_1(sK2))
    | v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f66,f45])).

fof(f45,plain,
    ( sK2 = k1_mcart_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f66,plain,
    ( sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))
    | v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl3_3 ),
    inference(resolution,[],[f65,f52])).

fof(f52,plain,
    ( m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k2_zfmisc_1(X1,X2))
      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | v1_xboole_0(k2_zfmisc_1(X1,X2)) ) ),
    inference(resolution,[],[f64,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    inference(resolution,[],[f38,f31])).

fof(f31,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,X1)
      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f105,plain,
    ( spl3_10
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f101,f86,f82,f103])).

fof(f82,plain,
    ( spl3_8
  <=> v1_xboole_0(k1_relat_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f101,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f83,f87])).

fof(f83,plain,
    ( v1_xboole_0(k1_relat_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f82])).

fof(f95,plain,(
    ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f94])).

fof(f94,plain,
    ( $false
    | ~ spl3_7 ),
    inference(trivial_inequality_removal,[],[f91])).

fof(f91,plain,
    ( sK2 != sK2
    | ~ spl3_7 ),
    inference(superposition,[],[f62,f75])).

fof(f75,plain,
    ( sK2 = k4_tarski(k1_mcart_1(sK2),sK2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl3_7
  <=> sK2 = k4_tarski(k1_mcart_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f62,plain,(
    ! [X0,X1] : k4_tarski(X0,X1) != X1 ),
    inference(superposition,[],[f41,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f8])).

fof(f41,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f88,plain,
    ( spl3_9
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f80,f71,f86])).

fof(f80,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl3_6 ),
    inference(resolution,[],[f72,f27])).

fof(f72,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f71])).

fof(f84,plain,
    ( spl3_8
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f79,f71,f82])).

fof(f79,plain,
    ( v1_xboole_0(k1_relat_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_6 ),
    inference(resolution,[],[f72,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

fof(f76,plain,
    ( spl3_6
    | spl3_7
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f69,f51,f47,f74,f71])).

fof(f47,plain,
    ( spl3_2
  <=> sK2 = k2_mcart_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f69,plain,
    ( sK2 = k4_tarski(k1_mcart_1(sK2),sK2)
    | v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f66,f48])).

fof(f48,plain,
    ( sK2 = k2_mcart_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f61,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f23,f59])).

fof(f23,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( sK2 = k2_mcart_1(sK2)
      | sK2 = k1_mcart_1(sK2) )
    & m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f20,f19])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( k2_mcart_1(X2) = X2
              | k1_mcart_1(X2) = X2 )
            & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ? [X2] :
          ( ( k2_mcart_1(X2) = X2
            | k1_mcart_1(X2) = X2 )
          & m1_subset_1(X2,k2_zfmisc_1(sK0,sK1)) )
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X2] :
        ( ( k2_mcart_1(X2) = X2
          | k1_mcart_1(X2) = X2 )
        & m1_subset_1(X2,k2_zfmisc_1(sK0,sK1)) )
   => ( ( sK2 = k2_mcart_1(sK2)
        | sK2 = k1_mcart_1(sK2) )
      & m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( k2_mcart_1(X2) = X2
            | k1_mcart_1(X2) = X2 )
          & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ~ ! [X2] :
                ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
               => ( k2_mcart_1(X2) != X2
                  & k1_mcart_1(X2) != X2 ) )
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ~ ( ~ ! [X2] :
              ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
             => ( k2_mcart_1(X2) != X2
                & k1_mcart_1(X2) != X2 ) )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_mcart_1)).

fof(f57,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f24,f55])).

fof(f24,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f21])).

fof(f53,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f25,f51])).

fof(f25,plain,(
    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f49,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f26,f47,f44])).

fof(f26,plain,
    ( sK2 = k2_mcart_1(sK2)
    | sK2 = k1_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:27:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.44  % (6833)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.44  % (6833)Refutation not found, incomplete strategy% (6833)------------------------------
% 0.21/0.44  % (6833)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (6826)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.45  % (6841)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.45  % (6833)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.45  
% 0.21/0.45  % (6833)Memory used [KB]: 6012
% 0.21/0.45  % (6833)Time elapsed: 0.055 s
% 0.21/0.45  % (6833)------------------------------
% 0.21/0.45  % (6833)------------------------------
% 0.21/0.46  % (6835)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.47  % (6824)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.47  % (6827)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (6841)Refutation not found, incomplete strategy% (6841)------------------------------
% 0.21/0.47  % (6841)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (6841)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (6841)Memory used [KB]: 10618
% 0.21/0.47  % (6841)Time elapsed: 0.083 s
% 0.21/0.47  % (6841)------------------------------
% 0.21/0.47  % (6841)------------------------------
% 0.21/0.47  % (6824)Refutation not found, incomplete strategy% (6824)------------------------------
% 0.21/0.47  % (6824)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (6824)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (6824)Memory used [KB]: 10618
% 0.21/0.47  % (6824)Time elapsed: 0.062 s
% 0.21/0.47  % (6824)------------------------------
% 0.21/0.47  % (6824)------------------------------
% 0.21/0.47  % (6827)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f178,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f49,f53,f57,f61,f76,f84,f88,f95,f105,f121,f138,f150,f173])).
% 0.21/0.47  fof(f173,plain,(
% 0.21/0.47    spl3_4 | spl3_5 | ~spl3_9 | ~spl3_15),
% 0.21/0.47    inference(avatar_split_clause,[],[f172,f136,f86,f59,f55])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    spl3_4 <=> k1_xboole_0 = sK1),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    spl3_5 <=> k1_xboole_0 = sK0),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    spl3_9 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.47  fof(f136,plain,(
% 0.21/0.47    spl3_15 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.47  fof(f172,plain,(
% 0.21/0.47    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | (~spl3_9 | ~spl3_15)),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f171])).
% 0.21/0.47  fof(f171,plain,(
% 0.21/0.47    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl3_9 | ~spl3_15)),
% 0.21/0.47    inference(forward_demodulation,[],[f159,f137])).
% 0.21/0.47  fof(f137,plain,(
% 0.21/0.47    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl3_15),
% 0.21/0.47    inference(avatar_component_clause,[],[f136])).
% 0.21/0.47  fof(f159,plain,(
% 0.21/0.47    sK0 = k1_relat_1(k1_xboole_0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl3_9),
% 0.21/0.47    inference(superposition,[],[f39,f87])).
% 0.21/0.47  fof(f87,plain,(
% 0.21/0.47    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl3_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f86])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).
% 0.21/0.47  fof(f150,plain,(
% 0.21/0.47    ~spl3_13),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f149])).
% 0.21/0.47  fof(f149,plain,(
% 0.21/0.47    $false | ~spl3_13),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f144])).
% 0.21/0.47  fof(f144,plain,(
% 0.21/0.47    sK2 != sK2 | ~spl3_13),
% 0.21/0.47    inference(superposition,[],[f63,f120])).
% 0.21/0.47  fof(f120,plain,(
% 0.21/0.47    sK2 = k4_tarski(sK2,k2_mcart_1(sK2)) | ~spl3_13),
% 0.21/0.47    inference(avatar_component_clause,[],[f119])).
% 0.21/0.47  fof(f119,plain,(
% 0.21/0.47    spl3_13 <=> sK2 = k4_tarski(sK2,k2_mcart_1(sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_tarski(X0,X1) != X0) )),
% 0.21/0.47    inference(superposition,[],[f42,f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X2,X1] : (k4_tarski(X1,X2) != k1_mcart_1(k4_tarski(X1,X2))) )),
% 0.21/0.47    inference(equality_resolution,[],[f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k1_mcart_1(X0) != X0 | k4_tarski(X1,X2) != X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0] : ((k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).
% 0.21/0.47  fof(f138,plain,(
% 0.21/0.47    spl3_15 | ~spl3_10),
% 0.21/0.47    inference(avatar_split_clause,[],[f130,f103,f136])).
% 0.21/0.47  fof(f103,plain,(
% 0.21/0.47    spl3_10 <=> v1_xboole_0(k1_relat_1(k1_xboole_0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.47  fof(f130,plain,(
% 0.21/0.47    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl3_10),
% 0.21/0.47    inference(resolution,[],[f104,f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.47  fof(f104,plain,(
% 0.21/0.47    v1_xboole_0(k1_relat_1(k1_xboole_0)) | ~spl3_10),
% 0.21/0.47    inference(avatar_component_clause,[],[f103])).
% 0.21/0.47  fof(f121,plain,(
% 0.21/0.47    spl3_6 | spl3_13 | ~spl3_1 | ~spl3_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f117,f51,f44,f119,f71])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    spl3_6 <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    spl3_1 <=> sK2 = k1_mcart_1(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    spl3_3 <=> m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.47  fof(f117,plain,(
% 0.21/0.47    sK2 = k4_tarski(sK2,k2_mcart_1(sK2)) | v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | (~spl3_1 | ~spl3_3)),
% 0.21/0.47    inference(forward_demodulation,[],[f66,f45])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    sK2 = k1_mcart_1(sK2) | ~spl3_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f44])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) | v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | ~spl3_3),
% 0.21/0.47    inference(resolution,[],[f65,f52])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) | ~spl3_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f51])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k2_zfmisc_1(X1,X2)) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | v1_xboole_0(k2_zfmisc_1(X1,X2))) )),
% 0.21/0.47    inference(resolution,[],[f64,f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.21/0.47    inference(nnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0) )),
% 0.21/0.47    inference(resolution,[],[f38,f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r2_hidden(X0,X1) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(flattening,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).
% 0.21/0.47  fof(f105,plain,(
% 0.21/0.47    spl3_10 | ~spl3_8 | ~spl3_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f101,f86,f82,f103])).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    spl3_8 <=> v1_xboole_0(k1_relat_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.47  fof(f101,plain,(
% 0.21/0.47    v1_xboole_0(k1_relat_1(k1_xboole_0)) | (~spl3_8 | ~spl3_9)),
% 0.21/0.47    inference(forward_demodulation,[],[f83,f87])).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    v1_xboole_0(k1_relat_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f82])).
% 0.21/0.47  fof(f95,plain,(
% 0.21/0.47    ~spl3_7),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f94])).
% 0.21/0.47  fof(f94,plain,(
% 0.21/0.47    $false | ~spl3_7),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f91])).
% 0.21/0.47  fof(f91,plain,(
% 0.21/0.47    sK2 != sK2 | ~spl3_7),
% 0.21/0.47    inference(superposition,[],[f62,f75])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    sK2 = k4_tarski(k1_mcart_1(sK2),sK2) | ~spl3_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f74])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    spl3_7 <=> sK2 = k4_tarski(k1_mcart_1(sK2),sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_tarski(X0,X1) != X1) )),
% 0.21/0.47    inference(superposition,[],[f41,f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ( ! [X2,X1] : (k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2))) )),
% 0.21/0.47    inference(equality_resolution,[],[f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k2_mcart_1(X0) != X0 | k4_tarski(X1,X2) != X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    spl3_9 | ~spl3_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f80,f71,f86])).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl3_6),
% 0.21/0.47    inference(resolution,[],[f72,f27])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | ~spl3_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f71])).
% 0.21/0.47  fof(f84,plain,(
% 0.21/0.47    spl3_8 | ~spl3_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f79,f71,f82])).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    v1_xboole_0(k1_relat_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_6),
% 0.21/0.47    inference(resolution,[],[f72,f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_xboole_0(X0) | v1_xboole_0(k1_relat_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k1_relat_1(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    spl3_6 | spl3_7 | ~spl3_2 | ~spl3_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f69,f51,f47,f74,f71])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    spl3_2 <=> sK2 = k2_mcart_1(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    sK2 = k4_tarski(k1_mcart_1(sK2),sK2) | v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | (~spl3_2 | ~spl3_3)),
% 0.21/0.47    inference(forward_demodulation,[],[f66,f48])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    sK2 = k2_mcart_1(sK2) | ~spl3_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f47])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    ~spl3_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f23,f59])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    k1_xboole_0 != sK0),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ((sK2 = k2_mcart_1(sK2) | sK2 = k1_mcart_1(sK2)) & m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f20,f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ? [X0,X1] : (? [X2] : ((k2_mcart_1(X2) = X2 | k1_mcart_1(X2) = X2) & m1_subset_1(X2,k2_zfmisc_1(X0,X1))) & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X2] : ((k2_mcart_1(X2) = X2 | k1_mcart_1(X2) = X2) & m1_subset_1(X2,k2_zfmisc_1(sK0,sK1))) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0)),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ? [X2] : ((k2_mcart_1(X2) = X2 | k1_mcart_1(X2) = X2) & m1_subset_1(X2,k2_zfmisc_1(sK0,sK1))) => ((sK2 = k2_mcart_1(sK2) | sK2 = k1_mcart_1(sK2)) & m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ? [X0,X1] : (? [X2] : ((k2_mcart_1(X2) = X2 | k1_mcart_1(X2) = X2) & m1_subset_1(X2,k2_zfmisc_1(X0,X1))) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.47    inference(ennf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => (k2_mcart_1(X2) != X2 & k1_mcart_1(X2) != X2)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.47    inference(negated_conjecture,[],[f9])).
% 0.21/0.47  fof(f9,conjecture,(
% 0.21/0.47    ! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => (k2_mcart_1(X2) != X2 & k1_mcart_1(X2) != X2)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_mcart_1)).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    ~spl3_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f24,f55])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    k1_xboole_0 != sK1),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    spl3_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f25,f51])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    spl3_1 | spl3_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f26,f47,f44])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    sK2 = k2_mcart_1(sK2) | sK2 = k1_mcart_1(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (6827)------------------------------
% 0.21/0.47  % (6827)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (6827)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (6827)Memory used [KB]: 10618
% 0.21/0.47  % (6827)Time elapsed: 0.006 s
% 0.21/0.47  % (6827)------------------------------
% 0.21/0.47  % (6827)------------------------------
% 0.21/0.48  % (6834)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (6820)Success in time 0.122 s
%------------------------------------------------------------------------------
