%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:32 EST 2020

% Result     : Theorem 1.52s
% Output     : Refutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 524 expanded)
%              Number of leaves         :   20 ( 153 expanded)
%              Depth                    :   21
%              Number of atoms          :  509 (2795 expanded)
%              Number of equality atoms :  266 (1671 expanded)
%              Maximal formula depth    :   26 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f229,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f140,f144,f148,f152,f228])).

fof(f228,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f227])).

fof(f227,plain,
    ( $false
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f218,f191])).

fof(f191,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f190,f59])).

fof(f59,plain,(
    o_0_0_xboole_0 != sK0 ),
    inference(definition_unfolding,[],[f35,f39])).

fof(f39,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f35,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f18,f31])).

fof(f31,plain,
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

fof(f190,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | o_0_0_xboole_0 = sK0
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f181,f58])).

fof(f58,plain,(
    o_0_0_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f36,f39])).

fof(f36,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f32])).

fof(f181,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | o_0_0_xboole_0 = sK1
    | o_0_0_xboole_0 = sK0
    | ~ spl5_1 ),
    inference(superposition,[],[f80,f175])).

fof(f175,plain,
    ( o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f154,f57])).

fof(f57,plain,(
    o_0_0_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f37,f39])).

fof(f37,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f32])).

fof(f154,plain,
    ( o_0_0_xboole_0 = sK2
    | o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl5_1 ),
    inference(resolution,[],[f153,f80])).

fof(f153,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl5_1 ),
    inference(resolution,[],[f130,f61])).

fof(f61,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f33,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f33,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f32])).

fof(f130,plain,
    ( ! [X6,X8,X7] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X6,X7),X8))
        | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X6,X7),X8)) )
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl5_1
  <=> ! [X7,X8,X6] :
        ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X6,X7),X8))
        | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X6,X7),X8)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f79,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f40,f39])).

fof(f40,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
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

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(superposition,[],[f41,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f45,f39,f39])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

fof(f41,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

fof(f218,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl5_1 ),
    inference(backward_demodulation,[],[f176,f196])).

fof(f196,plain,
    ( o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,sK2)
    | ~ spl5_1 ),
    inference(resolution,[],[f176,f62])).

fof(f176,plain,
    ( v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,sK2))
    | ~ spl5_1 ),
    inference(backward_demodulation,[],[f153,f175])).

fof(f152,plain,(
    ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f150,f57])).

fof(f150,plain,
    ( o_0_0_xboole_0 = sK2
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f149,f59])).

fof(f149,plain,
    ( o_0_0_xboole_0 = sK0
    | o_0_0_xboole_0 = sK2
    | ~ spl5_4 ),
    inference(resolution,[],[f139,f61])).

fof(f139,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1))
        | o_0_0_xboole_0 = X0
        | o_0_0_xboole_0 = X1 )
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl5_4
  <=> ! [X1,X0] :
        ( o_0_0_xboole_0 = X0
        | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1))
        | o_0_0_xboole_0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f148,plain,(
    ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f146,f57])).

fof(f146,plain,
    ( o_0_0_xboole_0 = sK2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f145,f58])).

fof(f145,plain,
    ( o_0_0_xboole_0 = sK1
    | o_0_0_xboole_0 = sK2
    | ~ spl5_3 ),
    inference(resolution,[],[f136,f61])).

fof(f136,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X2),X3))
        | o_0_0_xboole_0 = X2
        | o_0_0_xboole_0 = X3 )
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl5_3
  <=> ! [X3,X2] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X2),X3))
        | o_0_0_xboole_0 = X2
        | o_0_0_xboole_0 = X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f144,plain,(
    ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f143])).

fof(f143,plain,
    ( $false
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f142,f58])).

fof(f142,plain,
    ( o_0_0_xboole_0 = sK1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f141,f59])).

fof(f141,plain,
    ( o_0_0_xboole_0 = sK0
    | o_0_0_xboole_0 = sK1
    | ~ spl5_2 ),
    inference(resolution,[],[f133,f61])).

fof(f133,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X4,X5),sK2))
        | o_0_0_xboole_0 = X4
        | o_0_0_xboole_0 = X5 )
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f132])).

% (14479)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
fof(f132,plain,
    ( spl5_2
  <=> ! [X5,X4] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X4,X5),sK2))
        | o_0_0_xboole_0 = X4
        | o_0_0_xboole_0 = X5 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f140,plain,
    ( spl5_1
    | spl5_2
    | spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f127,f138,f135,f132,f129])).

fof(f127,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( o_0_0_xboole_0 = X0
      | o_0_0_xboole_0 = X1
      | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X2),X3))
      | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1))
      | o_0_0_xboole_0 = X3
      | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X4,X5),sK2))
      | o_0_0_xboole_0 = X5
      | o_0_0_xboole_0 = X4
      | o_0_0_xboole_0 = X2
      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X6,X7),X8))
      | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X6,X7),X8)) ) ),
    inference(subsumption_resolution,[],[f126,f100])).

fof(f100,plain,(
    sK3 != k2_mcart_1(sK4) ),
    inference(subsumption_resolution,[],[f99,f59])).

fof(f99,plain,
    ( sK3 != k2_mcart_1(sK4)
    | o_0_0_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f98,f58])).

fof(f98,plain,
    ( sK3 != k2_mcart_1(sK4)
    | o_0_0_xboole_0 = sK1
    | o_0_0_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f97,f57])).

fof(f97,plain,
    ( sK3 != k2_mcart_1(sK4)
    | o_0_0_xboole_0 = sK2
    | o_0_0_xboole_0 = sK1
    | o_0_0_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f94,f61])).

fof(f94,plain,
    ( sK3 != k2_mcart_1(sK4)
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | o_0_0_xboole_0 = sK2
    | o_0_0_xboole_0 = sK1
    | o_0_0_xboole_0 = sK0 ),
    inference(superposition,[],[f38,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f53,f48,f39,f39,f39])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f38,plain,(
    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f126,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( o_0_0_xboole_0 = X0
      | sK3 = k2_mcart_1(sK4)
      | o_0_0_xboole_0 = X1
      | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X2),X3))
      | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1))
      | o_0_0_xboole_0 = X3
      | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X4,X5),sK2))
      | o_0_0_xboole_0 = X5
      | o_0_0_xboole_0 = X4
      | o_0_0_xboole_0 = X2
      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X6,X7),X8))
      | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X6,X7),X8)) ) ),
    inference(equality_resolution,[],[f123])).

fof(f123,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( sK4 != X2
      | o_0_0_xboole_0 = X1
      | sK3 = k2_mcart_1(X2)
      | o_0_0_xboole_0 = X0
      | ~ m1_subset_1(X2,k2_zfmisc_1(k2_zfmisc_1(sK0,X3),X4))
      | ~ m1_subset_1(X2,k2_zfmisc_1(k2_zfmisc_1(X1,sK1),X0))
      | o_0_0_xboole_0 = X4
      | ~ m1_subset_1(X2,k2_zfmisc_1(k2_zfmisc_1(X5,X6),sK2))
      | o_0_0_xboole_0 = X6
      | o_0_0_xboole_0 = X5
      | o_0_0_xboole_0 = X3
      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X7,X8),X9))
      | ~ m1_subset_1(X2,k2_zfmisc_1(k2_zfmisc_1(X7,X8),X9)) ) ),
    inference(resolution,[],[f122,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f122,plain,(
    ! [X4,X2,X0,X10,X8,X7,X3,X1,X11,X9] :
      ( ~ r2_hidden(X3,k2_zfmisc_1(k2_zfmisc_1(X9,X10),X11))
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X2
      | k2_mcart_1(X3) = sK3
      | sK4 != X3
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X4))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X2,sK1),X1))
      | o_0_0_xboole_0 = X4
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X7,X8),sK2))
      | o_0_0_xboole_0 = X8
      | o_0_0_xboole_0 = X7
      | o_0_0_xboole_0 = X0 ) ),
    inference(condensation,[],[f120])).

fof(f120,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X11,X9] :
      ( o_0_0_xboole_0 = X0
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X2
      | k2_mcart_1(X3) = sK3
      | sK4 != X3
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X4))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X2,sK1),X1))
      | o_0_0_xboole_0 = X4
      | ~ r2_hidden(X3,k2_zfmisc_1(X5,X6))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X7,X8),sK2))
      | o_0_0_xboole_0 = X8
      | o_0_0_xboole_0 = X7
      | ~ r2_hidden(X3,k2_zfmisc_1(k2_zfmisc_1(X9,X10),X11)) ) ),
    inference(resolution,[],[f118,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f118,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] :
      ( ~ r2_hidden(k1_mcart_1(X4),k2_zfmisc_1(X5,X6))
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X3
      | sK3 = k2_mcart_1(X4)
      | sK4 != X4
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(sK0,X1),X0))
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X3,sK1),X2))
      | o_0_0_xboole_0 = X0
      | ~ r2_hidden(X4,k2_zfmisc_1(X7,X8))
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X9,X10),sK2))
      | o_0_0_xboole_0 = X10
      | o_0_0_xboole_0 = X9 ) ),
    inference(subsumption_resolution,[],[f116,f57])).

fof(f116,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] :
      ( o_0_0_xboole_0 = X0
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X3
      | sK3 = k2_mcart_1(X4)
      | sK4 != X4
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(sK0,X1),X0))
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X3,sK1),X2))
      | ~ r2_hidden(k1_mcart_1(X4),k2_zfmisc_1(X5,X6))
      | ~ r2_hidden(X4,k2_zfmisc_1(X7,X8))
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X9,X10),sK2))
      | o_0_0_xboole_0 = sK2
      | o_0_0_xboole_0 = X10
      | o_0_0_xboole_0 = X9 ) ),
    inference(resolution,[],[f114,f96])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_mcart_1(X3),X2)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f95])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_mcart_1(X3),X2)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(superposition,[],[f70,f65])).

% (14467)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f56,f48])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_mcart_1)).

fof(f114,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(k2_mcart_1(X0),sK2)
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X4
      | k2_mcart_1(X0) = sK3
      | sK4 != X0
      | ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,X2),X1))
      | ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X4,sK1),X3))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X5,X6))
      | ~ r2_hidden(X0,k2_zfmisc_1(X7,X8)) ) ),
    inference(superposition,[],[f112,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(resolution,[],[f43,f42])).

fof(f42,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,X1)
      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f112,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( sK4 != k4_tarski(k1_mcart_1(X0),X5)
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X4
      | sK3 = X5
      | ~ m1_subset_1(X5,sK2)
      | ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,X1),X2))
      | ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X4,sK1),X3))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X6,X7)) ) ),
    inference(subsumption_resolution,[],[f110,f59])).

fof(f110,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,X1),X2))
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = sK0
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X4
      | sK3 = X5
      | ~ m1_subset_1(X5,sK2)
      | sK4 != k4_tarski(k1_mcart_1(X0),X5)
      | ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X4,sK1),X3))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X6,X7)) ) ),
    inference(resolution,[],[f109,f107])).

fof(f107,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(k1_mcart_1(k1_mcart_1(X0)),sK0)
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | sK3 = X3
      | ~ m1_subset_1(X3,sK2)
      | sK4 != k4_tarski(k1_mcart_1(X0),X3)
      | ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,sK1),X2))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X4,X5)) ) ),
    inference(subsumption_resolution,[],[f106,f58])).

fof(f106,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,sK1),X2))
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = sK1
      | o_0_0_xboole_0 = X1
      | sK3 = X3
      | ~ m1_subset_1(X3,sK2)
      | sK4 != k4_tarski(k1_mcart_1(X0),X3)
      | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(X0)),sK0)
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X4,X5)) ) ),
    inference(resolution,[],[f105,f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(k2_mcart_1(X0),sK1)
      | sK3 = X1
      | ~ m1_subset_1(X1,sK2)
      | k4_tarski(X0,X1) != sK4
      | ~ m1_subset_1(k1_mcart_1(X0),sK0)
      | ~ r2_hidden(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(superposition,[],[f60,f78])).

fof(f60,plain,(
    ! [X6,X7,X5] :
      ( sK4 != k4_tarski(k4_tarski(X5,X6),X7)
      | sK3 = X7
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(definition_unfolding,[],[f34,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f34,plain,(
    ! [X6,X7,X5] :
      ( sK3 = X7
      | k3_mcart_1(X5,X6,X7) != sK4
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f105,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_mcart_1(k1_mcart_1(X3)),X1)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f104])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_mcart_1(k1_mcart_1(X3)),X1)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(superposition,[],[f69,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f52,f48,f39,f39,f39])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f55,f48])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_mcart_1)).

fof(f109,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k1_mcart_1(k1_mcart_1(X3)),X0)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f108])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k1_mcart_1(k1_mcart_1(X3)),X0)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(superposition,[],[f68,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f51,f48,f39,f39,f39])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f54,f48])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:33:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (14471)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (14482)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (14474)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (14463)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (14489)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (14466)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (14460)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (14482)Refutation not found, incomplete strategy% (14482)------------------------------
% 0.21/0.54  % (14482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (14472)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (14482)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (14482)Memory used [KB]: 10746
% 0.21/0.54  % (14482)Time elapsed: 0.083 s
% 0.21/0.54  % (14482)------------------------------
% 0.21/0.54  % (14482)------------------------------
% 0.21/0.54  % (14462)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (14481)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (14464)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (14483)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (14465)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.55  % (14470)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (14470)Refutation not found, incomplete strategy% (14470)------------------------------
% 0.21/0.55  % (14470)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (14470)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (14470)Memory used [KB]: 10618
% 0.21/0.55  % (14470)Time elapsed: 0.135 s
% 0.21/0.55  % (14470)------------------------------
% 0.21/0.55  % (14470)------------------------------
% 0.21/0.55  % (14461)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.55  % (14480)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (14475)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (14480)Refutation not found, incomplete strategy% (14480)------------------------------
% 0.21/0.55  % (14480)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (14480)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (14480)Memory used [KB]: 10874
% 0.21/0.55  % (14480)Time elapsed: 0.106 s
% 0.21/0.55  % (14480)------------------------------
% 0.21/0.55  % (14480)------------------------------
% 0.21/0.55  % (14486)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (14464)Refutation not found, incomplete strategy% (14464)------------------------------
% 0.21/0.55  % (14464)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (14464)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.56  % (14464)Memory used [KB]: 6268
% 0.21/0.56  % (14464)Time elapsed: 0.138 s
% 0.21/0.56  % (14464)------------------------------
% 0.21/0.56  % (14464)------------------------------
% 0.21/0.56  % (14476)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.56  % (14485)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.56  % (14478)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.56  % (14477)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.56  % (14460)Refutation not found, incomplete strategy% (14460)------------------------------
% 0.21/0.56  % (14460)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (14460)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (14460)Memory used [KB]: 1663
% 0.21/0.56  % (14460)Time elapsed: 0.141 s
% 0.21/0.56  % (14460)------------------------------
% 0.21/0.56  % (14460)------------------------------
% 1.52/0.56  % (14462)Refutation not found, incomplete strategy% (14462)------------------------------
% 1.52/0.56  % (14462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.56  % (14462)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.56  
% 1.52/0.56  % (14462)Memory used [KB]: 10746
% 1.52/0.56  % (14462)Time elapsed: 0.142 s
% 1.52/0.56  % (14462)------------------------------
% 1.52/0.56  % (14462)------------------------------
% 1.52/0.56  % (14473)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.52/0.56  % (14468)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.52/0.56  % (14483)Refutation not found, incomplete strategy% (14483)------------------------------
% 1.52/0.56  % (14483)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.56  % (14483)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.56  
% 1.52/0.57  % (14483)Memory used [KB]: 1791
% 1.52/0.57  % (14483)Time elapsed: 0.151 s
% 1.52/0.57  % (14483)------------------------------
% 1.52/0.57  % (14483)------------------------------
% 1.52/0.57  % (14475)Refutation not found, incomplete strategy% (14475)------------------------------
% 1.52/0.57  % (14475)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.57  % (14475)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.57  
% 1.52/0.57  % (14475)Memory used [KB]: 6268
% 1.52/0.57  % (14475)Time elapsed: 0.137 s
% 1.52/0.57  % (14475)------------------------------
% 1.52/0.57  % (14475)------------------------------
% 1.52/0.57  % (14463)Refutation found. Thanks to Tanya!
% 1.52/0.57  % SZS status Theorem for theBenchmark
% 1.52/0.57  % SZS output start Proof for theBenchmark
% 1.52/0.57  fof(f229,plain,(
% 1.52/0.57    $false),
% 1.52/0.57    inference(avatar_sat_refutation,[],[f140,f144,f148,f152,f228])).
% 1.52/0.57  fof(f228,plain,(
% 1.52/0.57    ~spl5_1),
% 1.52/0.57    inference(avatar_contradiction_clause,[],[f227])).
% 1.52/0.57  fof(f227,plain,(
% 1.52/0.57    $false | ~spl5_1),
% 1.52/0.57    inference(subsumption_resolution,[],[f218,f191])).
% 1.52/0.57  fof(f191,plain,(
% 1.52/0.57    ~v1_xboole_0(o_0_0_xboole_0) | ~spl5_1),
% 1.52/0.57    inference(subsumption_resolution,[],[f190,f59])).
% 1.52/0.57  fof(f59,plain,(
% 1.52/0.57    o_0_0_xboole_0 != sK0),
% 1.52/0.57    inference(definition_unfolding,[],[f35,f39])).
% 1.52/0.57  fof(f39,plain,(
% 1.52/0.57    k1_xboole_0 = o_0_0_xboole_0),
% 1.52/0.57    inference(cnf_transformation,[],[f1])).
% 1.52/0.57  fof(f1,axiom,(
% 1.52/0.57    k1_xboole_0 = o_0_0_xboole_0),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).
% 1.52/0.57  fof(f35,plain,(
% 1.52/0.57    k1_xboole_0 != sK0),
% 1.52/0.57    inference(cnf_transformation,[],[f32])).
% 1.52/0.57  fof(f32,plain,(
% 1.52/0.57    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 1.52/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f18,f31])).
% 1.52/0.57  fof(f31,plain,(
% 1.52/0.57    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)))),
% 1.52/0.57    introduced(choice_axiom,[])).
% 1.52/0.57  fof(f18,plain,(
% 1.52/0.57    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 1.52/0.57    inference(flattening,[],[f17])).
% 1.52/0.57  fof(f17,plain,(
% 1.52/0.57    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 1.52/0.57    inference(ennf_transformation,[],[f16])).
% 1.52/0.57  fof(f16,negated_conjecture,(
% 1.52/0.57    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.52/0.57    inference(negated_conjecture,[],[f15])).
% 1.52/0.57  fof(f15,conjecture,(
% 1.52/0.57    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).
% 1.52/0.57  fof(f190,plain,(
% 1.52/0.57    ~v1_xboole_0(o_0_0_xboole_0) | o_0_0_xboole_0 = sK0 | ~spl5_1),
% 1.52/0.57    inference(subsumption_resolution,[],[f181,f58])).
% 1.52/0.57  fof(f58,plain,(
% 1.52/0.57    o_0_0_xboole_0 != sK1),
% 1.52/0.57    inference(definition_unfolding,[],[f36,f39])).
% 1.52/0.57  fof(f36,plain,(
% 1.52/0.57    k1_xboole_0 != sK1),
% 1.52/0.57    inference(cnf_transformation,[],[f32])).
% 1.52/0.57  fof(f181,plain,(
% 1.52/0.57    ~v1_xboole_0(o_0_0_xboole_0) | o_0_0_xboole_0 = sK1 | o_0_0_xboole_0 = sK0 | ~spl5_1),
% 1.52/0.57    inference(superposition,[],[f80,f175])).
% 1.52/0.57  fof(f175,plain,(
% 1.52/0.57    o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl5_1),
% 1.52/0.57    inference(subsumption_resolution,[],[f154,f57])).
% 1.52/0.57  fof(f57,plain,(
% 1.52/0.57    o_0_0_xboole_0 != sK2),
% 1.52/0.57    inference(definition_unfolding,[],[f37,f39])).
% 1.52/0.57  fof(f37,plain,(
% 1.52/0.57    k1_xboole_0 != sK2),
% 1.52/0.57    inference(cnf_transformation,[],[f32])).
% 1.52/0.57  fof(f154,plain,(
% 1.52/0.57    o_0_0_xboole_0 = sK2 | o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl5_1),
% 1.52/0.57    inference(resolution,[],[f153,f80])).
% 1.52/0.57  fof(f153,plain,(
% 1.52/0.57    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl5_1),
% 1.52/0.57    inference(resolution,[],[f130,f61])).
% 1.52/0.57  fof(f61,plain,(
% 1.52/0.57    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.52/0.57    inference(definition_unfolding,[],[f33,f48])).
% 1.52/0.57  fof(f48,plain,(
% 1.52/0.57    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f8])).
% 1.52/0.57  fof(f8,axiom,(
% 1.52/0.57    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.52/0.57  fof(f33,plain,(
% 1.52/0.57    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 1.52/0.57    inference(cnf_transformation,[],[f32])).
% 1.52/0.57  fof(f130,plain,(
% 1.52/0.57    ( ! [X6,X8,X7] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X6,X7),X8)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X6,X7),X8))) ) | ~spl5_1),
% 1.52/0.57    inference(avatar_component_clause,[],[f129])).
% 1.52/0.57  fof(f129,plain,(
% 1.52/0.57    spl5_1 <=> ! [X7,X8,X6] : (v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X6,X7),X8)) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X6,X7),X8)))),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.52/0.57  fof(f80,plain,(
% 1.52/0.57    ( ! [X0,X1] : (~v1_xboole_0(k2_zfmisc_1(X0,X1)) | o_0_0_xboole_0 = X1 | o_0_0_xboole_0 = X0) )),
% 1.52/0.57    inference(subsumption_resolution,[],[f79,f62])).
% 1.52/0.57  fof(f62,plain,(
% 1.52/0.57    ( ! [X0] : (~v1_xboole_0(X0) | o_0_0_xboole_0 = X0) )),
% 1.52/0.57    inference(definition_unfolding,[],[f40,f39])).
% 1.52/0.57  fof(f40,plain,(
% 1.52/0.57    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f19])).
% 1.52/0.57  fof(f19,plain,(
% 1.52/0.57    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.52/0.57    inference(ennf_transformation,[],[f2])).
% 1.52/0.57  fof(f2,axiom,(
% 1.52/0.57    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.52/0.57  fof(f79,plain,(
% 1.52/0.57    ( ! [X0,X1] : (v1_xboole_0(X0) | ~v1_xboole_0(k2_zfmisc_1(X0,X1)) | o_0_0_xboole_0 = X1 | o_0_0_xboole_0 = X0) )),
% 1.52/0.57    inference(superposition,[],[f41,f64])).
% 1.52/0.57  fof(f64,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 | o_0_0_xboole_0 = X1 | o_0_0_xboole_0 = X0) )),
% 1.52/0.57    inference(definition_unfolding,[],[f45,f39,f39])).
% 1.52/0.57  fof(f45,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.52/0.57    inference(cnf_transformation,[],[f25])).
% 1.52/0.57  fof(f25,plain,(
% 1.52/0.57    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.52/0.57    inference(ennf_transformation,[],[f6])).
% 1.52/0.57  fof(f6,axiom,(
% 1.52/0.57    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).
% 1.52/0.57  fof(f41,plain,(
% 1.52/0.57    ( ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f20])).
% 1.52/0.57  fof(f20,plain,(
% 1.52/0.57    ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 1.52/0.57    inference(ennf_transformation,[],[f4])).
% 1.52/0.57  fof(f4,axiom,(
% 1.52/0.57    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k1_relat_1(X0)))),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).
% 1.52/0.57  fof(f218,plain,(
% 1.52/0.57    v1_xboole_0(o_0_0_xboole_0) | ~spl5_1),
% 1.52/0.57    inference(backward_demodulation,[],[f176,f196])).
% 1.52/0.57  fof(f196,plain,(
% 1.52/0.57    o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,sK2) | ~spl5_1),
% 1.52/0.57    inference(resolution,[],[f176,f62])).
% 1.52/0.57  fof(f176,plain,(
% 1.52/0.57    v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,sK2)) | ~spl5_1),
% 1.52/0.57    inference(backward_demodulation,[],[f153,f175])).
% 1.52/0.57  fof(f152,plain,(
% 1.52/0.57    ~spl5_4),
% 1.52/0.57    inference(avatar_contradiction_clause,[],[f151])).
% 1.52/0.57  fof(f151,plain,(
% 1.52/0.57    $false | ~spl5_4),
% 1.52/0.57    inference(subsumption_resolution,[],[f150,f57])).
% 1.52/0.57  fof(f150,plain,(
% 1.52/0.57    o_0_0_xboole_0 = sK2 | ~spl5_4),
% 1.52/0.57    inference(subsumption_resolution,[],[f149,f59])).
% 1.52/0.57  fof(f149,plain,(
% 1.52/0.57    o_0_0_xboole_0 = sK0 | o_0_0_xboole_0 = sK2 | ~spl5_4),
% 1.52/0.57    inference(resolution,[],[f139,f61])).
% 1.52/0.57  fof(f139,plain,(
% 1.52/0.57    ( ! [X0,X1] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1)) | o_0_0_xboole_0 = X0 | o_0_0_xboole_0 = X1) ) | ~spl5_4),
% 1.52/0.57    inference(avatar_component_clause,[],[f138])).
% 1.52/0.57  fof(f138,plain,(
% 1.52/0.57    spl5_4 <=> ! [X1,X0] : (o_0_0_xboole_0 = X0 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1)) | o_0_0_xboole_0 = X1)),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.52/0.57  fof(f148,plain,(
% 1.52/0.57    ~spl5_3),
% 1.52/0.57    inference(avatar_contradiction_clause,[],[f147])).
% 1.52/0.57  fof(f147,plain,(
% 1.52/0.57    $false | ~spl5_3),
% 1.52/0.57    inference(subsumption_resolution,[],[f146,f57])).
% 1.52/0.57  fof(f146,plain,(
% 1.52/0.57    o_0_0_xboole_0 = sK2 | ~spl5_3),
% 1.52/0.57    inference(subsumption_resolution,[],[f145,f58])).
% 1.52/0.57  fof(f145,plain,(
% 1.52/0.57    o_0_0_xboole_0 = sK1 | o_0_0_xboole_0 = sK2 | ~spl5_3),
% 1.52/0.57    inference(resolution,[],[f136,f61])).
% 1.52/0.57  fof(f136,plain,(
% 1.52/0.57    ( ! [X2,X3] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X2),X3)) | o_0_0_xboole_0 = X2 | o_0_0_xboole_0 = X3) ) | ~spl5_3),
% 1.52/0.57    inference(avatar_component_clause,[],[f135])).
% 1.52/0.57  fof(f135,plain,(
% 1.52/0.57    spl5_3 <=> ! [X3,X2] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X2),X3)) | o_0_0_xboole_0 = X2 | o_0_0_xboole_0 = X3)),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.52/0.57  fof(f144,plain,(
% 1.52/0.57    ~spl5_2),
% 1.52/0.57    inference(avatar_contradiction_clause,[],[f143])).
% 1.52/0.57  fof(f143,plain,(
% 1.52/0.57    $false | ~spl5_2),
% 1.52/0.57    inference(subsumption_resolution,[],[f142,f58])).
% 1.52/0.57  fof(f142,plain,(
% 1.52/0.57    o_0_0_xboole_0 = sK1 | ~spl5_2),
% 1.52/0.57    inference(subsumption_resolution,[],[f141,f59])).
% 1.52/0.57  fof(f141,plain,(
% 1.52/0.57    o_0_0_xboole_0 = sK0 | o_0_0_xboole_0 = sK1 | ~spl5_2),
% 1.52/0.57    inference(resolution,[],[f133,f61])).
% 1.52/0.57  fof(f133,plain,(
% 1.52/0.57    ( ! [X4,X5] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X4,X5),sK2)) | o_0_0_xboole_0 = X4 | o_0_0_xboole_0 = X5) ) | ~spl5_2),
% 1.52/0.57    inference(avatar_component_clause,[],[f132])).
% 1.52/0.57  % (14479)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.52/0.57  fof(f132,plain,(
% 1.52/0.57    spl5_2 <=> ! [X5,X4] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X4,X5),sK2)) | o_0_0_xboole_0 = X4 | o_0_0_xboole_0 = X5)),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.52/0.57  fof(f140,plain,(
% 1.52/0.57    spl5_1 | spl5_2 | spl5_3 | spl5_4),
% 1.52/0.57    inference(avatar_split_clause,[],[f127,f138,f135,f132,f129])).
% 1.52/0.57  fof(f127,plain,(
% 1.52/0.57    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (o_0_0_xboole_0 = X0 | o_0_0_xboole_0 = X1 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X2),X3)) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1)) | o_0_0_xboole_0 = X3 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X4,X5),sK2)) | o_0_0_xboole_0 = X5 | o_0_0_xboole_0 = X4 | o_0_0_xboole_0 = X2 | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X6,X7),X8)) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X6,X7),X8))) )),
% 1.52/0.57    inference(subsumption_resolution,[],[f126,f100])).
% 1.52/0.57  fof(f100,plain,(
% 1.52/0.57    sK3 != k2_mcart_1(sK4)),
% 1.52/0.57    inference(subsumption_resolution,[],[f99,f59])).
% 1.52/0.57  fof(f99,plain,(
% 1.52/0.57    sK3 != k2_mcart_1(sK4) | o_0_0_xboole_0 = sK0),
% 1.52/0.57    inference(subsumption_resolution,[],[f98,f58])).
% 1.52/0.57  fof(f98,plain,(
% 1.52/0.57    sK3 != k2_mcart_1(sK4) | o_0_0_xboole_0 = sK1 | o_0_0_xboole_0 = sK0),
% 1.52/0.57    inference(subsumption_resolution,[],[f97,f57])).
% 1.52/0.57  fof(f97,plain,(
% 1.52/0.57    sK3 != k2_mcart_1(sK4) | o_0_0_xboole_0 = sK2 | o_0_0_xboole_0 = sK1 | o_0_0_xboole_0 = sK0),
% 1.52/0.57    inference(subsumption_resolution,[],[f94,f61])).
% 1.52/0.57  fof(f94,plain,(
% 1.52/0.57    sK3 != k2_mcart_1(sK4) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | o_0_0_xboole_0 = sK2 | o_0_0_xboole_0 = sK1 | o_0_0_xboole_0 = sK0),
% 1.52/0.57    inference(superposition,[],[f38,f65])).
% 1.52/0.57  fof(f65,plain,(
% 1.52/0.57    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | o_0_0_xboole_0 = X2 | o_0_0_xboole_0 = X1 | o_0_0_xboole_0 = X0) )),
% 1.52/0.57    inference(definition_unfolding,[],[f53,f48,f39,f39,f39])).
% 1.52/0.57  fof(f53,plain,(
% 1.52/0.57    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.52/0.57    inference(cnf_transformation,[],[f27])).
% 1.52/0.57  fof(f27,plain,(
% 1.52/0.57    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.52/0.57    inference(ennf_transformation,[],[f14])).
% 1.52/0.57  fof(f14,axiom,(
% 1.52/0.57    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).
% 1.52/0.57  fof(f38,plain,(
% 1.52/0.57    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)),
% 1.52/0.57    inference(cnf_transformation,[],[f32])).
% 1.52/0.57  fof(f126,plain,(
% 1.52/0.57    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (o_0_0_xboole_0 = X0 | sK3 = k2_mcart_1(sK4) | o_0_0_xboole_0 = X1 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X2),X3)) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1)) | o_0_0_xboole_0 = X3 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X4,X5),sK2)) | o_0_0_xboole_0 = X5 | o_0_0_xboole_0 = X4 | o_0_0_xboole_0 = X2 | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X6,X7),X8)) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X6,X7),X8))) )),
% 1.52/0.57    inference(equality_resolution,[],[f123])).
% 1.52/0.57  fof(f123,plain,(
% 1.52/0.57    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sK4 != X2 | o_0_0_xboole_0 = X1 | sK3 = k2_mcart_1(X2) | o_0_0_xboole_0 = X0 | ~m1_subset_1(X2,k2_zfmisc_1(k2_zfmisc_1(sK0,X3),X4)) | ~m1_subset_1(X2,k2_zfmisc_1(k2_zfmisc_1(X1,sK1),X0)) | o_0_0_xboole_0 = X4 | ~m1_subset_1(X2,k2_zfmisc_1(k2_zfmisc_1(X5,X6),sK2)) | o_0_0_xboole_0 = X6 | o_0_0_xboole_0 = X5 | o_0_0_xboole_0 = X3 | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X7,X8),X9)) | ~m1_subset_1(X2,k2_zfmisc_1(k2_zfmisc_1(X7,X8),X9))) )),
% 1.52/0.57    inference(resolution,[],[f122,f44])).
% 1.52/0.57  fof(f44,plain,(
% 1.52/0.57    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f24])).
% 1.52/0.57  fof(f24,plain,(
% 1.52/0.57    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.52/0.57    inference(flattening,[],[f23])).
% 1.52/0.57  fof(f23,plain,(
% 1.52/0.57    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.52/0.57    inference(ennf_transformation,[],[f3])).
% 1.52/0.57  fof(f3,axiom,(
% 1.52/0.57    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.52/0.57  fof(f122,plain,(
% 1.52/0.57    ( ! [X4,X2,X0,X10,X8,X7,X3,X1,X11,X9] : (~r2_hidden(X3,k2_zfmisc_1(k2_zfmisc_1(X9,X10),X11)) | o_0_0_xboole_0 = X1 | o_0_0_xboole_0 = X2 | k2_mcart_1(X3) = sK3 | sK4 != X3 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X4)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X2,sK1),X1)) | o_0_0_xboole_0 = X4 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X7,X8),sK2)) | o_0_0_xboole_0 = X8 | o_0_0_xboole_0 = X7 | o_0_0_xboole_0 = X0) )),
% 1.52/0.57    inference(condensation,[],[f120])).
% 1.52/0.57  fof(f120,plain,(
% 1.52/0.57    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X11,X9] : (o_0_0_xboole_0 = X0 | o_0_0_xboole_0 = X1 | o_0_0_xboole_0 = X2 | k2_mcart_1(X3) = sK3 | sK4 != X3 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X4)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X2,sK1),X1)) | o_0_0_xboole_0 = X4 | ~r2_hidden(X3,k2_zfmisc_1(X5,X6)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X7,X8),sK2)) | o_0_0_xboole_0 = X8 | o_0_0_xboole_0 = X7 | ~r2_hidden(X3,k2_zfmisc_1(k2_zfmisc_1(X9,X10),X11))) )),
% 1.52/0.57    inference(resolution,[],[f118,f49])).
% 1.52/0.57  fof(f49,plain,(
% 1.52/0.57    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 1.52/0.57    inference(cnf_transformation,[],[f26])).
% 1.52/0.57  fof(f26,plain,(
% 1.52/0.57    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.52/0.57    inference(ennf_transformation,[],[f12])).
% 1.52/0.57  fof(f12,axiom,(
% 1.52/0.57    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.52/0.57  fof(f118,plain,(
% 1.52/0.57    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] : (~r2_hidden(k1_mcart_1(X4),k2_zfmisc_1(X5,X6)) | o_0_0_xboole_0 = X1 | o_0_0_xboole_0 = X2 | o_0_0_xboole_0 = X3 | sK3 = k2_mcart_1(X4) | sK4 != X4 | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(sK0,X1),X0)) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X3,sK1),X2)) | o_0_0_xboole_0 = X0 | ~r2_hidden(X4,k2_zfmisc_1(X7,X8)) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X9,X10),sK2)) | o_0_0_xboole_0 = X10 | o_0_0_xboole_0 = X9) )),
% 1.52/0.57    inference(subsumption_resolution,[],[f116,f57])).
% 1.52/0.57  fof(f116,plain,(
% 1.52/0.57    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] : (o_0_0_xboole_0 = X0 | o_0_0_xboole_0 = X1 | o_0_0_xboole_0 = X2 | o_0_0_xboole_0 = X3 | sK3 = k2_mcart_1(X4) | sK4 != X4 | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(sK0,X1),X0)) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X3,sK1),X2)) | ~r2_hidden(k1_mcart_1(X4),k2_zfmisc_1(X5,X6)) | ~r2_hidden(X4,k2_zfmisc_1(X7,X8)) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X9,X10),sK2)) | o_0_0_xboole_0 = sK2 | o_0_0_xboole_0 = X10 | o_0_0_xboole_0 = X9) )),
% 1.52/0.57    inference(resolution,[],[f114,f96])).
% 1.52/0.57  fof(f96,plain,(
% 1.52/0.57    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_mcart_1(X3),X2) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | o_0_0_xboole_0 = X2 | o_0_0_xboole_0 = X1 | o_0_0_xboole_0 = X0) )),
% 1.52/0.57    inference(duplicate_literal_removal,[],[f95])).
% 1.52/0.57  fof(f95,plain,(
% 1.52/0.57    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_mcart_1(X3),X2) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | o_0_0_xboole_0 = X2 | o_0_0_xboole_0 = X1 | o_0_0_xboole_0 = X0) )),
% 1.52/0.57    inference(superposition,[],[f70,f65])).
% 1.52/0.57  % (14467)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.52/0.57  fof(f70,plain,(
% 1.52/0.57    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 1.52/0.57    inference(definition_unfolding,[],[f56,f48])).
% 1.52/0.57  fof(f56,plain,(
% 1.52/0.57    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 1.52/0.57    inference(cnf_transformation,[],[f30])).
% 1.52/0.57  fof(f30,plain,(
% 1.52/0.57    ! [X0,X1,X2,X3] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 1.52/0.57    inference(ennf_transformation,[],[f11])).
% 1.52/0.57  fof(f11,axiom,(
% 1.52/0.57    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2))),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_mcart_1)).
% 1.52/0.57  fof(f114,plain,(
% 1.52/0.57    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(k2_mcart_1(X0),sK2) | o_0_0_xboole_0 = X1 | o_0_0_xboole_0 = X2 | o_0_0_xboole_0 = X3 | o_0_0_xboole_0 = X4 | k2_mcart_1(X0) = sK3 | sK4 != X0 | ~m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,X2),X1)) | ~m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X4,sK1),X3)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X5,X6)) | ~r2_hidden(X0,k2_zfmisc_1(X7,X8))) )),
% 1.52/0.57    inference(superposition,[],[f112,f78])).
% 1.52/0.57  fof(f78,plain,(
% 1.52/0.57    ( ! [X2,X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 1.52/0.57    inference(resolution,[],[f43,f42])).
% 1.52/0.57  fof(f42,plain,(
% 1.52/0.57    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.52/0.57    inference(cnf_transformation,[],[f5])).
% 1.52/0.57  fof(f5,axiom,(
% 1.52/0.57    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.52/0.57  fof(f43,plain,(
% 1.52/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r2_hidden(X0,X1) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0) )),
% 1.52/0.57    inference(cnf_transformation,[],[f22])).
% 1.52/0.57  fof(f22,plain,(
% 1.52/0.57    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 1.52/0.57    inference(flattening,[],[f21])).
% 1.52/0.57  fof(f21,plain,(
% 1.52/0.57    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 1.52/0.57    inference(ennf_transformation,[],[f13])).
% 1.52/0.57  fof(f13,axiom,(
% 1.52/0.57    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).
% 1.52/0.57  fof(f112,plain,(
% 1.52/0.57    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sK4 != k4_tarski(k1_mcart_1(X0),X5) | o_0_0_xboole_0 = X2 | o_0_0_xboole_0 = X1 | o_0_0_xboole_0 = X3 | o_0_0_xboole_0 = X4 | sK3 = X5 | ~m1_subset_1(X5,sK2) | ~m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,X1),X2)) | ~m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X4,sK1),X3)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X6,X7))) )),
% 1.52/0.57    inference(subsumption_resolution,[],[f110,f59])).
% 1.52/0.57  fof(f110,plain,(
% 1.52/0.57    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (~m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,X1),X2)) | o_0_0_xboole_0 = X2 | o_0_0_xboole_0 = X1 | o_0_0_xboole_0 = sK0 | o_0_0_xboole_0 = X3 | o_0_0_xboole_0 = X4 | sK3 = X5 | ~m1_subset_1(X5,sK2) | sK4 != k4_tarski(k1_mcart_1(X0),X5) | ~m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X4,sK1),X3)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X6,X7))) )),
% 1.52/0.57    inference(resolution,[],[f109,f107])).
% 1.52/0.57  fof(f107,plain,(
% 1.52/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k1_mcart_1(k1_mcart_1(X0)),sK0) | o_0_0_xboole_0 = X2 | o_0_0_xboole_0 = X1 | sK3 = X3 | ~m1_subset_1(X3,sK2) | sK4 != k4_tarski(k1_mcart_1(X0),X3) | ~m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,sK1),X2)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X4,X5))) )),
% 1.52/0.57    inference(subsumption_resolution,[],[f106,f58])).
% 1.52/0.57  fof(f106,plain,(
% 1.52/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,sK1),X2)) | o_0_0_xboole_0 = X2 | o_0_0_xboole_0 = sK1 | o_0_0_xboole_0 = X1 | sK3 = X3 | ~m1_subset_1(X3,sK2) | sK4 != k4_tarski(k1_mcart_1(X0),X3) | ~m1_subset_1(k1_mcart_1(k1_mcart_1(X0)),sK0) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X4,X5))) )),
% 1.52/0.57    inference(resolution,[],[f105,f81])).
% 1.52/0.57  fof(f81,plain,(
% 1.52/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(k2_mcart_1(X0),sK1) | sK3 = X1 | ~m1_subset_1(X1,sK2) | k4_tarski(X0,X1) != sK4 | ~m1_subset_1(k1_mcart_1(X0),sK0) | ~r2_hidden(X0,k2_zfmisc_1(X2,X3))) )),
% 1.52/0.57    inference(superposition,[],[f60,f78])).
% 1.52/0.57  fof(f60,plain,(
% 1.52/0.57    ( ! [X6,X7,X5] : (sK4 != k4_tarski(k4_tarski(X5,X6),X7) | sK3 = X7 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 1.52/0.57    inference(definition_unfolding,[],[f34,f47])).
% 1.52/0.57  fof(f47,plain,(
% 1.52/0.57    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f7])).
% 1.52/0.57  fof(f7,axiom,(
% 1.52/0.57    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 1.52/0.57  fof(f34,plain,(
% 1.52/0.57    ( ! [X6,X7,X5] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f32])).
% 1.52/0.57  fof(f105,plain,(
% 1.52/0.57    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_mcart_1(k1_mcart_1(X3)),X1) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | o_0_0_xboole_0 = X2 | o_0_0_xboole_0 = X1 | o_0_0_xboole_0 = X0) )),
% 1.52/0.57    inference(duplicate_literal_removal,[],[f104])).
% 1.52/0.57  fof(f104,plain,(
% 1.52/0.57    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_mcart_1(k1_mcart_1(X3)),X1) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | o_0_0_xboole_0 = X2 | o_0_0_xboole_0 = X1 | o_0_0_xboole_0 = X0) )),
% 1.52/0.57    inference(superposition,[],[f69,f66])).
% 1.52/0.57  fof(f66,plain,(
% 1.52/0.57    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | o_0_0_xboole_0 = X2 | o_0_0_xboole_0 = X1 | o_0_0_xboole_0 = X0) )),
% 1.52/0.57    inference(definition_unfolding,[],[f52,f48,f39,f39,f39])).
% 1.52/0.57  fof(f52,plain,(
% 1.52/0.57    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.52/0.57    inference(cnf_transformation,[],[f27])).
% 1.52/0.57  fof(f69,plain,(
% 1.52/0.57    ( ! [X2,X0,X3,X1] : (m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 1.52/0.57    inference(definition_unfolding,[],[f55,f48])).
% 1.52/0.57  fof(f55,plain,(
% 1.52/0.57    ( ! [X2,X0,X3,X1] : (m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 1.52/0.57    inference(cnf_transformation,[],[f29])).
% 1.52/0.57  fof(f29,plain,(
% 1.52/0.57    ! [X0,X1,X2,X3] : (m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 1.52/0.57    inference(ennf_transformation,[],[f10])).
% 1.52/0.57  fof(f10,axiom,(
% 1.52/0.57    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1))),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_mcart_1)).
% 1.52/0.57  fof(f109,plain,(
% 1.52/0.57    ( ! [X2,X0,X3,X1] : (m1_subset_1(k1_mcart_1(k1_mcart_1(X3)),X0) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | o_0_0_xboole_0 = X2 | o_0_0_xboole_0 = X1 | o_0_0_xboole_0 = X0) )),
% 1.52/0.57    inference(duplicate_literal_removal,[],[f108])).
% 1.52/0.57  fof(f108,plain,(
% 1.52/0.57    ( ! [X2,X0,X3,X1] : (m1_subset_1(k1_mcart_1(k1_mcart_1(X3)),X0) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | o_0_0_xboole_0 = X2 | o_0_0_xboole_0 = X1 | o_0_0_xboole_0 = X0) )),
% 1.52/0.57    inference(superposition,[],[f68,f67])).
% 1.52/0.57  fof(f67,plain,(
% 1.52/0.57    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | o_0_0_xboole_0 = X2 | o_0_0_xboole_0 = X1 | o_0_0_xboole_0 = X0) )),
% 1.52/0.57    inference(definition_unfolding,[],[f51,f48,f39,f39,f39])).
% 1.52/0.57  fof(f51,plain,(
% 1.52/0.57    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.52/0.57    inference(cnf_transformation,[],[f27])).
% 1.52/0.57  fof(f68,plain,(
% 1.52/0.57    ( ! [X2,X0,X3,X1] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 1.52/0.57    inference(definition_unfolding,[],[f54,f48])).
% 1.52/0.57  fof(f54,plain,(
% 1.52/0.57    ( ! [X2,X0,X3,X1] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 1.52/0.57    inference(cnf_transformation,[],[f28])).
% 1.52/0.57  fof(f28,plain,(
% 1.52/0.57    ! [X0,X1,X2,X3] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 1.52/0.57    inference(ennf_transformation,[],[f9])).
% 1.52/0.57  fof(f9,axiom,(
% 1.52/0.57    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0))),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_mcart_1)).
% 1.52/0.57  % SZS output end Proof for theBenchmark
% 1.52/0.57  % (14463)------------------------------
% 1.52/0.57  % (14463)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.57  % (14463)Termination reason: Refutation
% 1.52/0.57  
% 1.52/0.57  % (14463)Memory used [KB]: 10874
% 1.52/0.57  % (14463)Time elapsed: 0.119 s
% 1.52/0.57  % (14463)------------------------------
% 1.52/0.57  % (14463)------------------------------
% 1.52/0.57  % (14456)Success in time 0.2 s
%------------------------------------------------------------------------------
