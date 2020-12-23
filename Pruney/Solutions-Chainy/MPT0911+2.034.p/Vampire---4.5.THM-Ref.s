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
% DateTime   : Thu Dec  3 12:59:34 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 222 expanded)
%              Number of leaves         :   16 (  60 expanded)
%              Depth                    :   12
%              Number of atoms          :  237 ( 830 expanded)
%              Number of equality atoms :   96 ( 383 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f305,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f95,f140,f207,f238,f304])).

fof(f304,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f299])).

fof(f299,plain,
    ( $false
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f44,f90,f292,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,X1)
      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f292,plain,
    ( sK4 != k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))
    | ~ spl5_1 ),
    inference(forward_demodulation,[],[f289,f278])).

fof(f278,plain,
    ( k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f44,f264,f42])).

fof(f264,plain,
    ( r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f90,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f289,plain,
    ( sK4 != k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))),k2_mcart_1(sK4))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f283,f86,f272,f285,f48])).

fof(f48,plain,(
    ! [X6,X7,X5] :
      ( sK4 != k4_tarski(k4_tarski(X5,X6),X7)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X5,sK0)
      | sK3 = X7 ) ),
    inference(definition_unfolding,[],[f26,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

% (19102)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f7,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f26,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X5,sK0)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X7,sK2)
      | k3_mcart_1(X5,X6,X7) != sK4
      | sK3 = X7 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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

fof(f285,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f277,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f277,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f264,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f272,plain,
    ( m1_subset_1(k2_mcart_1(sK4),sK2)
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f265,f37])).

fof(f265,plain,
    ( r2_hidden(k2_mcart_1(sK4),sK2)
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f90,f41])).

fof(f86,plain,(
    sK3 != k2_mcart_1(sK4) ),
    inference(superposition,[],[f31,f81])).

fof(f81,plain,(
    k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) ),
    inference(unit_resulting_resolution,[],[f29,f28,f30,f47,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) ) ),
    inference(definition_unfolding,[],[f34,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f27,f39])).

fof(f27,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f30,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f15])).

fof(f28,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f15])).

fof(f29,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f15])).

fof(f31,plain,(
    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f15])).

fof(f283,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f276,f37])).

fof(f276,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0)
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f264,f40])).

fof(f90,plain,
    ( r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl5_1
  <=> r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f44,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f238,plain,(
    ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f234])).

fof(f234,plain,
    ( $false
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f30,f139])).

fof(f139,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl5_4
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f207,plain,
    ( ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f100,f149])).

fof(f149,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(backward_demodulation,[],[f57,f146])).

fof(f146,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f142,f110])).

fof(f110,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f102,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f102,plain,
    ( v1_xboole_0(k2_relat_1(k1_xboole_0))
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f96,f97])).

fof(f97,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f94,f35])).

fof(f94,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl5_2
  <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f96,plain,
    ( v1_xboole_0(k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f94,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_relat_1)).

fof(f142,plain,
    ( sK1 = k2_relat_1(k1_xboole_0)
    | ~ spl5_3 ),
    inference(backward_demodulation,[],[f64,f135])).

fof(f135,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl5_3
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f64,plain,(
    sK1 = k2_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f28,f29,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

fof(f57,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(unit_resulting_resolution,[],[f29,f35])).

fof(f100,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f94,f97])).

fof(f140,plain,
    ( spl5_3
    | spl5_4
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f130,f92,f137,f133])).

fof(f130,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl5_2 ),
    inference(duplicate_literal_removal,[],[f129])).

fof(f129,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f125,f110])).

fof(f125,plain,
    ( sK2 = k2_relat_1(k1_xboole_0)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl5_2 ),
    inference(superposition,[],[f46,f97])).

fof(f95,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f85,f92,f88])).

fof(f85,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f47,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:58:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (19075)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (19076)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (19093)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.52  % (19077)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (19091)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.52  % (19074)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (19087)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (19096)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (19101)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (19088)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (19089)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.53  % (19096)Refutation not found, incomplete strategy% (19096)------------------------------
% 0.20/0.53  % (19096)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (19096)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (19096)Memory used [KB]: 1663
% 0.20/0.53  % (19096)Time elapsed: 0.083 s
% 0.20/0.53  % (19096)------------------------------
% 0.20/0.53  % (19096)------------------------------
% 0.20/0.53  % (19088)Refutation not found, incomplete strategy% (19088)------------------------------
% 0.20/0.53  % (19088)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (19088)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (19088)Memory used [KB]: 6140
% 0.20/0.53  % (19088)Time elapsed: 0.084 s
% 0.20/0.53  % (19088)------------------------------
% 0.20/0.53  % (19088)------------------------------
% 0.20/0.53  % (19078)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (19080)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.53  % (19100)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (19099)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.53  % (19098)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (19073)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.54  % (19073)Refutation not found, incomplete strategy% (19073)------------------------------
% 0.20/0.54  % (19073)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (19073)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (19073)Memory used [KB]: 1663
% 0.20/0.54  % (19073)Time elapsed: 0.123 s
% 0.20/0.54  % (19073)------------------------------
% 0.20/0.54  % (19073)------------------------------
% 0.20/0.54  % (19099)Refutation not found, incomplete strategy% (19099)------------------------------
% 0.20/0.54  % (19099)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (19083)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.54  % (19081)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.54  % (19093)Refutation not found, incomplete strategy% (19093)------------------------------
% 0.20/0.54  % (19093)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (19079)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.54  % (19093)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (19093)Memory used [KB]: 10746
% 0.20/0.54  % (19093)Time elapsed: 0.127 s
% 0.20/0.54  % (19093)------------------------------
% 0.20/0.54  % (19093)------------------------------
% 0.20/0.54  % (19077)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f305,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(avatar_sat_refutation,[],[f95,f140,f207,f238,f304])).
% 0.20/0.54  fof(f304,plain,(
% 0.20/0.54    ~spl5_1),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f299])).
% 0.20/0.54  fof(f299,plain,(
% 0.20/0.54    $false | ~spl5_1),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f44,f90,f292,f42])).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r2_hidden(X0,X1) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f23])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(flattening,[],[f22])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f10])).
% 0.20/0.54  fof(f10,axiom,(
% 0.20/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).
% 0.20/0.54  fof(f292,plain,(
% 0.20/0.54    sK4 != k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) | ~spl5_1),
% 0.20/0.54    inference(forward_demodulation,[],[f289,f278])).
% 0.20/0.54  fof(f278,plain,(
% 0.20/0.54    k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) | ~spl5_1),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f44,f264,f42])).
% 0.20/0.54  fof(f264,plain,(
% 0.20/0.54    r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1)) | ~spl5_1),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f90,f40])).
% 0.20/0.54  fof(f40,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f21])).
% 0.20/0.54  fof(f21,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.54    inference(ennf_transformation,[],[f9])).
% 0.20/0.54  fof(f9,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.20/0.54  fof(f289,plain,(
% 0.20/0.54    sK4 != k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))),k2_mcart_1(sK4)) | ~spl5_1),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f283,f86,f272,f285,f48])).
% 0.20/0.54  fof(f48,plain,(
% 0.20/0.54    ( ! [X6,X7,X5] : (sK4 != k4_tarski(k4_tarski(X5,X6),X7) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X5,sK0) | sK3 = X7) )),
% 0.20/0.54    inference(definition_unfolding,[],[f26,f36])).
% 0.20/0.54  fof(f36,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f7])).
% 0.20/0.54  % (19102)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  fof(f7,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.20/0.54  fof(f26,plain,(
% 0.20/0.54    ( ! [X6,X7,X5] : (~m1_subset_1(X5,sK0) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X7,sK2) | k3_mcart_1(X5,X6,X7) != sK4 | sK3 = X7) )),
% 0.20/0.54    inference(cnf_transformation,[],[f15])).
% 0.20/0.54  fof(f15,plain,(
% 0.20/0.54    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.20/0.54    inference(flattening,[],[f14])).
% 0.20/0.54  fof(f14,plain,(
% 0.20/0.54    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.20/0.54    inference(ennf_transformation,[],[f13])).
% 0.20/0.54  fof(f13,negated_conjecture,(
% 0.20/0.54    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.20/0.54    inference(negated_conjecture,[],[f12])).
% 0.20/0.54  fof(f12,conjecture,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_mcart_1)).
% 0.20/0.54  fof(f285,plain,(
% 0.20/0.54    m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) | ~spl5_1),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f277,f37])).
% 0.20/0.54  fof(f37,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f18])).
% 0.20/0.54  fof(f18,plain,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.20/0.54  fof(f277,plain,(
% 0.20/0.54    r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1) | ~spl5_1),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f264,f41])).
% 0.20/0.54  fof(f41,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f21])).
% 0.20/0.54  fof(f272,plain,(
% 0.20/0.54    m1_subset_1(k2_mcart_1(sK4),sK2) | ~spl5_1),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f265,f37])).
% 0.20/0.54  fof(f265,plain,(
% 0.20/0.54    r2_hidden(k2_mcart_1(sK4),sK2) | ~spl5_1),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f90,f41])).
% 0.20/0.54  fof(f86,plain,(
% 0.20/0.54    sK3 != k2_mcart_1(sK4)),
% 0.20/0.54    inference(superposition,[],[f31,f81])).
% 0.20/0.54  fof(f81,plain,(
% 0.20/0.54    k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f29,f28,f30,f47,f49])).
% 0.20/0.54  fof(f49,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X0 | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f34,f39])).
% 0.20/0.54  fof(f39,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f8])).
% 0.20/0.54  fof(f8,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f16])).
% 0.20/0.54  fof(f16,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.54    inference(ennf_transformation,[],[f11])).
% 0.20/0.54  fof(f11,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).
% 0.20/0.54  fof(f47,plain,(
% 0.20/0.54    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.20/0.54    inference(definition_unfolding,[],[f27,f39])).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.20/0.54    inference(cnf_transformation,[],[f15])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    k1_xboole_0 != sK2),
% 0.20/0.54    inference(cnf_transformation,[],[f15])).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    k1_xboole_0 != sK0),
% 0.20/0.54    inference(cnf_transformation,[],[f15])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    k1_xboole_0 != sK1),
% 0.20/0.54    inference(cnf_transformation,[],[f15])).
% 0.20/0.54  fof(f31,plain,(
% 0.20/0.54    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)),
% 0.20/0.54    inference(cnf_transformation,[],[f15])).
% 0.20/0.54  fof(f283,plain,(
% 0.20/0.54    m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) | ~spl5_1),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f276,f37])).
% 0.20/0.54  fof(f276,plain,(
% 0.20/0.54    r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0) | ~spl5_1),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f264,f40])).
% 0.20/0.54  fof(f90,plain,(
% 0.20/0.54    r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl5_1),
% 0.20/0.54    inference(avatar_component_clause,[],[f88])).
% 0.20/0.54  fof(f88,plain,(
% 0.20/0.54    spl5_1 <=> r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.54  fof(f238,plain,(
% 0.20/0.54    ~spl5_4),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f234])).
% 0.20/0.54  fof(f234,plain,(
% 0.20/0.54    $false | ~spl5_4),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f30,f139])).
% 0.20/0.54  fof(f139,plain,(
% 0.20/0.54    k1_xboole_0 = sK2 | ~spl5_4),
% 0.20/0.54    inference(avatar_component_clause,[],[f137])).
% 0.20/0.54  fof(f137,plain,(
% 0.20/0.54    spl5_4 <=> k1_xboole_0 = sK2),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.54  fof(f207,plain,(
% 0.20/0.54    ~spl5_2 | ~spl5_3),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f203])).
% 0.20/0.54  fof(f203,plain,(
% 0.20/0.54    $false | (~spl5_2 | ~spl5_3)),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f100,f149])).
% 0.20/0.54  fof(f149,plain,(
% 0.20/0.54    ~v1_xboole_0(k1_xboole_0) | (~spl5_2 | ~spl5_3)),
% 0.20/0.54    inference(backward_demodulation,[],[f57,f146])).
% 0.20/0.54  fof(f146,plain,(
% 0.20/0.54    k1_xboole_0 = sK1 | (~spl5_2 | ~spl5_3)),
% 0.20/0.54    inference(forward_demodulation,[],[f142,f110])).
% 0.20/0.54  fof(f110,plain,(
% 0.20/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl5_2),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f102,f35])).
% 0.20/0.54  fof(f35,plain,(
% 0.20/0.54    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f17])).
% 0.20/0.54  fof(f17,plain,(
% 0.20/0.54    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.54  fof(f102,plain,(
% 0.20/0.54    v1_xboole_0(k2_relat_1(k1_xboole_0)) | ~spl5_2),
% 0.20/0.54    inference(forward_demodulation,[],[f96,f97])).
% 0.20/0.54  fof(f97,plain,(
% 0.20/0.54    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl5_2),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f94,f35])).
% 0.20/0.54  fof(f94,plain,(
% 0.20/0.54    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl5_2),
% 0.20/0.54    inference(avatar_component_clause,[],[f92])).
% 0.20/0.54  fof(f92,plain,(
% 0.20/0.54    spl5_2 <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.54  fof(f96,plain,(
% 0.20/0.54    v1_xboole_0(k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))) | ~spl5_2),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f94,f43])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    ( ! [X0] : (~v1_xboole_0(X0) | v1_xboole_0(k2_relat_1(X0))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f24])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f4])).
% 0.20/0.54  fof(f4,axiom,(
% 0.20/0.54    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k2_relat_1(X0)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_relat_1)).
% 0.20/0.54  fof(f142,plain,(
% 0.20/0.54    sK1 = k2_relat_1(k1_xboole_0) | ~spl5_3),
% 0.20/0.54    inference(backward_demodulation,[],[f64,f135])).
% 0.20/0.54  fof(f135,plain,(
% 0.20/0.54    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl5_3),
% 0.20/0.54    inference(avatar_component_clause,[],[f133])).
% 0.20/0.54  fof(f133,plain,(
% 0.20/0.54    spl5_3 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.54  fof(f64,plain,(
% 0.20/0.54    sK1 = k2_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f28,f29,f46])).
% 0.20/0.54  fof(f46,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f25])).
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.54    inference(ennf_transformation,[],[f6])).
% 0.20/0.54  fof(f6,axiom,(
% 0.20/0.54    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).
% 0.20/0.54  fof(f57,plain,(
% 0.20/0.54    ~v1_xboole_0(sK1)),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f29,f35])).
% 0.20/0.54  fof(f100,plain,(
% 0.20/0.54    v1_xboole_0(k1_xboole_0) | ~spl5_2),
% 0.20/0.54    inference(backward_demodulation,[],[f94,f97])).
% 0.20/0.54  fof(f140,plain,(
% 0.20/0.54    spl5_3 | spl5_4 | ~spl5_2),
% 0.20/0.54    inference(avatar_split_clause,[],[f130,f92,f137,f133])).
% 0.20/0.54  fof(f130,plain,(
% 0.20/0.54    k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl5_2),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f129])).
% 0.20/0.54  fof(f129,plain,(
% 0.20/0.54    k1_xboole_0 = sK2 | k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl5_2),
% 0.20/0.54    inference(forward_demodulation,[],[f125,f110])).
% 0.20/0.54  fof(f125,plain,(
% 0.20/0.54    sK2 = k2_relat_1(k1_xboole_0) | k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl5_2),
% 0.20/0.54    inference(superposition,[],[f46,f97])).
% 0.20/0.54  fof(f95,plain,(
% 0.20/0.54    spl5_1 | spl5_2),
% 0.20/0.54    inference(avatar_split_clause,[],[f85,f92,f88])).
% 0.20/0.54  fof(f85,plain,(
% 0.20/0.54    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.20/0.54    inference(resolution,[],[f47,f38])).
% 0.20/0.54  fof(f38,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f20])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.54    inference(flattening,[],[f19])).
% 0.20/0.54  fof(f19,plain,(
% 0.20/0.54    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f3])).
% 0.20/0.54  fof(f3,axiom,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (19077)------------------------------
% 0.20/0.54  % (19077)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (19077)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (19077)Memory used [KB]: 6396
% 0.20/0.54  % (19077)Time elapsed: 0.108 s
% 0.20/0.54  % (19077)------------------------------
% 0.20/0.54  % (19077)------------------------------
% 0.20/0.54  % (19072)Success in time 0.185 s
%------------------------------------------------------------------------------
