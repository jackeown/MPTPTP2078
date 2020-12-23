%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 260 expanded)
%              Number of leaves         :   31 ( 110 expanded)
%              Depth                    :   10
%              Number of atoms          :  418 ( 780 expanded)
%              Number of equality atoms :   77 ( 156 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f492,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f71,f77,f82,f97,f126,f132,f151,f161,f169,f184,f195,f213,f252,f260,f265,f277,f315,f337,f352,f358,f413,f491])).

fof(f491,plain,
    ( ~ spl6_31
    | spl6_33
    | ~ spl6_34 ),
    inference(avatar_contradiction_clause,[],[f490])).

fof(f490,plain,
    ( $false
    | ~ spl6_31
    | spl6_33
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f489,f357])).

fof(f357,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f355])).

fof(f355,plain,
    ( spl6_34
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f489,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_31
    | spl6_33 ),
    inference(subsumption_resolution,[],[f339,f351])).

fof(f351,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | spl6_33 ),
    inference(avatar_component_clause,[],[f349])).

fof(f349,plain,
    ( spl6_33
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f339,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_31 ),
    inference(resolution,[],[f336,f53])).

fof(f53,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f336,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f334])).

fof(f334,plain,
    ( spl6_31
  <=> v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f413,plain,
    ( ~ spl6_11
    | ~ spl6_20
    | ~ spl6_27 ),
    inference(avatar_contradiction_clause,[],[f412])).

fof(f412,plain,
    ( $false
    | ~ spl6_11
    | ~ spl6_20
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f370,f212])).

fof(f212,plain,
    ( r2_hidden(sK5(sK4,sK2,sK3),sK0)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl6_20
  <=> r2_hidden(sK5(sK4,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f370,plain,
    ( ~ r2_hidden(sK5(sK4,sK2,sK3),sK0)
    | ~ spl6_11
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f267,f131])).

fof(f131,plain,
    ( r2_hidden(sK5(sK4,sK2,sK3),sK2)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f129])).

% (11925)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% (11917)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f129,plain,
    ( spl6_11
  <=> r2_hidden(sK5(sK4,sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f267,plain,
    ( ~ r2_hidden(sK5(sK4,sK2,sK3),sK2)
    | ~ r2_hidden(sK5(sK4,sK2,sK3),sK0)
    | ~ spl6_27 ),
    inference(trivial_inequality_removal,[],[f266])).

fof(f266,plain,
    ( sK4 != sK4
    | ~ r2_hidden(sK5(sK4,sK2,sK3),sK2)
    | ~ r2_hidden(sK5(sK4,sK2,sK3),sK0)
    | ~ spl6_27 ),
    inference(superposition,[],[f26,f264])).

fof(f264,plain,
    ( sK4 = k1_funct_1(sK3,sK5(sK4,sK2,sK3))
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f262])).

fof(f262,plain,
    ( spl6_27
  <=> sK4 = k1_funct_1(sK3,sK5(sK4,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f26,plain,(
    ! [X5] :
      ( sK4 != k1_funct_1(sK3,X5)
      | ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X5,sK0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ~ ( k1_funct_1(X3,X5) = X4
                  & r2_hidden(X5,X2)
                  & r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).

fof(f358,plain,
    ( spl6_34
    | ~ spl6_19
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f324,f274,f192,f355])).

fof(f192,plain,
    ( spl6_19
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f274,plain,
    ( spl6_29
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f324,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_19
    | ~ spl6_29 ),
    inference(superposition,[],[f194,f276])).

fof(f276,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f274])).

fof(f194,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f192])).

fof(f352,plain,
    ( ~ spl6_33
    | spl6_16
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f322,f274,f166,f349])).

fof(f166,plain,
    ( spl6_16
  <=> sK0 = k1_relset_1(sK0,k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f322,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | spl6_16
    | ~ spl6_29 ),
    inference(superposition,[],[f168,f276])).

fof(f168,plain,
    ( sK0 != k1_relset_1(sK0,k1_xboole_0,sK3)
    | spl6_16 ),
    inference(avatar_component_clause,[],[f166])).

fof(f337,plain,
    ( spl6_31
    | ~ spl6_15
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f321,f274,f158,f334])).

fof(f158,plain,
    ( spl6_15
  <=> v1_funct_2(sK3,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f321,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl6_15
    | ~ spl6_29 ),
    inference(superposition,[],[f160,f276])).

fof(f160,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f158])).

fof(f315,plain,
    ( spl6_26
    | ~ spl6_28 ),
    inference(avatar_contradiction_clause,[],[f314])).

fof(f314,plain,
    ( $false
    | spl6_26
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f308,f31])).

fof(f31,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f308,plain,
    ( ~ r1_tarski(k1_xboole_0,k4_tarski(sK5(sK4,sK2,k1_xboole_0),sK4))
    | spl6_26
    | ~ spl6_28 ),
    inference(superposition,[],[f259,f272])).

fof(f272,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f270])).

fof(f270,plain,
    ( spl6_28
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f259,plain,
    ( ~ r1_tarski(sK3,k4_tarski(sK5(sK4,sK2,sK3),sK4))
    | spl6_26 ),
    inference(avatar_component_clause,[],[f257])).

fof(f257,plain,
    ( spl6_26
  <=> r1_tarski(sK3,k4_tarski(sK5(sK4,sK2,sK3),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f277,plain,
    ( spl6_28
    | spl6_29
    | ~ spl6_15
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f268,f192,f158,f274,f270])).

fof(f268,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ spl6_15
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f163,f194])).

fof(f163,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl6_15 ),
    inference(resolution,[],[f160,f55])).

fof(f55,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f265,plain,
    ( spl6_27
    | ~ spl6_1
    | ~ spl6_10
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f253,f249,f118,f60,f262])).

fof(f60,plain,
    ( spl6_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f118,plain,
    ( spl6_10
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f249,plain,
    ( spl6_25
  <=> r2_hidden(k4_tarski(sK5(sK4,sK2,sK3),sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f253,plain,
    ( sK4 = k1_funct_1(sK3,sK5(sK4,sK2,sK3))
    | ~ spl6_1
    | ~ spl6_10
    | ~ spl6_25 ),
    inference(resolution,[],[f251,f133])).

fof(f133,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),sK3)
        | k1_funct_1(sK3,X2) = X3 )
    | ~ spl6_1
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f65,f119])).

fof(f119,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f118])).

fof(f65,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(sK3)
        | k1_funct_1(sK3,X2) = X3
        | ~ r2_hidden(k4_tarski(X2,X3),sK3) )
    | ~ spl6_1 ),
    inference(resolution,[],[f62,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f62,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f251,plain,
    ( r2_hidden(k4_tarski(sK5(sK4,sK2,sK3),sK4),sK3)
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f249])).

fof(f260,plain,
    ( ~ spl6_26
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f255,f249,f257])).

fof(f255,plain,
    ( ~ r1_tarski(sK3,k4_tarski(sK5(sK4,sK2,sK3),sK4))
    | ~ spl6_25 ),
    inference(resolution,[],[f251,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f252,plain,
    ( spl6_25
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f247,f118,f94,f249])).

fof(f94,plain,
    ( spl6_6
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f247,plain,
    ( r2_hidden(k4_tarski(sK5(sK4,sK2,sK3),sK4),sK3)
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f99,f119])).

fof(f99,plain,
    ( r2_hidden(k4_tarski(sK5(sK4,sK2,sK3),sK4),sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl6_6 ),
    inference(resolution,[],[f96,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f96,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f94])).

fof(f213,plain,
    ( spl6_20
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f208,f181,f118,f94,f210])).

fof(f181,plain,
    ( spl6_18
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f208,plain,
    ( r2_hidden(sK5(sK4,sK2,sK3),sK0)
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f142,f183])).

fof(f183,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f181])).

fof(f142,plain,
    ( r2_hidden(sK5(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f98,f119])).

fof(f98,plain,
    ( r2_hidden(sK5(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl6_6 ),
    inference(resolution,[],[f96,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f195,plain,
    ( spl6_19
    | ~ spl6_3
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f186,f148,f74,f192])).

fof(f74,plain,
    ( spl6_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f148,plain,
    ( spl6_14
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f186,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl6_3
    | ~ spl6_14 ),
    inference(superposition,[],[f76,f150])).

fof(f150,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f148])).

fof(f76,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f74])).

fof(f184,plain,
    ( spl6_18
    | ~ spl6_3
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f178,f144,f74,f181])).

fof(f144,plain,
    ( spl6_13
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f178,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl6_3
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f176,f76])).

fof(f176,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_13 ),
    inference(superposition,[],[f146,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f146,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f144])).

fof(f169,plain,
    ( ~ spl6_16
    | spl6_13
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f162,f148,f144,f166])).

fof(f162,plain,
    ( sK0 != k1_relset_1(sK0,k1_xboole_0,sK3)
    | spl6_13
    | ~ spl6_14 ),
    inference(forward_demodulation,[],[f145,f150])).

fof(f145,plain,
    ( sK0 != k1_relset_1(sK0,sK1,sK3)
    | spl6_13 ),
    inference(avatar_component_clause,[],[f144])).

fof(f161,plain,
    ( spl6_15
    | ~ spl6_2
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f156,f148,f68,f158])).

fof(f68,plain,
    ( spl6_2
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f156,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl6_2
    | ~ spl6_14 ),
    inference(superposition,[],[f70,f150])).

fof(f70,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f151,plain,
    ( spl6_13
    | spl6_14
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f141,f74,f68,f148,f144])).

fof(f141,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f72,f76])).

fof(f72,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_2 ),
    inference(resolution,[],[f70,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f132,plain,
    ( spl6_11
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f127,f118,f94,f129])).

fof(f127,plain,
    ( r2_hidden(sK5(sK4,sK2,sK3),sK2)
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f100,f119])).

fof(f100,plain,
    ( r2_hidden(sK5(sK4,sK2,sK3),sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl6_6 ),
    inference(resolution,[],[f96,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK5(X0,X1,X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f126,plain,
    ( ~ spl6_3
    | spl6_10 ),
    inference(avatar_contradiction_clause,[],[f124])).

fof(f124,plain,
    ( $false
    | ~ spl6_3
    | spl6_10 ),
    inference(resolution,[],[f122,f76])).

fof(f122,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl6_10 ),
    inference(resolution,[],[f120,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f120,plain,
    ( ~ v1_relat_1(sK3)
    | spl6_10 ),
    inference(avatar_component_clause,[],[f118])).

fof(f97,plain,
    ( spl6_6
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f92,f79,f74,f94])).

fof(f79,plain,
    ( spl6_4
  <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f92,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f91,f76])).

fof(f91,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_4 ),
    inference(superposition,[],[f81,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f81,plain,
    ( r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f82,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f27,f79])).

fof(f27,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f77,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f30,f74])).

fof(f30,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f15])).

fof(f71,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f29,f68])).

fof(f29,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f63,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f28,f60])).

fof(f28,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:22:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (11910)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.47  % (11921)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (11910)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (11913)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (11920)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f492,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f63,f71,f77,f82,f97,f126,f132,f151,f161,f169,f184,f195,f213,f252,f260,f265,f277,f315,f337,f352,f358,f413,f491])).
% 0.21/0.48  fof(f491,plain,(
% 0.21/0.48    ~spl6_31 | spl6_33 | ~spl6_34),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f490])).
% 0.21/0.48  fof(f490,plain,(
% 0.21/0.48    $false | (~spl6_31 | spl6_33 | ~spl6_34)),
% 0.21/0.48    inference(subsumption_resolution,[],[f489,f357])).
% 0.21/0.48  fof(f357,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl6_34),
% 0.21/0.48    inference(avatar_component_clause,[],[f355])).
% 0.21/0.48  fof(f355,plain,(
% 0.21/0.48    spl6_34 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 0.21/0.48  fof(f489,plain,(
% 0.21/0.48    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl6_31 | spl6_33)),
% 0.21/0.48    inference(subsumption_resolution,[],[f339,f351])).
% 0.21/0.48  fof(f351,plain,(
% 0.21/0.48    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | spl6_33),
% 0.21/0.48    inference(avatar_component_clause,[],[f349])).
% 0.21/0.48  fof(f349,plain,(
% 0.21/0.48    spl6_33 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 0.21/0.48  fof(f339,plain,(
% 0.21/0.48    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl6_31),
% 0.21/0.48    inference(resolution,[],[f336,f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X2,X1] : (~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.21/0.48    inference(equality_resolution,[],[f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(flattening,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.48  fof(f336,plain,(
% 0.21/0.48    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | ~spl6_31),
% 0.21/0.48    inference(avatar_component_clause,[],[f334])).
% 0.21/0.48  fof(f334,plain,(
% 0.21/0.48    spl6_31 <=> v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 0.21/0.48  fof(f413,plain,(
% 0.21/0.48    ~spl6_11 | ~spl6_20 | ~spl6_27),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f412])).
% 0.21/0.48  fof(f412,plain,(
% 0.21/0.48    $false | (~spl6_11 | ~spl6_20 | ~spl6_27)),
% 0.21/0.48    inference(subsumption_resolution,[],[f370,f212])).
% 0.21/0.48  fof(f212,plain,(
% 0.21/0.48    r2_hidden(sK5(sK4,sK2,sK3),sK0) | ~spl6_20),
% 0.21/0.48    inference(avatar_component_clause,[],[f210])).
% 0.21/0.48  fof(f210,plain,(
% 0.21/0.48    spl6_20 <=> r2_hidden(sK5(sK4,sK2,sK3),sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.21/0.48  fof(f370,plain,(
% 0.21/0.48    ~r2_hidden(sK5(sK4,sK2,sK3),sK0) | (~spl6_11 | ~spl6_27)),
% 0.21/0.48    inference(subsumption_resolution,[],[f267,f131])).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    r2_hidden(sK5(sK4,sK2,sK3),sK2) | ~spl6_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f129])).
% 0.21/0.48  % (11925)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.48  % (11917)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    spl6_11 <=> r2_hidden(sK5(sK4,sK2,sK3),sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.21/0.48  fof(f267,plain,(
% 0.21/0.48    ~r2_hidden(sK5(sK4,sK2,sK3),sK2) | ~r2_hidden(sK5(sK4,sK2,sK3),sK0) | ~spl6_27),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f266])).
% 0.21/0.48  fof(f266,plain,(
% 0.21/0.48    sK4 != sK4 | ~r2_hidden(sK5(sK4,sK2,sK3),sK2) | ~r2_hidden(sK5(sK4,sK2,sK3),sK0) | ~spl6_27),
% 0.21/0.48    inference(superposition,[],[f26,f264])).
% 0.21/0.48  fof(f264,plain,(
% 0.21/0.48    sK4 = k1_funct_1(sK3,sK5(sK4,sK2,sK3)) | ~spl6_27),
% 0.21/0.48    inference(avatar_component_clause,[],[f262])).
% 0.21/0.48  fof(f262,plain,(
% 0.21/0.48    spl6_27 <=> sK4 = k1_funct_1(sK3,sK5(sK4,sK2,sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X5] : (sK4 != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X5,sK0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.48    inference(flattening,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.48    inference(ennf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.48    inference(negated_conjecture,[],[f12])).
% 0.21/0.48  fof(f12,conjecture,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).
% 0.21/0.49  fof(f358,plain,(
% 0.21/0.49    spl6_34 | ~spl6_19 | ~spl6_29),
% 0.21/0.49    inference(avatar_split_clause,[],[f324,f274,f192,f355])).
% 0.21/0.49  fof(f192,plain,(
% 0.21/0.49    spl6_19 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.21/0.49  fof(f274,plain,(
% 0.21/0.49    spl6_29 <=> k1_xboole_0 = sK0),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.21/0.49  fof(f324,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl6_19 | ~spl6_29)),
% 0.21/0.49    inference(superposition,[],[f194,f276])).
% 0.21/0.49  fof(f276,plain,(
% 0.21/0.49    k1_xboole_0 = sK0 | ~spl6_29),
% 0.21/0.49    inference(avatar_component_clause,[],[f274])).
% 0.21/0.49  fof(f194,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl6_19),
% 0.21/0.49    inference(avatar_component_clause,[],[f192])).
% 0.21/0.49  fof(f352,plain,(
% 0.21/0.49    ~spl6_33 | spl6_16 | ~spl6_29),
% 0.21/0.49    inference(avatar_split_clause,[],[f322,f274,f166,f349])).
% 0.21/0.49  fof(f166,plain,(
% 0.21/0.49    spl6_16 <=> sK0 = k1_relset_1(sK0,k1_xboole_0,sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.21/0.49  fof(f322,plain,(
% 0.21/0.49    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (spl6_16 | ~spl6_29)),
% 0.21/0.49    inference(superposition,[],[f168,f276])).
% 0.21/0.49  fof(f168,plain,(
% 0.21/0.49    sK0 != k1_relset_1(sK0,k1_xboole_0,sK3) | spl6_16),
% 0.21/0.49    inference(avatar_component_clause,[],[f166])).
% 0.21/0.49  fof(f337,plain,(
% 0.21/0.49    spl6_31 | ~spl6_15 | ~spl6_29),
% 0.21/0.49    inference(avatar_split_clause,[],[f321,f274,f158,f334])).
% 0.21/0.49  fof(f158,plain,(
% 0.21/0.49    spl6_15 <=> v1_funct_2(sK3,sK0,k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.21/0.49  fof(f321,plain,(
% 0.21/0.49    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl6_15 | ~spl6_29)),
% 0.21/0.49    inference(superposition,[],[f160,f276])).
% 0.21/0.49  fof(f160,plain,(
% 0.21/0.49    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl6_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f158])).
% 0.21/0.49  fof(f315,plain,(
% 0.21/0.49    spl6_26 | ~spl6_28),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f314])).
% 0.21/0.49  fof(f314,plain,(
% 0.21/0.49    $false | (spl6_26 | ~spl6_28)),
% 0.21/0.49    inference(subsumption_resolution,[],[f308,f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.49  fof(f308,plain,(
% 0.21/0.49    ~r1_tarski(k1_xboole_0,k4_tarski(sK5(sK4,sK2,k1_xboole_0),sK4)) | (spl6_26 | ~spl6_28)),
% 0.21/0.49    inference(superposition,[],[f259,f272])).
% 0.21/0.49  fof(f272,plain,(
% 0.21/0.49    k1_xboole_0 = sK3 | ~spl6_28),
% 0.21/0.49    inference(avatar_component_clause,[],[f270])).
% 0.21/0.49  fof(f270,plain,(
% 0.21/0.49    spl6_28 <=> k1_xboole_0 = sK3),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.21/0.49  fof(f259,plain,(
% 0.21/0.49    ~r1_tarski(sK3,k4_tarski(sK5(sK4,sK2,sK3),sK4)) | spl6_26),
% 0.21/0.49    inference(avatar_component_clause,[],[f257])).
% 0.21/0.49  fof(f257,plain,(
% 0.21/0.49    spl6_26 <=> r1_tarski(sK3,k4_tarski(sK5(sK4,sK2,sK3),sK4))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.21/0.49  fof(f277,plain,(
% 0.21/0.49    spl6_28 | spl6_29 | ~spl6_15 | ~spl6_19),
% 0.21/0.49    inference(avatar_split_clause,[],[f268,f192,f158,f274,f270])).
% 0.21/0.49  fof(f268,plain,(
% 0.21/0.49    k1_xboole_0 = sK0 | k1_xboole_0 = sK3 | (~spl6_15 | ~spl6_19)),
% 0.21/0.49    inference(subsumption_resolution,[],[f163,f194])).
% 0.21/0.49  fof(f163,plain,(
% 0.21/0.49    k1_xboole_0 = sK0 | k1_xboole_0 = sK3 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl6_15),
% 0.21/0.49    inference(resolution,[],[f160,f55])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X2,X0] : (~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 0.21/0.49    inference(equality_resolution,[],[f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f265,plain,(
% 0.21/0.49    spl6_27 | ~spl6_1 | ~spl6_10 | ~spl6_25),
% 0.21/0.49    inference(avatar_split_clause,[],[f253,f249,f118,f60,f262])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    spl6_1 <=> v1_funct_1(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    spl6_10 <=> v1_relat_1(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.49  fof(f249,plain,(
% 0.21/0.49    spl6_25 <=> r2_hidden(k4_tarski(sK5(sK4,sK2,sK3),sK4),sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.21/0.49  fof(f253,plain,(
% 0.21/0.49    sK4 = k1_funct_1(sK3,sK5(sK4,sK2,sK3)) | (~spl6_1 | ~spl6_10 | ~spl6_25)),
% 0.21/0.49    inference(resolution,[],[f251,f133])).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK3) | k1_funct_1(sK3,X2) = X3) ) | (~spl6_1 | ~spl6_10)),
% 0.21/0.49    inference(subsumption_resolution,[],[f65,f119])).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    v1_relat_1(sK3) | ~spl6_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f118])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ( ! [X2,X3] : (~v1_relat_1(sK3) | k1_funct_1(sK3,X2) = X3 | ~r2_hidden(k4_tarski(X2,X3),sK3)) ) | ~spl6_1),
% 0.21/0.49    inference(resolution,[],[f62,f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(flattening,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    v1_funct_1(sK3) | ~spl6_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f60])).
% 0.21/0.49  fof(f251,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK5(sK4,sK2,sK3),sK4),sK3) | ~spl6_25),
% 0.21/0.49    inference(avatar_component_clause,[],[f249])).
% 0.21/0.49  fof(f260,plain,(
% 0.21/0.49    ~spl6_26 | ~spl6_25),
% 0.21/0.49    inference(avatar_split_clause,[],[f255,f249,f257])).
% 0.21/0.49  fof(f255,plain,(
% 0.21/0.49    ~r1_tarski(sK3,k4_tarski(sK5(sK4,sK2,sK3),sK4)) | ~spl6_25),
% 0.21/0.49    inference(resolution,[],[f251,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.49  fof(f252,plain,(
% 0.21/0.49    spl6_25 | ~spl6_6 | ~spl6_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f247,f118,f94,f249])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    spl6_6 <=> r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.49  fof(f247,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK5(sK4,sK2,sK3),sK4),sK3) | (~spl6_6 | ~spl6_10)),
% 0.21/0.49    inference(subsumption_resolution,[],[f99,f119])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK5(sK4,sK2,sK3),sK4),sK3) | ~v1_relat_1(sK3) | ~spl6_6),
% 0.21/0.49    inference(resolution,[],[f96,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~spl6_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f94])).
% 0.21/0.49  fof(f213,plain,(
% 0.21/0.49    spl6_20 | ~spl6_6 | ~spl6_10 | ~spl6_18),
% 0.21/0.49    inference(avatar_split_clause,[],[f208,f181,f118,f94,f210])).
% 0.21/0.49  fof(f181,plain,(
% 0.21/0.49    spl6_18 <=> sK0 = k1_relat_1(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.21/0.49  fof(f208,plain,(
% 0.21/0.49    r2_hidden(sK5(sK4,sK2,sK3),sK0) | (~spl6_6 | ~spl6_10 | ~spl6_18)),
% 0.21/0.49    inference(forward_demodulation,[],[f142,f183])).
% 0.21/0.49  fof(f183,plain,(
% 0.21/0.49    sK0 = k1_relat_1(sK3) | ~spl6_18),
% 0.21/0.49    inference(avatar_component_clause,[],[f181])).
% 0.21/0.49  fof(f142,plain,(
% 0.21/0.49    r2_hidden(sK5(sK4,sK2,sK3),k1_relat_1(sK3)) | (~spl6_6 | ~spl6_10)),
% 0.21/0.49    inference(subsumption_resolution,[],[f98,f119])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    r2_hidden(sK5(sK4,sK2,sK3),k1_relat_1(sK3)) | ~v1_relat_1(sK3) | ~spl6_6),
% 0.21/0.49    inference(resolution,[],[f96,f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f195,plain,(
% 0.21/0.49    spl6_19 | ~spl6_3 | ~spl6_14),
% 0.21/0.49    inference(avatar_split_clause,[],[f186,f148,f74,f192])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    spl6_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.49  fof(f148,plain,(
% 0.21/0.49    spl6_14 <=> k1_xboole_0 = sK1),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.21/0.49  fof(f186,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl6_3 | ~spl6_14)),
% 0.21/0.49    inference(superposition,[],[f76,f150])).
% 0.21/0.49  fof(f150,plain,(
% 0.21/0.49    k1_xboole_0 = sK1 | ~spl6_14),
% 0.21/0.49    inference(avatar_component_clause,[],[f148])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f74])).
% 0.21/0.49  fof(f184,plain,(
% 0.21/0.49    spl6_18 | ~spl6_3 | ~spl6_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f178,f144,f74,f181])).
% 0.21/0.49  fof(f144,plain,(
% 0.21/0.49    spl6_13 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.21/0.49  fof(f178,plain,(
% 0.21/0.49    sK0 = k1_relat_1(sK3) | (~spl6_3 | ~spl6_13)),
% 0.21/0.49    inference(subsumption_resolution,[],[f176,f76])).
% 0.21/0.49  fof(f176,plain,(
% 0.21/0.49    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_13),
% 0.21/0.49    inference(superposition,[],[f146,f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.49  fof(f146,plain,(
% 0.21/0.49    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl6_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f144])).
% 0.21/0.49  fof(f169,plain,(
% 0.21/0.49    ~spl6_16 | spl6_13 | ~spl6_14),
% 0.21/0.49    inference(avatar_split_clause,[],[f162,f148,f144,f166])).
% 0.21/0.49  fof(f162,plain,(
% 0.21/0.49    sK0 != k1_relset_1(sK0,k1_xboole_0,sK3) | (spl6_13 | ~spl6_14)),
% 0.21/0.49    inference(forward_demodulation,[],[f145,f150])).
% 0.21/0.49  fof(f145,plain,(
% 0.21/0.49    sK0 != k1_relset_1(sK0,sK1,sK3) | spl6_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f144])).
% 0.21/0.49  fof(f161,plain,(
% 0.21/0.49    spl6_15 | ~spl6_2 | ~spl6_14),
% 0.21/0.49    inference(avatar_split_clause,[],[f156,f148,f68,f158])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    spl6_2 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.49  fof(f156,plain,(
% 0.21/0.49    v1_funct_2(sK3,sK0,k1_xboole_0) | (~spl6_2 | ~spl6_14)),
% 0.21/0.49    inference(superposition,[],[f70,f150])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    v1_funct_2(sK3,sK0,sK1) | ~spl6_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f68])).
% 0.21/0.49  fof(f151,plain,(
% 0.21/0.49    spl6_13 | spl6_14 | ~spl6_2 | ~spl6_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f141,f74,f68,f148,f144])).
% 0.21/0.49  fof(f141,plain,(
% 0.21/0.49    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | (~spl6_2 | ~spl6_3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f72,f76])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_2),
% 0.21/0.49    inference(resolution,[],[f70,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    spl6_11 | ~spl6_6 | ~spl6_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f127,f118,f94,f129])).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    r2_hidden(sK5(sK4,sK2,sK3),sK2) | (~spl6_6 | ~spl6_10)),
% 0.21/0.49    inference(subsumption_resolution,[],[f100,f119])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    r2_hidden(sK5(sK4,sK2,sK3),sK2) | ~v1_relat_1(sK3) | ~spl6_6),
% 0.21/0.49    inference(resolution,[],[f96,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK5(X0,X1,X2),X1) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    ~spl6_3 | spl6_10),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f124])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    $false | (~spl6_3 | spl6_10)),
% 0.21/0.49    inference(resolution,[],[f122,f76])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl6_10),
% 0.21/0.49    inference(resolution,[],[f120,f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    ~v1_relat_1(sK3) | spl6_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f118])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    spl6_6 | ~spl6_3 | ~spl6_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f92,f79,f74,f94])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    spl6_4 <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | (~spl6_3 | ~spl6_4)),
% 0.21/0.49    inference(subsumption_resolution,[],[f91,f76])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_4),
% 0.21/0.49    inference(superposition,[],[f81,f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) | ~spl6_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f79])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    spl6_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f27,f79])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    spl6_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f30,f74])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    spl6_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f29,f68])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    spl6_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f28,f60])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    v1_funct_1(sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (11910)------------------------------
% 0.21/0.49  % (11910)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (11910)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (11910)Memory used [KB]: 10874
% 0.21/0.49  % (11910)Time elapsed: 0.069 s
% 0.21/0.49  % (11910)------------------------------
% 0.21/0.49  % (11910)------------------------------
% 0.21/0.49  % (11905)Success in time 0.128 s
%------------------------------------------------------------------------------
