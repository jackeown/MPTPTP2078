%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 193 expanded)
%              Number of leaves         :   23 (  64 expanded)
%              Depth                    :   16
%              Number of atoms          :  424 ( 720 expanded)
%              Number of equality atoms :   48 (  57 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f286,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f81,f89,f95,f100,f110,f117,f131,f164,f185,f223,f285])).

fof(f285,plain,
    ( ~ spl5_1
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_14
    | spl5_15 ),
    inference(avatar_contradiction_clause,[],[f284])).

fof(f284,plain,
    ( $false
    | ~ spl5_1
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_14
    | spl5_15 ),
    inference(subsumption_resolution,[],[f283,f194])).

fof(f194,plain,
    ( ! [X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | spl5_15 ),
    inference(resolution,[],[f184,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f184,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | spl5_15 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl5_15
  <=> v5_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f283,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl5_1
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_14 ),
    inference(duplicate_literal_removal,[],[f281])).

fof(f281,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl5_1
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_14 ),
    inference(resolution,[],[f259,f230])).

fof(f230,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_funct_1(sK3,sK4(sK1,X0,sK3)),X0)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) )
    | ~ spl5_1
    | ~ spl5_7
    | ~ spl5_14 ),
    inference(superposition,[],[f174,f163])).

fof(f163,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl5_14
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f174,plain,
    ( ! [X3] :
        ( ~ r2_hidden(k1_funct_1(sK3,sK4(k1_relat_1(sK3),X3,sK3)),X3)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X3))) )
    | ~ spl5_1
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f83,f109])).

fof(f109,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl5_7
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f83,plain,
    ( ! [X3] :
        ( ~ v1_relat_1(sK3)
        | ~ r2_hidden(k1_funct_1(sK3,sK4(k1_relat_1(sK3),X3,sK3)),X3)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X3))) )
    | ~ spl5_1 ),
    inference(resolution,[],[f70,f65])).

fof(f65,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(k1_funct_1(X2,sK4(k1_relat_1(X2),X1,X2)),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k1_relat_1(X2) != X0
      | ~ r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( ! [X3] :
              ( r2_hidden(X3,X0)
             => r2_hidden(k1_funct_1(X2,X3),X1) )
          & k1_relat_1(X2) = X0 )
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

fof(f70,plain,
    ( v1_funct_1(sK3)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl5_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f259,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK3,sK4(sK1,X0,sK3)),sK0)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) )
    | ~ spl5_1
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_14 ),
    inference(resolution,[],[f235,f214])).

fof(f214,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(k1_funct_1(sK3,X0),sK0) )
    | ~ spl5_1
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(resolution,[],[f180,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f180,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | r2_hidden(k1_funct_1(sK3,X0),sK0) )
    | ~ spl5_1
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f179,f80])).

fof(f80,plain,
    ( ~ v1_xboole_0(sK1)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl5_3
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f179,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK3,X0),sK0)
        | ~ m1_subset_1(X0,sK1)
        | v1_xboole_0(sK1) )
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f178,f94])).

fof(f94,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl5_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f178,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK3,X0),sK0)
        | ~ m1_subset_1(X0,sK1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | v1_xboole_0(sK1) )
    | ~ spl5_1
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f177,f88])).

fof(f88,plain,
    ( v1_funct_2(sK3,sK1,sK2)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl5_4
  <=> v1_funct_2(sK3,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f177,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK3,X0),sK0)
        | ~ m1_subset_1(X0,sK1)
        | ~ v1_funct_2(sK3,sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | v1_xboole_0(sK1) )
    | ~ spl5_1 ),
    inference(duplicate_literal_removal,[],[f176])).

fof(f176,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK3,X0),sK0)
        | ~ m1_subset_1(X0,sK1)
        | ~ v1_funct_2(sK3,sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | ~ m1_subset_1(X0,sK1)
        | v1_xboole_0(sK1) )
    | ~ spl5_1 ),
    inference(superposition,[],[f30,f82])).

fof(f82,plain,
    ( ! [X2,X0,X1] :
        ( k3_funct_2(X0,X1,sK3,X2) = k1_funct_1(sK3,X2)
        | ~ v1_funct_2(sK3,X0,X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X2,X0)
        | v1_xboole_0(X0) )
    | ~ spl5_1 ),
    inference(resolution,[],[f70,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | v1_xboole_0(X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f30,plain,(
    ! [X4] :
      ( r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0)
      | ~ m1_subset_1(X4,sK1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                  | ~ m1_subset_1(X4,X1) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                  | ~ m1_subset_1(X4,X1) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_2(X3,X1,X2)
                  & v1_funct_1(X3) )
               => ( ! [X4] :
                      ( m1_subset_1(X4,X1)
                     => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) )
                 => r1_tarski(k2_relset_1(X1,X2,X3),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_2(X3,X1,X2)
                & v1_funct_1(X3) )
             => ( ! [X4] :
                    ( m1_subset_1(X4,X1)
                   => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) )
               => r1_tarski(k2_relset_1(X1,X2,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_funct_2)).

fof(f235,plain,
    ( ! [X2] :
        ( r2_hidden(sK4(sK1,X2,sK3),sK1)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) )
    | ~ spl5_1
    | ~ spl5_7
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f234,f109])).

fof(f234,plain,
    ( ! [X2] :
        ( r2_hidden(sK4(sK1,X2,sK3),sK1)
        | ~ v1_relat_1(sK3)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) )
    | ~ spl5_1
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f232,f70])).

fof(f232,plain,
    ( ! [X2] :
        ( r2_hidden(sK4(sK1,X2,sK3),sK1)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) )
    | ~ spl5_14 ),
    inference(superposition,[],[f66,f163])).

fof(f66,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK4(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k1_relat_1(X2) != X0
      | r2_hidden(sK4(X0,X1,X2),X0)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f223,plain,
    ( ~ spl5_5
    | ~ spl5_7
    | spl5_8
    | ~ spl5_10 ),
    inference(avatar_contradiction_clause,[],[f222])).

fof(f222,plain,
    ( $false
    | ~ spl5_5
    | ~ spl5_7
    | spl5_8
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f221,f37])).

fof(f37,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f221,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | ~ spl5_5
    | ~ spl5_7
    | spl5_8
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f218,f130])).

fof(f130,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl5_10
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f218,plain,
    ( ~ r1_tarski(sK2,sK0)
    | ~ spl5_5
    | ~ spl5_7
    | spl5_8 ),
    inference(resolution,[],[f211,f94])).

fof(f211,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ r1_tarski(X1,sK0) )
    | ~ spl5_7
    | spl5_8 ),
    inference(resolution,[],[f186,f45])).

fof(f186,plain,
    ( ! [X0] :
        ( ~ v5_relat_1(sK3,X0)
        | ~ r1_tarski(X0,sK0) )
    | ~ spl5_7
    | spl5_8 ),
    inference(resolution,[],[f118,f112])).

fof(f112,plain,
    ( ! [X1] :
        ( r1_tarski(k2_relat_1(sK3),X1)
        | ~ v5_relat_1(sK3,X1) )
    | ~ spl5_7 ),
    inference(resolution,[],[f109,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

% (1714)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
fof(f16,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f118,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK3),X0)
        | ~ r1_tarski(X0,sK0) )
    | spl5_8 ),
    inference(resolution,[],[f116,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f116,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK0)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl5_8
  <=> r1_tarski(k2_relat_1(sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f185,plain,
    ( ~ spl5_15
    | ~ spl5_7
    | spl5_8 ),
    inference(avatar_split_clause,[],[f175,f114,f107,f182])).

fof(f175,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | ~ spl5_7
    | spl5_8 ),
    inference(resolution,[],[f112,f116])).

fof(f164,plain,
    ( spl5_14
    | ~ spl5_5
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f158,f124,f92,f161])).

fof(f124,plain,
    ( spl5_9
  <=> sK1 = k1_relset_1(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f158,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl5_5
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f156,f94])).

fof(f156,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_9 ),
    inference(superposition,[],[f126,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f126,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f124])).

fof(f131,plain,
    ( spl5_9
    | spl5_10
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f122,f92,f86,f128,f124])).

fof(f122,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f90,f94])).

fof(f90,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_4 ),
    inference(resolution,[],[f88,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f117,plain,
    ( ~ spl5_8
    | ~ spl5_5
    | spl5_6 ),
    inference(avatar_split_clause,[],[f105,f97,f92,f114])).

fof(f97,plain,
    ( spl5_6
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f105,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK0)
    | ~ spl5_5
    | spl5_6 ),
    inference(subsumption_resolution,[],[f104,f94])).

fof(f104,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl5_6 ),
    inference(superposition,[],[f99,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f99,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f97])).

fof(f110,plain,
    ( spl5_7
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f102,f92,f107])).

fof(f102,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_5 ),
    inference(resolution,[],[f94,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f100,plain,(
    ~ spl5_6 ),
    inference(avatar_split_clause,[],[f34,f97])).

fof(f34,plain,(
    ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f95,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f33,f92])).

fof(f33,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f15])).

fof(f89,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f32,f86])).

fof(f32,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f81,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f36,f78])).

fof(f36,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f71,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f31,f68])).

fof(f31,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:52:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (1709)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (1709)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (1718)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f286,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f71,f81,f89,f95,f100,f110,f117,f131,f164,f185,f223,f285])).
% 0.21/0.48  fof(f285,plain,(
% 0.21/0.48    ~spl5_1 | spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_14 | spl5_15),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f284])).
% 0.21/0.48  fof(f284,plain,(
% 0.21/0.48    $false | (~spl5_1 | spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_14 | spl5_15)),
% 0.21/0.48    inference(subsumption_resolution,[],[f283,f194])).
% 0.21/0.48  fof(f194,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))) ) | spl5_15),
% 0.21/0.48    inference(resolution,[],[f184,f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.48  fof(f184,plain,(
% 0.21/0.48    ~v5_relat_1(sK3,sK0) | spl5_15),
% 0.21/0.48    inference(avatar_component_clause,[],[f182])).
% 0.21/0.48  fof(f182,plain,(
% 0.21/0.48    spl5_15 <=> v5_relat_1(sK3,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.48  fof(f283,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl5_1 | spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_14)),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f281])).
% 0.21/0.48  fof(f281,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl5_1 | spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_14)),
% 0.21/0.48    inference(resolution,[],[f259,f230])).
% 0.21/0.48  fof(f230,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(k1_funct_1(sK3,sK4(sK1,X0,sK3)),X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))) ) | (~spl5_1 | ~spl5_7 | ~spl5_14)),
% 0.21/0.48    inference(superposition,[],[f174,f163])).
% 0.21/0.48  fof(f163,plain,(
% 0.21/0.48    sK1 = k1_relat_1(sK3) | ~spl5_14),
% 0.21/0.48    inference(avatar_component_clause,[],[f161])).
% 0.21/0.48  fof(f161,plain,(
% 0.21/0.48    spl5_14 <=> sK1 = k1_relat_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.48  fof(f174,plain,(
% 0.21/0.48    ( ! [X3] : (~r2_hidden(k1_funct_1(sK3,sK4(k1_relat_1(sK3),X3,sK3)),X3) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X3)))) ) | (~spl5_1 | ~spl5_7)),
% 0.21/0.48    inference(subsumption_resolution,[],[f83,f109])).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    v1_relat_1(sK3) | ~spl5_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f107])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    spl5_7 <=> v1_relat_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    ( ! [X3] : (~v1_relat_1(sK3) | ~r2_hidden(k1_funct_1(sK3,sK4(k1_relat_1(sK3),X3,sK3)),X3) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X3)))) ) | ~spl5_1),
% 0.21/0.48    inference(resolution,[],[f70,f65])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X2,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r2_hidden(k1_funct_1(X2,sK4(k1_relat_1(X2),X1,X2)),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))) )),
% 0.21/0.48    inference(equality_resolution,[],[f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_relat_1(X2) != X0 | ~r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.48    inference(flattening,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    v1_funct_1(sK3) | ~spl5_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f68])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    spl5_1 <=> v1_funct_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.48  fof(f259,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,sK4(sK1,X0,sK3)),sK0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))) ) | (~spl5_1 | spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_14)),
% 0.21/0.48    inference(resolution,[],[f235,f214])).
% 0.21/0.48  fof(f214,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(k1_funct_1(sK3,X0),sK0)) ) | (~spl5_1 | spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.21/0.48    inference(resolution,[],[f180,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.21/0.48  fof(f180,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,sK1) | r2_hidden(k1_funct_1(sK3,X0),sK0)) ) | (~spl5_1 | spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.21/0.48    inference(subsumption_resolution,[],[f179,f80])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    ~v1_xboole_0(sK1) | spl5_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f78])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    spl5_3 <=> v1_xboole_0(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.48  fof(f179,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),sK0) | ~m1_subset_1(X0,sK1) | v1_xboole_0(sK1)) ) | (~spl5_1 | ~spl5_4 | ~spl5_5)),
% 0.21/0.48    inference(subsumption_resolution,[],[f178,f94])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl5_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f92])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    spl5_5 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.48  fof(f178,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),sK0) | ~m1_subset_1(X0,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | v1_xboole_0(sK1)) ) | (~spl5_1 | ~spl5_4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f177,f88])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    v1_funct_2(sK3,sK1,sK2) | ~spl5_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f86])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    spl5_4 <=> v1_funct_2(sK3,sK1,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.48  fof(f177,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),sK0) | ~m1_subset_1(X0,sK1) | ~v1_funct_2(sK3,sK1,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | v1_xboole_0(sK1)) ) | ~spl5_1),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f176])).
% 0.21/0.48  fof(f176,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),sK0) | ~m1_subset_1(X0,sK1) | ~v1_funct_2(sK3,sK1,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~m1_subset_1(X0,sK1) | v1_xboole_0(sK1)) ) | ~spl5_1),
% 0.21/0.48    inference(superposition,[],[f30,f82])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k3_funct_2(X0,X1,sK3,X2) = k1_funct_1(sK3,X2) | ~v1_funct_2(sK3,X0,X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,X0) | v1_xboole_0(X0)) ) | ~spl5_1),
% 0.21/0.48    inference(resolution,[],[f70,f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | v1_xboole_0(X0) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.21/0.48    inference(flattening,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X4] : (r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0) | ~m1_subset_1(X4,sK1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 0.21/0.48    inference(flattening,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 0.21/0.48    inference(negated_conjecture,[],[f12])).
% 0.21/0.48  fof(f12,conjecture,(
% 0.21/0.48    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_funct_2)).
% 0.21/0.48  fof(f235,plain,(
% 0.21/0.48    ( ! [X2] : (r2_hidden(sK4(sK1,X2,sK3),sK1) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))) ) | (~spl5_1 | ~spl5_7 | ~spl5_14)),
% 0.21/0.48    inference(subsumption_resolution,[],[f234,f109])).
% 0.21/0.48  fof(f234,plain,(
% 0.21/0.48    ( ! [X2] : (r2_hidden(sK4(sK1,X2,sK3),sK1) | ~v1_relat_1(sK3) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))) ) | (~spl5_1 | ~spl5_14)),
% 0.21/0.48    inference(subsumption_resolution,[],[f232,f70])).
% 0.21/0.48  fof(f232,plain,(
% 0.21/0.48    ( ! [X2] : (r2_hidden(sK4(sK1,X2,sK3),sK1) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))) ) | ~spl5_14),
% 0.21/0.48    inference(superposition,[],[f66,f163])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ( ! [X2,X1] : (r2_hidden(sK4(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))) )),
% 0.21/0.48    inference(equality_resolution,[],[f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_relat_1(X2) != X0 | r2_hidden(sK4(X0,X1,X2),X0) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f223,plain,(
% 0.21/0.48    ~spl5_5 | ~spl5_7 | spl5_8 | ~spl5_10),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f222])).
% 0.21/0.48  fof(f222,plain,(
% 0.21/0.48    $false | (~spl5_5 | ~spl5_7 | spl5_8 | ~spl5_10)),
% 0.21/0.48    inference(subsumption_resolution,[],[f221,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.48  fof(f221,plain,(
% 0.21/0.48    ~r1_tarski(k1_xboole_0,sK0) | (~spl5_5 | ~spl5_7 | spl5_8 | ~spl5_10)),
% 0.21/0.48    inference(forward_demodulation,[],[f218,f130])).
% 0.21/0.48  fof(f130,plain,(
% 0.21/0.48    k1_xboole_0 = sK2 | ~spl5_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f128])).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    spl5_10 <=> k1_xboole_0 = sK2),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.48  fof(f218,plain,(
% 0.21/0.48    ~r1_tarski(sK2,sK0) | (~spl5_5 | ~spl5_7 | spl5_8)),
% 0.21/0.48    inference(resolution,[],[f211,f94])).
% 0.21/0.48  fof(f211,plain,(
% 0.21/0.48    ( ! [X2,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(X1,sK0)) ) | (~spl5_7 | spl5_8)),
% 0.21/0.48    inference(resolution,[],[f186,f45])).
% 0.21/0.48  fof(f186,plain,(
% 0.21/0.48    ( ! [X0] : (~v5_relat_1(sK3,X0) | ~r1_tarski(X0,sK0)) ) | (~spl5_7 | spl5_8)),
% 0.21/0.48    inference(resolution,[],[f118,f112])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    ( ! [X1] : (r1_tarski(k2_relat_1(sK3),X1) | ~v5_relat_1(sK3,X1)) ) | ~spl5_7),
% 0.21/0.48    inference(resolution,[],[f109,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  % (1714)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3),X0) | ~r1_tarski(X0,sK0)) ) | spl5_8),
% 0.21/0.48    inference(resolution,[],[f116,f56])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    ~r1_tarski(k2_relat_1(sK3),sK0) | spl5_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f114])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    spl5_8 <=> r1_tarski(k2_relat_1(sK3),sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.48  fof(f185,plain,(
% 0.21/0.48    ~spl5_15 | ~spl5_7 | spl5_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f175,f114,f107,f182])).
% 0.21/0.48  fof(f175,plain,(
% 0.21/0.48    ~v5_relat_1(sK3,sK0) | (~spl5_7 | spl5_8)),
% 0.21/0.48    inference(resolution,[],[f112,f116])).
% 0.21/0.48  fof(f164,plain,(
% 0.21/0.48    spl5_14 | ~spl5_5 | ~spl5_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f158,f124,f92,f161])).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    spl5_9 <=> sK1 = k1_relset_1(sK1,sK2,sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.48  fof(f158,plain,(
% 0.21/0.48    sK1 = k1_relat_1(sK3) | (~spl5_5 | ~spl5_9)),
% 0.21/0.48    inference(subsumption_resolution,[],[f156,f94])).
% 0.21/0.48  fof(f156,plain,(
% 0.21/0.48    sK1 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl5_9),
% 0.21/0.48    inference(superposition,[],[f126,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    sK1 = k1_relset_1(sK1,sK2,sK3) | ~spl5_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f124])).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    spl5_9 | spl5_10 | ~spl5_4 | ~spl5_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f122,f92,f86,f128,f124])).
% 0.21/0.48  fof(f122,plain,(
% 0.21/0.48    k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3) | (~spl5_4 | ~spl5_5)),
% 0.21/0.48    inference(subsumption_resolution,[],[f90,f94])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl5_4),
% 0.21/0.48    inference(resolution,[],[f88,f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(flattening,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    ~spl5_8 | ~spl5_5 | spl5_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f105,f97,f92,f114])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    spl5_6 <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    ~r1_tarski(k2_relat_1(sK3),sK0) | (~spl5_5 | spl5_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f104,f94])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    ~r1_tarski(k2_relat_1(sK3),sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl5_6),
% 0.21/0.48    inference(superposition,[],[f99,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    ~r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0) | spl5_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f97])).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    spl5_7 | ~spl5_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f102,f92,f107])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    v1_relat_1(sK3) | ~spl5_5),
% 0.21/0.48    inference(resolution,[],[f94,f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    ~spl5_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f34,f97])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ~r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    spl5_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f33,f92])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    spl5_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f32,f86])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    v1_funct_2(sK3,sK1,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    ~spl5_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f36,f78])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ~v1_xboole_0(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    spl5_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f31,f68])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    v1_funct_1(sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (1709)------------------------------
% 0.21/0.48  % (1709)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (1709)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (1709)Memory used [KB]: 10746
% 0.21/0.48  % (1709)Time elapsed: 0.068 s
% 0.21/0.48  % (1709)------------------------------
% 0.21/0.48  % (1709)------------------------------
% 0.21/0.48  % (1704)Success in time 0.125 s
%------------------------------------------------------------------------------
