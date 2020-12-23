%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 269 expanded)
%              Number of leaves         :   26 ( 110 expanded)
%              Depth                    :   12
%              Number of atoms          :  493 ( 869 expanded)
%              Number of equality atoms :   18 (  49 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f357,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f67,f80,f84,f89,f96,f113,f128,f137,f180,f198,f225,f317,f321,f335,f355])).

fof(f355,plain,
    ( ~ spl8_1
    | ~ spl8_3
    | ~ spl8_31
    | ~ spl8_32
    | ~ spl8_33 ),
    inference(avatar_contradiction_clause,[],[f354])).

fof(f354,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_31
    | ~ spl8_32
    | ~ spl8_33 ),
    inference(subsumption_resolution,[],[f353,f79])).

fof(f79,plain,
    ( v1_relat_1(sK3)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl8_3
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f353,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl8_1
    | ~ spl8_31
    | ~ spl8_32
    | ~ spl8_33 ),
    inference(subsumption_resolution,[],[f352,f325])).

fof(f325,plain,
    ( sK4 != k1_funct_1(sK3,sK6(sK2,sK0,sK3,sK4))
    | ~ spl8_31
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f322,f320])).

fof(f320,plain,
    ( r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2)
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f319])).

fof(f319,plain,
    ( spl8_32
  <=> r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f322,plain,
    ( ~ r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2)
    | sK4 != k1_funct_1(sK3,sK6(sK2,sK0,sK3,sK4))
    | ~ spl8_31 ),
    inference(resolution,[],[f316,f31])).

fof(f31,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,sK0)
      | ~ r2_hidden(X5,sK2)
      | sK4 != k1_funct_1(sK3,X5) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ( m1_subset_1(X5,X0)
               => ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2) ) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).

fof(f316,plain,
    ( m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0)
    | ~ spl8_31 ),
    inference(avatar_component_clause,[],[f315])).

fof(f315,plain,
    ( spl8_31
  <=> m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f352,plain,
    ( sK4 = k1_funct_1(sK3,sK6(sK2,sK0,sK3,sK4))
    | ~ v1_relat_1(sK3)
    | ~ spl8_1
    | ~ spl8_33 ),
    inference(subsumption_resolution,[],[f343,f62])).

fof(f62,plain,
    ( v1_funct_1(sK3)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl8_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f343,plain,
    ( ~ v1_funct_1(sK3)
    | sK4 = k1_funct_1(sK3,sK6(sK2,sK0,sK3,sK4))
    | ~ v1_relat_1(sK3)
    | ~ spl8_33 ),
    inference(resolution,[],[f334,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f334,plain,
    ( r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3)
    | ~ spl8_33 ),
    inference(avatar_component_clause,[],[f333])).

fof(f333,plain,
    ( spl8_33
  <=> r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f335,plain,
    ( spl8_33
    | ~ spl8_2
    | ~ spl8_5
    | spl8_7
    | spl8_8
    | spl8_12
    | ~ spl8_21 ),
    inference(avatar_split_clause,[],[f309,f223,f135,f111,f94,f87,f65,f333])).

fof(f65,plain,
    ( spl8_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f87,plain,
    ( spl8_5
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f94,plain,
    ( spl8_7
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f111,plain,
    ( spl8_8
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f135,plain,
    ( spl8_12
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f223,plain,
    ( spl8_21
  <=> m1_subset_1(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f309,plain,
    ( r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3)
    | ~ spl8_2
    | ~ spl8_5
    | spl8_7
    | spl8_8
    | spl8_12
    | ~ spl8_21 ),
    inference(subsumption_resolution,[],[f308,f224])).

fof(f224,plain,
    ( m1_subset_1(sK4,sK1)
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f223])).

fof(f308,plain,
    ( ~ m1_subset_1(sK4,sK1)
    | r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3)
    | ~ spl8_2
    | ~ spl8_5
    | spl8_7
    | spl8_8
    | spl8_12 ),
    inference(subsumption_resolution,[],[f305,f136])).

fof(f136,plain,
    ( ~ v1_xboole_0(sK2)
    | spl8_12 ),
    inference(avatar_component_clause,[],[f135])).

fof(f305,plain,
    ( v1_xboole_0(sK2)
    | ~ m1_subset_1(sK4,sK1)
    | r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3)
    | ~ spl8_2
    | ~ spl8_5
    | spl8_7
    | spl8_8 ),
    inference(resolution,[],[f208,f88])).

fof(f88,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f87])).

fof(f208,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X4,k9_relat_1(sK3,X3))
        | v1_xboole_0(X3)
        | ~ m1_subset_1(X4,sK1)
        | r2_hidden(k4_tarski(sK6(X3,sK0,sK3,X4),X4),sK3) )
    | ~ spl8_2
    | spl8_7
    | spl8_8 ),
    inference(subsumption_resolution,[],[f207,f95])).

fof(f95,plain,
    ( ~ v1_xboole_0(sK1)
    | spl8_7 ),
    inference(avatar_component_clause,[],[f94])).

fof(f207,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X4,k9_relat_1(sK3,X3))
        | v1_xboole_0(X3)
        | ~ m1_subset_1(X4,sK1)
        | r2_hidden(k4_tarski(sK6(X3,sK0,sK3,X4),X4),sK3)
        | v1_xboole_0(sK1) )
    | ~ spl8_2
    | spl8_8 ),
    inference(subsumption_resolution,[],[f206,f66])).

fof(f66,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f206,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X4,k9_relat_1(sK3,X3))
        | v1_xboole_0(X3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(X4,sK1)
        | r2_hidden(k4_tarski(sK6(X3,sK0,sK3,X4),X4),sK3)
        | v1_xboole_0(sK1) )
    | ~ spl8_2
    | spl8_8 ),
    inference(subsumption_resolution,[],[f201,f112])).

fof(f112,plain,
    ( ~ v1_xboole_0(sK0)
    | spl8_8 ),
    inference(avatar_component_clause,[],[f111])).

fof(f201,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X4,k9_relat_1(sK3,X3))
        | v1_xboole_0(X3)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(X4,sK1)
        | r2_hidden(k4_tarski(sK6(X3,sK0,sK3,X4),X4),sK3)
        | v1_xboole_0(sK1) )
    | ~ spl8_2 ),
    inference(superposition,[],[f49,f73])).

fof(f73,plain,
    ( ! [X4] : k7_relset_1(sK0,sK1,sK3,X4) = k9_relat_1(sK3,X4)
    | ~ spl8_2 ),
    inference(resolution,[],[f66,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ m1_subset_1(X4,X0)
      | r2_hidden(k4_tarski(sK6(X1,X2,X3,X4),X4),X3)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) ) )
                      | ~ m1_subset_1(X4,X0) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                 => ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relset_1)).

fof(f321,plain,
    ( spl8_32
    | ~ spl8_2
    | ~ spl8_5
    | spl8_7
    | spl8_8
    | spl8_12
    | ~ spl8_21 ),
    inference(avatar_split_clause,[],[f298,f223,f135,f111,f94,f87,f65,f319])).

fof(f298,plain,
    ( r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2)
    | ~ spl8_2
    | ~ spl8_5
    | spl8_7
    | spl8_8
    | spl8_12
    | ~ spl8_21 ),
    inference(subsumption_resolution,[],[f297,f224])).

fof(f297,plain,
    ( ~ m1_subset_1(sK4,sK1)
    | r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2)
    | ~ spl8_2
    | ~ spl8_5
    | spl8_7
    | spl8_8
    | spl8_12 ),
    inference(subsumption_resolution,[],[f294,f136])).

fof(f294,plain,
    ( v1_xboole_0(sK2)
    | ~ m1_subset_1(sK4,sK1)
    | r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2)
    | ~ spl8_2
    | ~ spl8_5
    | spl8_7
    | spl8_8 ),
    inference(resolution,[],[f211,f88])).

fof(f211,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(X6,k9_relat_1(sK3,X5))
        | v1_xboole_0(X5)
        | ~ m1_subset_1(X6,sK1)
        | r2_hidden(sK6(X5,sK0,sK3,X6),X5) )
    | ~ spl8_2
    | spl8_7
    | spl8_8 ),
    inference(subsumption_resolution,[],[f210,f95])).

fof(f210,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(X6,k9_relat_1(sK3,X5))
        | v1_xboole_0(X5)
        | ~ m1_subset_1(X6,sK1)
        | r2_hidden(sK6(X5,sK0,sK3,X6),X5)
        | v1_xboole_0(sK1) )
    | ~ spl8_2
    | spl8_8 ),
    inference(subsumption_resolution,[],[f209,f66])).

fof(f209,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(X6,k9_relat_1(sK3,X5))
        | v1_xboole_0(X5)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(X6,sK1)
        | r2_hidden(sK6(X5,sK0,sK3,X6),X5)
        | v1_xboole_0(sK1) )
    | ~ spl8_2
    | spl8_8 ),
    inference(subsumption_resolution,[],[f202,f112])).

fof(f202,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(X6,k9_relat_1(sK3,X5))
        | v1_xboole_0(X5)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(X6,sK1)
        | r2_hidden(sK6(X5,sK0,sK3,X6),X5)
        | v1_xboole_0(sK1) )
    | ~ spl8_2 ),
    inference(superposition,[],[f50,f73])).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ m1_subset_1(X4,X0)
      | r2_hidden(sK6(X1,X2,X3,X4),X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f317,plain,
    ( spl8_31
    | ~ spl8_2
    | ~ spl8_5
    | spl8_7
    | spl8_8
    | spl8_12
    | ~ spl8_21 ),
    inference(avatar_split_clause,[],[f291,f223,f135,f111,f94,f87,f65,f315])).

fof(f291,plain,
    ( m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0)
    | ~ spl8_2
    | ~ spl8_5
    | spl8_7
    | spl8_8
    | spl8_12
    | ~ spl8_21 ),
    inference(subsumption_resolution,[],[f290,f224])).

fof(f290,plain,
    ( ~ m1_subset_1(sK4,sK1)
    | m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0)
    | ~ spl8_2
    | ~ spl8_5
    | spl8_7
    | spl8_8
    | spl8_12 ),
    inference(subsumption_resolution,[],[f287,f136])).

fof(f287,plain,
    ( v1_xboole_0(sK2)
    | ~ m1_subset_1(sK4,sK1)
    | m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0)
    | ~ spl8_2
    | ~ spl8_5
    | spl8_7
    | spl8_8 ),
    inference(resolution,[],[f205,f88])).

fof(f205,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X2,k9_relat_1(sK3,X1))
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X2,sK1)
        | m1_subset_1(sK6(X1,sK0,sK3,X2),sK0) )
    | ~ spl8_2
    | spl8_7
    | spl8_8 ),
    inference(subsumption_resolution,[],[f204,f95])).

fof(f204,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X2,k9_relat_1(sK3,X1))
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X2,sK1)
        | m1_subset_1(sK6(X1,sK0,sK3,X2),sK0)
        | v1_xboole_0(sK1) )
    | ~ spl8_2
    | spl8_8 ),
    inference(subsumption_resolution,[],[f203,f66])).

fof(f203,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X2,k9_relat_1(sK3,X1))
        | v1_xboole_0(X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(X2,sK1)
        | m1_subset_1(sK6(X1,sK0,sK3,X2),sK0)
        | v1_xboole_0(sK1) )
    | ~ spl8_2
    | spl8_8 ),
    inference(subsumption_resolution,[],[f200,f112])).

fof(f200,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X2,k9_relat_1(sK3,X1))
        | v1_xboole_0(X1)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(X2,sK1)
        | m1_subset_1(sK6(X1,sK0,sK3,X2),sK0)
        | v1_xboole_0(sK1) )
    | ~ spl8_2 ),
    inference(superposition,[],[f48,f73])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ m1_subset_1(X4,X0)
      | m1_subset_1(sK6(X1,X2,X3,X4),X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f225,plain,
    ( spl8_21
    | ~ spl8_2
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f215,f87,f65,f223])).

fof(f215,plain,
    ( m1_subset_1(sK4,sK1)
    | ~ spl8_2
    | ~ spl8_5 ),
    inference(resolution,[],[f199,f105])).

fof(f105,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(X0))
        | m1_subset_1(sK4,X0) )
    | ~ spl8_5 ),
    inference(resolution,[],[f88,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f199,plain,
    ( ! [X0] : m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(sK1))
    | ~ spl8_2 ),
    inference(superposition,[],[f72,f73])).

fof(f72,plain,
    ( ! [X3] : m1_subset_1(k7_relset_1(sK0,sK1,sK3,X3),k1_zfmisc_1(sK1))
    | ~ spl8_2 ),
    inference(resolution,[],[f66,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(f198,plain,
    ( ~ spl8_6
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f188,f178,f91])).

fof(f91,plain,
    ( spl8_6
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f178,plain,
    ( spl8_18
  <=> r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f188,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl8_18 ),
    inference(resolution,[],[f179,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f179,plain,
    ( r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3)
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f178])).

fof(f180,plain,
    ( spl8_18
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f107,f87,f78,f178])).

fof(f107,plain,
    ( r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3)
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f100,f79])).

fof(f100,plain,
    ( r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_5 ),
    inference(resolution,[],[f88,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK7(X0,X1,X2),X0),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f137,plain,
    ( ~ spl8_12
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f129,f126,f135])).

fof(f126,plain,
    ( spl8_11
  <=> r2_hidden(sK7(sK4,sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f129,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl8_11 ),
    inference(resolution,[],[f127,f46])).

fof(f127,plain,
    ( r2_hidden(sK7(sK4,sK2,sK3),sK2)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f126])).

fof(f128,plain,
    ( spl8_11
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f108,f87,f78,f126])).

fof(f108,plain,
    ( r2_hidden(sK7(sK4,sK2,sK3),sK2)
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f101,f79])).

fof(f101,plain,
    ( r2_hidden(sK7(sK4,sK2,sK3),sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl8_5 ),
    inference(resolution,[],[f88,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK7(X0,X1,X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f113,plain,
    ( spl8_6
    | ~ spl8_8
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f70,f65,f111,f91])).

fof(f70,plain,
    ( ~ v1_xboole_0(sK0)
    | v1_xboole_0(sK3)
    | ~ spl8_2 ),
    inference(resolution,[],[f66,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f96,plain,
    ( spl8_6
    | ~ spl8_7
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f69,f65,f94,f91])).

fof(f69,plain,
    ( ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK3)
    | ~ spl8_2 ),
    inference(resolution,[],[f66,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f89,plain,
    ( spl8_5
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f85,f82,f65,f87])).

fof(f82,plain,
    ( spl8_4
  <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f85,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(forward_demodulation,[],[f83,f73])).

fof(f83,plain,
    ( r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f82])).

fof(f84,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f32,f82])).

fof(f32,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f80,plain,
    ( spl8_3
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f68,f65,f78])).

fof(f68,plain,
    ( v1_relat_1(sK3)
    | ~ spl8_2 ),
    inference(resolution,[],[f66,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f67,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f34,f65])).

fof(f34,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f63,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f33,f61])).

fof(f33,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:02:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (22103)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (22091)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (22109)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.49  % (22092)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (22094)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (22095)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (22104)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (22098)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % (22101)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.50  % (22096)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (22106)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.50  % (22099)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.50  % (22093)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (22105)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (22090)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (22110)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (22110)Refutation not found, incomplete strategy% (22110)------------------------------
% 0.21/0.51  % (22110)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (22110)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (22110)Memory used [KB]: 10618
% 0.21/0.51  % (22110)Time elapsed: 0.096 s
% 0.21/0.51  % (22110)------------------------------
% 0.21/0.51  % (22110)------------------------------
% 0.21/0.51  % (22090)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f357,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f63,f67,f80,f84,f89,f96,f113,f128,f137,f180,f198,f225,f317,f321,f335,f355])).
% 0.21/0.51  fof(f355,plain,(
% 0.21/0.51    ~spl8_1 | ~spl8_3 | ~spl8_31 | ~spl8_32 | ~spl8_33),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f354])).
% 0.21/0.51  fof(f354,plain,(
% 0.21/0.51    $false | (~spl8_1 | ~spl8_3 | ~spl8_31 | ~spl8_32 | ~spl8_33)),
% 0.21/0.51    inference(subsumption_resolution,[],[f353,f79])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    v1_relat_1(sK3) | ~spl8_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f78])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    spl8_3 <=> v1_relat_1(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.51  fof(f353,plain,(
% 0.21/0.51    ~v1_relat_1(sK3) | (~spl8_1 | ~spl8_31 | ~spl8_32 | ~spl8_33)),
% 0.21/0.51    inference(subsumption_resolution,[],[f352,f325])).
% 0.21/0.51  fof(f325,plain,(
% 0.21/0.51    sK4 != k1_funct_1(sK3,sK6(sK2,sK0,sK3,sK4)) | (~spl8_31 | ~spl8_32)),
% 0.21/0.51    inference(subsumption_resolution,[],[f322,f320])).
% 0.21/0.51  fof(f320,plain,(
% 0.21/0.51    r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2) | ~spl8_32),
% 0.21/0.51    inference(avatar_component_clause,[],[f319])).
% 0.21/0.51  fof(f319,plain,(
% 0.21/0.51    spl8_32 <=> r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).
% 0.21/0.51  fof(f322,plain,(
% 0.21/0.51    ~r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2) | sK4 != k1_funct_1(sK3,sK6(sK2,sK0,sK3,sK4)) | ~spl8_31),
% 0.21/0.51    inference(resolution,[],[f316,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ( ! [X5] : (~m1_subset_1(X5,sK0) | ~r2_hidden(X5,sK2) | sK4 != k1_funct_1(sK3,X5)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 0.21/0.51    inference(flattening,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 0.21/0.51    inference(ennf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.51    inference(pure_predicate_removal,[],[f14])).
% 0.21/0.51  fof(f14,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.51    inference(negated_conjecture,[],[f13])).
% 0.21/0.51  fof(f13,conjecture,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).
% 0.21/0.51  fof(f316,plain,(
% 0.21/0.51    m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0) | ~spl8_31),
% 0.21/0.51    inference(avatar_component_clause,[],[f315])).
% 0.21/0.51  fof(f315,plain,(
% 0.21/0.51    spl8_31 <=> m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).
% 0.21/0.51  fof(f352,plain,(
% 0.21/0.51    sK4 = k1_funct_1(sK3,sK6(sK2,sK0,sK3,sK4)) | ~v1_relat_1(sK3) | (~spl8_1 | ~spl8_33)),
% 0.21/0.51    inference(subsumption_resolution,[],[f343,f62])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    v1_funct_1(sK3) | ~spl8_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    spl8_1 <=> v1_funct_1(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.51  fof(f343,plain,(
% 0.21/0.51    ~v1_funct_1(sK3) | sK4 = k1_funct_1(sK3,sK6(sK2,sK0,sK3,sK4)) | ~v1_relat_1(sK3) | ~spl8_33),
% 0.21/0.51    inference(resolution,[],[f334,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.51    inference(flattening,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.21/0.51  fof(f334,plain,(
% 0.21/0.51    r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3) | ~spl8_33),
% 0.21/0.51    inference(avatar_component_clause,[],[f333])).
% 0.21/0.51  fof(f333,plain,(
% 0.21/0.51    spl8_33 <=> r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).
% 0.21/0.51  fof(f335,plain,(
% 0.21/0.51    spl8_33 | ~spl8_2 | ~spl8_5 | spl8_7 | spl8_8 | spl8_12 | ~spl8_21),
% 0.21/0.51    inference(avatar_split_clause,[],[f309,f223,f135,f111,f94,f87,f65,f333])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    spl8_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    spl8_5 <=> r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    spl8_7 <=> v1_xboole_0(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    spl8_8 <=> v1_xboole_0(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.51  fof(f135,plain,(
% 0.21/0.51    spl8_12 <=> v1_xboole_0(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.21/0.51  fof(f223,plain,(
% 0.21/0.51    spl8_21 <=> m1_subset_1(sK4,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 0.21/0.51  fof(f309,plain,(
% 0.21/0.51    r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3) | (~spl8_2 | ~spl8_5 | spl8_7 | spl8_8 | spl8_12 | ~spl8_21)),
% 0.21/0.51    inference(subsumption_resolution,[],[f308,f224])).
% 0.21/0.51  fof(f224,plain,(
% 0.21/0.51    m1_subset_1(sK4,sK1) | ~spl8_21),
% 0.21/0.51    inference(avatar_component_clause,[],[f223])).
% 0.21/0.51  fof(f308,plain,(
% 0.21/0.51    ~m1_subset_1(sK4,sK1) | r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3) | (~spl8_2 | ~spl8_5 | spl8_7 | spl8_8 | spl8_12)),
% 0.21/0.51    inference(subsumption_resolution,[],[f305,f136])).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    ~v1_xboole_0(sK2) | spl8_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f135])).
% 0.21/0.51  fof(f305,plain,(
% 0.21/0.51    v1_xboole_0(sK2) | ~m1_subset_1(sK4,sK1) | r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3) | (~spl8_2 | ~spl8_5 | spl8_7 | spl8_8)),
% 0.21/0.51    inference(resolution,[],[f208,f88])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~spl8_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f87])).
% 0.21/0.51  fof(f208,plain,(
% 0.21/0.51    ( ! [X4,X3] : (~r2_hidden(X4,k9_relat_1(sK3,X3)) | v1_xboole_0(X3) | ~m1_subset_1(X4,sK1) | r2_hidden(k4_tarski(sK6(X3,sK0,sK3,X4),X4),sK3)) ) | (~spl8_2 | spl8_7 | spl8_8)),
% 0.21/0.51    inference(subsumption_resolution,[],[f207,f95])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    ~v1_xboole_0(sK1) | spl8_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f94])).
% 0.21/0.51  fof(f207,plain,(
% 0.21/0.51    ( ! [X4,X3] : (~r2_hidden(X4,k9_relat_1(sK3,X3)) | v1_xboole_0(X3) | ~m1_subset_1(X4,sK1) | r2_hidden(k4_tarski(sK6(X3,sK0,sK3,X4),X4),sK3) | v1_xboole_0(sK1)) ) | (~spl8_2 | spl8_8)),
% 0.21/0.51    inference(subsumption_resolution,[],[f206,f66])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl8_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f65])).
% 0.21/0.51  fof(f206,plain,(
% 0.21/0.51    ( ! [X4,X3] : (~r2_hidden(X4,k9_relat_1(sK3,X3)) | v1_xboole_0(X3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X4,sK1) | r2_hidden(k4_tarski(sK6(X3,sK0,sK3,X4),X4),sK3) | v1_xboole_0(sK1)) ) | (~spl8_2 | spl8_8)),
% 0.21/0.51    inference(subsumption_resolution,[],[f201,f112])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    ~v1_xboole_0(sK0) | spl8_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f111])).
% 0.21/0.51  fof(f201,plain,(
% 0.21/0.51    ( ! [X4,X3] : (~r2_hidden(X4,k9_relat_1(sK3,X3)) | v1_xboole_0(X3) | v1_xboole_0(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X4,sK1) | r2_hidden(k4_tarski(sK6(X3,sK0,sK3,X4),X4),sK3) | v1_xboole_0(sK1)) ) | ~spl8_2),
% 0.21/0.51    inference(superposition,[],[f49,f73])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ( ! [X4] : (k7_relset_1(sK0,sK1,sK3,X4) = k9_relat_1(sK3,X4)) ) | ~spl8_2),
% 0.21/0.51    inference(resolution,[],[f66,f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~m1_subset_1(X4,X0) | r2_hidden(k4_tarski(sK6(X1,X2,X3,X4),X4),X3) | v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relset_1)).
% 0.21/0.51  fof(f321,plain,(
% 0.21/0.51    spl8_32 | ~spl8_2 | ~spl8_5 | spl8_7 | spl8_8 | spl8_12 | ~spl8_21),
% 0.21/0.51    inference(avatar_split_clause,[],[f298,f223,f135,f111,f94,f87,f65,f319])).
% 0.21/0.51  fof(f298,plain,(
% 0.21/0.51    r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2) | (~spl8_2 | ~spl8_5 | spl8_7 | spl8_8 | spl8_12 | ~spl8_21)),
% 0.21/0.51    inference(subsumption_resolution,[],[f297,f224])).
% 0.21/0.51  fof(f297,plain,(
% 0.21/0.51    ~m1_subset_1(sK4,sK1) | r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2) | (~spl8_2 | ~spl8_5 | spl8_7 | spl8_8 | spl8_12)),
% 0.21/0.51    inference(subsumption_resolution,[],[f294,f136])).
% 0.21/0.51  fof(f294,plain,(
% 0.21/0.51    v1_xboole_0(sK2) | ~m1_subset_1(sK4,sK1) | r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2) | (~spl8_2 | ~spl8_5 | spl8_7 | spl8_8)),
% 0.21/0.51    inference(resolution,[],[f211,f88])).
% 0.21/0.51  fof(f211,plain,(
% 0.21/0.51    ( ! [X6,X5] : (~r2_hidden(X6,k9_relat_1(sK3,X5)) | v1_xboole_0(X5) | ~m1_subset_1(X6,sK1) | r2_hidden(sK6(X5,sK0,sK3,X6),X5)) ) | (~spl8_2 | spl8_7 | spl8_8)),
% 0.21/0.51    inference(subsumption_resolution,[],[f210,f95])).
% 0.21/0.51  fof(f210,plain,(
% 0.21/0.51    ( ! [X6,X5] : (~r2_hidden(X6,k9_relat_1(sK3,X5)) | v1_xboole_0(X5) | ~m1_subset_1(X6,sK1) | r2_hidden(sK6(X5,sK0,sK3,X6),X5) | v1_xboole_0(sK1)) ) | (~spl8_2 | spl8_8)),
% 0.21/0.51    inference(subsumption_resolution,[],[f209,f66])).
% 0.21/0.51  fof(f209,plain,(
% 0.21/0.51    ( ! [X6,X5] : (~r2_hidden(X6,k9_relat_1(sK3,X5)) | v1_xboole_0(X5) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X6,sK1) | r2_hidden(sK6(X5,sK0,sK3,X6),X5) | v1_xboole_0(sK1)) ) | (~spl8_2 | spl8_8)),
% 0.21/0.51    inference(subsumption_resolution,[],[f202,f112])).
% 0.21/0.51  fof(f202,plain,(
% 0.21/0.51    ( ! [X6,X5] : (~r2_hidden(X6,k9_relat_1(sK3,X5)) | v1_xboole_0(X5) | v1_xboole_0(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X6,sK1) | r2_hidden(sK6(X5,sK0,sK3,X6),X5) | v1_xboole_0(sK1)) ) | ~spl8_2),
% 0.21/0.51    inference(superposition,[],[f50,f73])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~m1_subset_1(X4,X0) | r2_hidden(sK6(X1,X2,X3,X4),X1) | v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f317,plain,(
% 0.21/0.51    spl8_31 | ~spl8_2 | ~spl8_5 | spl8_7 | spl8_8 | spl8_12 | ~spl8_21),
% 0.21/0.51    inference(avatar_split_clause,[],[f291,f223,f135,f111,f94,f87,f65,f315])).
% 0.21/0.51  fof(f291,plain,(
% 0.21/0.51    m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0) | (~spl8_2 | ~spl8_5 | spl8_7 | spl8_8 | spl8_12 | ~spl8_21)),
% 0.21/0.51    inference(subsumption_resolution,[],[f290,f224])).
% 0.21/0.51  fof(f290,plain,(
% 0.21/0.51    ~m1_subset_1(sK4,sK1) | m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0) | (~spl8_2 | ~spl8_5 | spl8_7 | spl8_8 | spl8_12)),
% 0.21/0.51    inference(subsumption_resolution,[],[f287,f136])).
% 0.21/0.51  fof(f287,plain,(
% 0.21/0.51    v1_xboole_0(sK2) | ~m1_subset_1(sK4,sK1) | m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0) | (~spl8_2 | ~spl8_5 | spl8_7 | spl8_8)),
% 0.21/0.51    inference(resolution,[],[f205,f88])).
% 0.21/0.51  fof(f205,plain,(
% 0.21/0.51    ( ! [X2,X1] : (~r2_hidden(X2,k9_relat_1(sK3,X1)) | v1_xboole_0(X1) | ~m1_subset_1(X2,sK1) | m1_subset_1(sK6(X1,sK0,sK3,X2),sK0)) ) | (~spl8_2 | spl8_7 | spl8_8)),
% 0.21/0.51    inference(subsumption_resolution,[],[f204,f95])).
% 0.21/0.51  fof(f204,plain,(
% 0.21/0.51    ( ! [X2,X1] : (~r2_hidden(X2,k9_relat_1(sK3,X1)) | v1_xboole_0(X1) | ~m1_subset_1(X2,sK1) | m1_subset_1(sK6(X1,sK0,sK3,X2),sK0) | v1_xboole_0(sK1)) ) | (~spl8_2 | spl8_8)),
% 0.21/0.51    inference(subsumption_resolution,[],[f203,f66])).
% 0.21/0.51  fof(f203,plain,(
% 0.21/0.51    ( ! [X2,X1] : (~r2_hidden(X2,k9_relat_1(sK3,X1)) | v1_xboole_0(X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X2,sK1) | m1_subset_1(sK6(X1,sK0,sK3,X2),sK0) | v1_xboole_0(sK1)) ) | (~spl8_2 | spl8_8)),
% 0.21/0.51    inference(subsumption_resolution,[],[f200,f112])).
% 0.21/0.51  fof(f200,plain,(
% 0.21/0.51    ( ! [X2,X1] : (~r2_hidden(X2,k9_relat_1(sK3,X1)) | v1_xboole_0(X1) | v1_xboole_0(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X2,sK1) | m1_subset_1(sK6(X1,sK0,sK3,X2),sK0) | v1_xboole_0(sK1)) ) | ~spl8_2),
% 0.21/0.51    inference(superposition,[],[f48,f73])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~m1_subset_1(X4,X0) | m1_subset_1(sK6(X1,X2,X3,X4),X2) | v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f225,plain,(
% 0.21/0.51    spl8_21 | ~spl8_2 | ~spl8_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f215,f87,f65,f223])).
% 0.21/0.51  fof(f215,plain,(
% 0.21/0.51    m1_subset_1(sK4,sK1) | (~spl8_2 | ~spl8_5)),
% 0.21/0.51    inference(resolution,[],[f199,f105])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(X0)) | m1_subset_1(sK4,X0)) ) | ~spl8_5),
% 0.21/0.51    inference(resolution,[],[f88,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.51    inference(flattening,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.51  fof(f199,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(sK1))) ) | ~spl8_2),
% 0.21/0.51    inference(superposition,[],[f72,f73])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    ( ! [X3] : (m1_subset_1(k7_relset_1(sK0,sK1,sK3,X3),k1_zfmisc_1(sK1))) ) | ~spl8_2),
% 0.21/0.51    inference(resolution,[],[f66,f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).
% 0.21/0.51  fof(f198,plain,(
% 0.21/0.51    ~spl8_6 | ~spl8_18),
% 0.21/0.51    inference(avatar_split_clause,[],[f188,f178,f91])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    spl8_6 <=> v1_xboole_0(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.51  fof(f178,plain,(
% 0.21/0.51    spl8_18 <=> r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.21/0.51  fof(f188,plain,(
% 0.21/0.51    ~v1_xboole_0(sK3) | ~spl8_18),
% 0.21/0.51    inference(resolution,[],[f179,f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.51  fof(f179,plain,(
% 0.21/0.51    r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3) | ~spl8_18),
% 0.21/0.51    inference(avatar_component_clause,[],[f178])).
% 0.21/0.51  fof(f180,plain,(
% 0.21/0.51    spl8_18 | ~spl8_3 | ~spl8_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f107,f87,f78,f178])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3) | (~spl8_3 | ~spl8_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f100,f79])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3) | ~v1_relat_1(sK3) | ~spl8_5),
% 0.21/0.51    inference(resolution,[],[f88,f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK7(X0,X1,X2),X0),X2) | ~v1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 0.21/0.51  fof(f137,plain,(
% 0.21/0.51    ~spl8_12 | ~spl8_11),
% 0.21/0.51    inference(avatar_split_clause,[],[f129,f126,f135])).
% 0.21/0.51  fof(f126,plain,(
% 0.21/0.51    spl8_11 <=> r2_hidden(sK7(sK4,sK2,sK3),sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.21/0.51  fof(f129,plain,(
% 0.21/0.51    ~v1_xboole_0(sK2) | ~spl8_11),
% 0.21/0.51    inference(resolution,[],[f127,f46])).
% 0.21/0.51  fof(f127,plain,(
% 0.21/0.51    r2_hidden(sK7(sK4,sK2,sK3),sK2) | ~spl8_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f126])).
% 0.21/0.51  fof(f128,plain,(
% 0.21/0.51    spl8_11 | ~spl8_3 | ~spl8_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f108,f87,f78,f126])).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    r2_hidden(sK7(sK4,sK2,sK3),sK2) | (~spl8_3 | ~spl8_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f101,f79])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    r2_hidden(sK7(sK4,sK2,sK3),sK2) | ~v1_relat_1(sK3) | ~spl8_5),
% 0.21/0.51    inference(resolution,[],[f88,f56])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK7(X0,X1,X2),X1) | ~v1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    spl8_6 | ~spl8_8 | ~spl8_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f70,f65,f111,f91])).
% 1.20/0.51  fof(f70,plain,(
% 1.20/0.51    ~v1_xboole_0(sK0) | v1_xboole_0(sK3) | ~spl8_2),
% 1.20/0.51    inference(resolution,[],[f66,f52])).
% 1.20/0.51  fof(f52,plain,(
% 1.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0) | v1_xboole_0(X2)) )),
% 1.20/0.51    inference(cnf_transformation,[],[f27])).
% 1.20/0.51  fof(f27,plain,(
% 1.20/0.51    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 1.20/0.51    inference(ennf_transformation,[],[f8])).
% 1.20/0.51  fof(f8,axiom,(
% 1.20/0.51    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 1.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).
% 1.20/0.51  fof(f96,plain,(
% 1.20/0.51    spl8_6 | ~spl8_7 | ~spl8_2),
% 1.20/0.51    inference(avatar_split_clause,[],[f69,f65,f94,f91])).
% 1.20/0.51  fof(f69,plain,(
% 1.20/0.51    ~v1_xboole_0(sK1) | v1_xboole_0(sK3) | ~spl8_2),
% 1.20/0.51    inference(resolution,[],[f66,f53])).
% 1.20/0.51  fof(f53,plain,(
% 1.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0) | v1_xboole_0(X2)) )),
% 1.20/0.51    inference(cnf_transformation,[],[f28])).
% 1.20/0.51  fof(f28,plain,(
% 1.20/0.51    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 1.20/0.51    inference(ennf_transformation,[],[f9])).
% 1.20/0.51  fof(f9,axiom,(
% 1.20/0.51    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 1.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 1.20/0.51  fof(f89,plain,(
% 1.20/0.51    spl8_5 | ~spl8_2 | ~spl8_4),
% 1.20/0.51    inference(avatar_split_clause,[],[f85,f82,f65,f87])).
% 1.20/0.51  fof(f82,plain,(
% 1.20/0.51    spl8_4 <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 1.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.20/0.51  fof(f85,plain,(
% 1.20/0.51    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | (~spl8_2 | ~spl8_4)),
% 1.20/0.51    inference(forward_demodulation,[],[f83,f73])).
% 1.20/0.51  fof(f83,plain,(
% 1.20/0.51    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) | ~spl8_4),
% 1.20/0.51    inference(avatar_component_clause,[],[f82])).
% 1.20/0.51  fof(f84,plain,(
% 1.20/0.51    spl8_4),
% 1.20/0.51    inference(avatar_split_clause,[],[f32,f82])).
% 1.20/0.51  fof(f32,plain,(
% 1.20/0.51    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 1.20/0.51    inference(cnf_transformation,[],[f17])).
% 1.20/0.51  fof(f80,plain,(
% 1.20/0.51    spl8_3 | ~spl8_2),
% 1.20/0.51    inference(avatar_split_clause,[],[f68,f65,f78])).
% 1.20/0.51  fof(f68,plain,(
% 1.20/0.51    v1_relat_1(sK3) | ~spl8_2),
% 1.20/0.51    inference(resolution,[],[f66,f58])).
% 1.20/0.51  fof(f58,plain,(
% 1.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.20/0.51    inference(cnf_transformation,[],[f30])).
% 1.20/0.51  fof(f30,plain,(
% 1.20/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.20/0.51    inference(ennf_transformation,[],[f7])).
% 1.20/0.51  fof(f7,axiom,(
% 1.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.20/0.51  fof(f67,plain,(
% 1.20/0.51    spl8_2),
% 1.20/0.51    inference(avatar_split_clause,[],[f34,f65])).
% 1.20/0.51  fof(f34,plain,(
% 1.20/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.20/0.51    inference(cnf_transformation,[],[f17])).
% 1.20/0.51  fof(f63,plain,(
% 1.20/0.51    spl8_1),
% 1.20/0.51    inference(avatar_split_clause,[],[f33,f61])).
% 1.20/0.51  fof(f33,plain,(
% 1.20/0.51    v1_funct_1(sK3)),
% 1.20/0.51    inference(cnf_transformation,[],[f17])).
% 1.20/0.51  % SZS output end Proof for theBenchmark
% 1.20/0.51  % (22090)------------------------------
% 1.20/0.51  % (22090)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.51  % (22090)Termination reason: Refutation
% 1.20/0.51  
% 1.20/0.51  % (22090)Memory used [KB]: 6396
% 1.20/0.51  % (22090)Time elapsed: 0.096 s
% 1.20/0.51  % (22090)------------------------------
% 1.20/0.51  % (22090)------------------------------
% 1.20/0.51  % (22108)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 1.20/0.51  % (22097)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 1.20/0.52  % (22102)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.20/0.52  % (22100)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 1.36/0.53  % (22101)Refutation not found, incomplete strategy% (22101)------------------------------
% 1.36/0.53  % (22101)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.53  % (22101)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.53  
% 1.36/0.53  % (22101)Memory used [KB]: 11257
% 1.36/0.53  % (22101)Time elapsed: 0.114 s
% 1.36/0.53  % (22101)------------------------------
% 1.36/0.53  % (22101)------------------------------
% 1.36/0.53  % (22089)Success in time 0.172 s
%------------------------------------------------------------------------------
