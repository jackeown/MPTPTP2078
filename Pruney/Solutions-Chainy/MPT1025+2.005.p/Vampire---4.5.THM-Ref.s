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
% DateTime   : Thu Dec  3 13:06:21 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 294 expanded)
%              Number of leaves         :   28 ( 119 expanded)
%              Depth                    :   12
%              Number of atoms          :  513 ( 921 expanded)
%              Number of equality atoms :   18 (  53 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f288,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f62,f73,f77,f82,f89,f103,f111,f117,f136,f143,f168,f179,f220,f231,f234,f269,f287])).

fof(f287,plain,
    ( ~ spl9_1
    | ~ spl9_3
    | ~ spl9_22
    | ~ spl9_23
    | ~ spl9_25 ),
    inference(avatar_contradiction_clause,[],[f286])).

fof(f286,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_3
    | ~ spl9_22
    | ~ spl9_23
    | ~ spl9_25 ),
    inference(subsumption_resolution,[],[f285,f72])).

fof(f72,plain,
    ( v1_relat_1(sK3)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl9_3
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f285,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl9_1
    | ~ spl9_22
    | ~ spl9_23
    | ~ spl9_25 ),
    inference(subsumption_resolution,[],[f284,f247])).

fof(f247,plain,
    ( sK4 != k1_funct_1(sK3,sK6(sK2,sK0,sK3,sK4))
    | ~ spl9_22
    | ~ spl9_23 ),
    inference(subsumption_resolution,[],[f246,f230])).

fof(f230,plain,
    ( r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2)
    | ~ spl9_23 ),
    inference(avatar_component_clause,[],[f229])).

fof(f229,plain,
    ( spl9_23
  <=> r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f246,plain,
    ( ~ r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2)
    | sK4 != k1_funct_1(sK3,sK6(sK2,sK0,sK3,sK4))
    | ~ spl9_22 ),
    inference(resolution,[],[f219,f29])).

fof(f29,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,sK0)
      | ~ r2_hidden(X5,sK2)
      | sK4 != k1_funct_1(sK3,X5) ) ),
    inference(cnf_transformation,[],[f16])).

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
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).

fof(f219,plain,
    ( m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0)
    | ~ spl9_22 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl9_22
  <=> m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f284,plain,
    ( sK4 = k1_funct_1(sK3,sK6(sK2,sK0,sK3,sK4))
    | ~ v1_relat_1(sK3)
    | ~ spl9_1
    | ~ spl9_25 ),
    inference(subsumption_resolution,[],[f277,f57])).

fof(f57,plain,
    ( v1_funct_1(sK3)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl9_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f277,plain,
    ( ~ v1_funct_1(sK3)
    | sK4 = k1_funct_1(sK3,sK6(sK2,sK0,sK3,sK4))
    | ~ v1_relat_1(sK3)
    | ~ spl9_25 ),
    inference(resolution,[],[f268,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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

fof(f268,plain,
    ( r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3)
    | ~ spl9_25 ),
    inference(avatar_component_clause,[],[f267])).

fof(f267,plain,
    ( spl9_25
  <=> r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f269,plain,
    ( spl9_25
    | ~ spl9_2
    | ~ spl9_5
    | spl9_7
    | spl9_11
    | spl9_15
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f259,f177,f138,f115,f87,f80,f60,f267])).

fof(f60,plain,
    ( spl9_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f80,plain,
    ( spl9_5
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f87,plain,
    ( spl9_7
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f115,plain,
    ( spl9_11
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f138,plain,
    ( spl9_15
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f177,plain,
    ( spl9_18
  <=> m1_subset_1(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f259,plain,
    ( r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3)
    | ~ spl9_2
    | ~ spl9_5
    | spl9_7
    | spl9_11
    | spl9_15
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f258,f178])).

fof(f178,plain,
    ( m1_subset_1(sK4,sK1)
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f177])).

fof(f258,plain,
    ( ~ m1_subset_1(sK4,sK1)
    | r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3)
    | ~ spl9_2
    | ~ spl9_5
    | spl9_7
    | spl9_11
    | spl9_15 ),
    inference(subsumption_resolution,[],[f255,f116])).

fof(f116,plain,
    ( ~ v1_xboole_0(sK2)
    | spl9_11 ),
    inference(avatar_component_clause,[],[f115])).

fof(f255,plain,
    ( v1_xboole_0(sK2)
    | ~ m1_subset_1(sK4,sK1)
    | r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3)
    | ~ spl9_2
    | ~ spl9_5
    | spl9_7
    | spl9_15 ),
    inference(resolution,[],[f238,f81])).

fof(f81,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f80])).

fof(f238,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X4,k9_relat_1(sK3,X3))
        | v1_xboole_0(X3)
        | ~ m1_subset_1(X4,sK1)
        | r2_hidden(k4_tarski(sK6(X3,sK0,sK3,X4),X4),sK3) )
    | ~ spl9_2
    | spl9_7
    | spl9_15 ),
    inference(subsumption_resolution,[],[f162,f139])).

fof(f139,plain,
    ( ~ v1_xboole_0(sK1)
    | spl9_15 ),
    inference(avatar_component_clause,[],[f138])).

fof(f162,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X4,k9_relat_1(sK3,X3))
        | v1_xboole_0(X3)
        | ~ m1_subset_1(X4,sK1)
        | r2_hidden(k4_tarski(sK6(X3,sK0,sK3,X4),X4),sK3)
        | v1_xboole_0(sK1) )
    | ~ spl9_2
    | spl9_7 ),
    inference(subsumption_resolution,[],[f161,f61])).

fof(f61,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f161,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X4,k9_relat_1(sK3,X3))
        | v1_xboole_0(X3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(X4,sK1)
        | r2_hidden(k4_tarski(sK6(X3,sK0,sK3,X4),X4),sK3)
        | v1_xboole_0(sK1) )
    | ~ spl9_2
    | spl9_7 ),
    inference(subsumption_resolution,[],[f156,f88])).

fof(f88,plain,
    ( ~ v1_xboole_0(sK0)
    | spl9_7 ),
    inference(avatar_component_clause,[],[f87])).

fof(f156,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X4,k9_relat_1(sK3,X3))
        | v1_xboole_0(X3)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(X4,sK1)
        | r2_hidden(k4_tarski(sK6(X3,sK0,sK3,X4),X4),sK3)
        | v1_xboole_0(sK1) )
    | ~ spl9_2 ),
    inference(superposition,[],[f41,f67])).

fof(f67,plain,
    ( ! [X4] : k7_relset_1(sK0,sK1,sK3,X4) = k9_relat_1(sK3,X4)
    | ~ spl9_2 ),
    inference(resolution,[],[f61,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

% (10384)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ m1_subset_1(X4,X0)
      | r2_hidden(k4_tarski(sK6(X1,X2,X3,X4),X4),X3)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relset_1)).

fof(f234,plain,
    ( spl9_8
    | ~ spl9_16 ),
    inference(avatar_contradiction_clause,[],[f232])).

fof(f232,plain,
    ( $false
    | spl9_8
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f102,f142])).

fof(f142,plain,
    ( ! [X0] : v1_xboole_0(k9_relat_1(sK3,X0))
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl9_16
  <=> ! [X0] : v1_xboole_0(k9_relat_1(sK3,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f102,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK3,sK2))
    | spl9_8 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl9_8
  <=> v1_xboole_0(k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f231,plain,
    ( spl9_23
    | ~ spl9_2
    | ~ spl9_5
    | spl9_7
    | spl9_11
    | spl9_15
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f214,f177,f138,f115,f87,f80,f60,f229])).

fof(f214,plain,
    ( r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2)
    | ~ spl9_2
    | ~ spl9_5
    | spl9_7
    | spl9_11
    | spl9_15
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f213,f178])).

fof(f213,plain,
    ( ~ m1_subset_1(sK4,sK1)
    | r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2)
    | ~ spl9_2
    | ~ spl9_5
    | spl9_7
    | spl9_11
    | spl9_15 ),
    inference(subsumption_resolution,[],[f210,f116])).

fof(f210,plain,
    ( v1_xboole_0(sK2)
    | ~ m1_subset_1(sK4,sK1)
    | r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2)
    | ~ spl9_2
    | ~ spl9_5
    | spl9_7
    | spl9_15 ),
    inference(resolution,[],[f166,f81])).

fof(f166,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(X6,k9_relat_1(sK3,X5))
        | v1_xboole_0(X5)
        | ~ m1_subset_1(X6,sK1)
        | r2_hidden(sK6(X5,sK0,sK3,X6),X5) )
    | ~ spl9_2
    | spl9_7
    | spl9_15 ),
    inference(subsumption_resolution,[],[f165,f139])).

fof(f165,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(X6,k9_relat_1(sK3,X5))
        | v1_xboole_0(X5)
        | ~ m1_subset_1(X6,sK1)
        | r2_hidden(sK6(X5,sK0,sK3,X6),X5)
        | v1_xboole_0(sK1) )
    | ~ spl9_2
    | spl9_7 ),
    inference(subsumption_resolution,[],[f164,f61])).

fof(f164,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(X6,k9_relat_1(sK3,X5))
        | v1_xboole_0(X5)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(X6,sK1)
        | r2_hidden(sK6(X5,sK0,sK3,X6),X5)
        | v1_xboole_0(sK1) )
    | ~ spl9_2
    | spl9_7 ),
    inference(subsumption_resolution,[],[f157,f88])).

fof(f157,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(X6,k9_relat_1(sK3,X5))
        | v1_xboole_0(X5)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(X6,sK1)
        | r2_hidden(sK6(X5,sK0,sK3,X6),X5)
        | v1_xboole_0(sK1) )
    | ~ spl9_2 ),
    inference(superposition,[],[f42,f67])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ m1_subset_1(X4,X0)
      | r2_hidden(sK6(X1,X2,X3,X4),X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f220,plain,
    ( spl9_22
    | ~ spl9_2
    | ~ spl9_5
    | spl9_7
    | spl9_11
    | spl9_15
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f207,f177,f138,f115,f87,f80,f60,f218])).

fof(f207,plain,
    ( m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0)
    | ~ spl9_2
    | ~ spl9_5
    | spl9_7
    | spl9_11
    | spl9_15
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f206,f178])).

fof(f206,plain,
    ( ~ m1_subset_1(sK4,sK1)
    | m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0)
    | ~ spl9_2
    | ~ spl9_5
    | spl9_7
    | spl9_11
    | spl9_15 ),
    inference(subsumption_resolution,[],[f203,f116])).

fof(f203,plain,
    ( v1_xboole_0(sK2)
    | ~ m1_subset_1(sK4,sK1)
    | m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0)
    | ~ spl9_2
    | ~ spl9_5
    | spl9_7
    | spl9_15 ),
    inference(resolution,[],[f160,f81])).

fof(f160,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X2,k9_relat_1(sK3,X1))
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X2,sK1)
        | m1_subset_1(sK6(X1,sK0,sK3,X2),sK0) )
    | ~ spl9_2
    | spl9_7
    | spl9_15 ),
    inference(subsumption_resolution,[],[f159,f139])).

fof(f159,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X2,k9_relat_1(sK3,X1))
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X2,sK1)
        | m1_subset_1(sK6(X1,sK0,sK3,X2),sK0)
        | v1_xboole_0(sK1) )
    | ~ spl9_2
    | spl9_7 ),
    inference(subsumption_resolution,[],[f158,f61])).

fof(f158,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X2,k9_relat_1(sK3,X1))
        | v1_xboole_0(X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(X2,sK1)
        | m1_subset_1(sK6(X1,sK0,sK3,X2),sK0)
        | v1_xboole_0(sK1) )
    | ~ spl9_2
    | spl9_7 ),
    inference(subsumption_resolution,[],[f155,f88])).

fof(f155,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X2,k9_relat_1(sK3,X1))
        | v1_xboole_0(X1)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(X2,sK1)
        | m1_subset_1(sK6(X1,sK0,sK3,X2),sK0)
        | v1_xboole_0(sK1) )
    | ~ spl9_2 ),
    inference(superposition,[],[f40,f67])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ m1_subset_1(X4,X0)
      | m1_subset_1(sK6(X1,X2,X3,X4),X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f179,plain,
    ( spl9_18
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f170,f80,f60,f177])).

fof(f170,plain,
    ( m1_subset_1(sK4,sK1)
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(resolution,[],[f154,f96])).

fof(f96,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(X0))
        | m1_subset_1(sK4,X0) )
    | ~ spl9_5 ),
    inference(resolution,[],[f81,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f154,plain,
    ( ! [X0] : m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(sK1))
    | ~ spl9_2 ),
    inference(superposition,[],[f65,f67])).

fof(f65,plain,
    ( ! [X0] : m1_subset_1(k7_relset_1(sK0,sK1,sK3,X0),k1_zfmisc_1(sK1))
    | ~ spl9_2 ),
    inference(resolution,[],[f61,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(f168,plain,
    ( ~ spl9_6
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f148,f134,f84])).

fof(f84,plain,
    ( spl9_6
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f134,plain,
    ( spl9_14
  <=> r2_hidden(k4_tarski(sK8(sK4,sK2,sK3),sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f148,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl9_14 ),
    inference(resolution,[],[f135,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f135,plain,
    ( r2_hidden(k4_tarski(sK8(sK4,sK2,sK3),sK4),sK3)
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f134])).

fof(f143,plain,
    ( ~ spl9_15
    | spl9_16
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f132,f60,f141,f138])).

fof(f132,plain,
    ( ! [X0] :
        ( v1_xboole_0(k9_relat_1(sK3,X0))
        | ~ v1_xboole_0(sK1) )
    | ~ spl9_2 ),
    inference(forward_demodulation,[],[f131,f67])).

fof(f131,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(sK1)
        | v1_xboole_0(k7_relset_1(sK0,sK1,sK3,X0)) )
    | ~ spl9_2 ),
    inference(resolution,[],[f65,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f136,plain,
    ( spl9_14
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f98,f80,f71,f134])).

fof(f98,plain,
    ( r2_hidden(k4_tarski(sK8(sK4,sK2,sK3),sK4),sK3)
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f93,f72])).

fof(f93,plain,
    ( r2_hidden(k4_tarski(sK8(sK4,sK2,sK3),sK4),sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl9_5 ),
    inference(resolution,[],[f81,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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

fof(f117,plain,
    ( ~ spl9_11
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f112,f109,f115])).

fof(f109,plain,
    ( spl9_10
  <=> r2_hidden(sK8(sK4,sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f112,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl9_10 ),
    inference(resolution,[],[f110,f39])).

fof(f110,plain,
    ( r2_hidden(sK8(sK4,sK2,sK3),sK2)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f109])).

fof(f111,plain,
    ( spl9_10
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f99,f80,f71,f109])).

fof(f99,plain,
    ( r2_hidden(sK8(sK4,sK2,sK3),sK2)
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f94,f72])).

fof(f94,plain,
    ( r2_hidden(sK8(sK4,sK2,sK3),sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl9_5 ),
    inference(resolution,[],[f81,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK8(X0,X1,X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f103,plain,
    ( ~ spl9_8
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f95,f80,f101])).

fof(f95,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK3,sK2))
    | ~ spl9_5 ),
    inference(resolution,[],[f81,f39])).

fof(f89,plain,
    ( spl9_6
    | ~ spl9_7
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f64,f60,f87,f84])).

fof(f64,plain,
    ( ~ v1_xboole_0(sK0)
    | v1_xboole_0(sK3)
    | ~ spl9_2 ),
    inference(resolution,[],[f61,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f82,plain,
    ( spl9_5
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f78,f75,f60,f80])).

fof(f75,plain,
    ( spl9_4
  <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f78,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(forward_demodulation,[],[f76,f67])).

fof(f76,plain,
    ( r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f75])).

fof(f77,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f30,f75])).

fof(f30,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f73,plain,
    ( spl9_3
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f63,f60,f71])).

fof(f63,plain,
    ( v1_relat_1(sK3)
    | ~ spl9_2 ),
    inference(resolution,[],[f61,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f62,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f32,f60])).

fof(f32,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f58,plain,(
    spl9_1 ),
    inference(avatar_split_clause,[],[f31,f56])).

fof(f31,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:02:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (10395)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.47  % (10387)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.47  % (10392)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.48  % (10381)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.48  % (10400)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.48  % (10381)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.49  % (10386)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (10388)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f288,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f58,f62,f73,f77,f82,f89,f103,f111,f117,f136,f143,f168,f179,f220,f231,f234,f269,f287])).
% 0.22/0.49  fof(f287,plain,(
% 0.22/0.49    ~spl9_1 | ~spl9_3 | ~spl9_22 | ~spl9_23 | ~spl9_25),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f286])).
% 0.22/0.49  fof(f286,plain,(
% 0.22/0.49    $false | (~spl9_1 | ~spl9_3 | ~spl9_22 | ~spl9_23 | ~spl9_25)),
% 0.22/0.49    inference(subsumption_resolution,[],[f285,f72])).
% 0.22/0.49  fof(f72,plain,(
% 0.22/0.49    v1_relat_1(sK3) | ~spl9_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f71])).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    spl9_3 <=> v1_relat_1(sK3)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.22/0.49  fof(f285,plain,(
% 0.22/0.49    ~v1_relat_1(sK3) | (~spl9_1 | ~spl9_22 | ~spl9_23 | ~spl9_25)),
% 0.22/0.49    inference(subsumption_resolution,[],[f284,f247])).
% 0.22/0.49  fof(f247,plain,(
% 0.22/0.49    sK4 != k1_funct_1(sK3,sK6(sK2,sK0,sK3,sK4)) | (~spl9_22 | ~spl9_23)),
% 0.22/0.49    inference(subsumption_resolution,[],[f246,f230])).
% 0.22/0.49  fof(f230,plain,(
% 0.22/0.49    r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2) | ~spl9_23),
% 0.22/0.49    inference(avatar_component_clause,[],[f229])).
% 0.22/0.49  fof(f229,plain,(
% 0.22/0.49    spl9_23 <=> r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).
% 0.22/0.49  fof(f246,plain,(
% 0.22/0.49    ~r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2) | sK4 != k1_funct_1(sK3,sK6(sK2,sK0,sK3,sK4)) | ~spl9_22),
% 0.22/0.49    inference(resolution,[],[f219,f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ( ! [X5] : (~m1_subset_1(X5,sK0) | ~r2_hidden(X5,sK2) | sK4 != k1_funct_1(sK3,X5)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 0.22/0.49    inference(flattening,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 0.22/0.49    inference(ennf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.22/0.49    inference(pure_predicate_removal,[],[f13])).
% 0.22/0.49  fof(f13,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.22/0.49    inference(negated_conjecture,[],[f12])).
% 0.22/0.49  fof(f12,conjecture,(
% 0.22/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).
% 0.22/0.49  fof(f219,plain,(
% 0.22/0.49    m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0) | ~spl9_22),
% 0.22/0.49    inference(avatar_component_clause,[],[f218])).
% 0.22/0.49  fof(f218,plain,(
% 0.22/0.49    spl9_22 <=> m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).
% 0.22/0.49  fof(f284,plain,(
% 0.22/0.49    sK4 = k1_funct_1(sK3,sK6(sK2,sK0,sK3,sK4)) | ~v1_relat_1(sK3) | (~spl9_1 | ~spl9_25)),
% 0.22/0.49    inference(subsumption_resolution,[],[f277,f57])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    v1_funct_1(sK3) | ~spl9_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f56])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    spl9_1 <=> v1_funct_1(sK3)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.22/0.49  fof(f277,plain,(
% 0.22/0.49    ~v1_funct_1(sK3) | sK4 = k1_funct_1(sK3,sK6(sK2,sK0,sK3,sK4)) | ~v1_relat_1(sK3) | ~spl9_25),
% 0.22/0.49    inference(resolution,[],[f268,f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.49    inference(flattening,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 0.22/0.49  fof(f268,plain,(
% 0.22/0.49    r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3) | ~spl9_25),
% 0.22/0.49    inference(avatar_component_clause,[],[f267])).
% 0.22/0.49  fof(f267,plain,(
% 0.22/0.49    spl9_25 <=> r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).
% 0.22/0.49  fof(f269,plain,(
% 0.22/0.49    spl9_25 | ~spl9_2 | ~spl9_5 | spl9_7 | spl9_11 | spl9_15 | ~spl9_18),
% 0.22/0.49    inference(avatar_split_clause,[],[f259,f177,f138,f115,f87,f80,f60,f267])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    spl9_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.22/0.49  fof(f80,plain,(
% 0.22/0.49    spl9_5 <=> r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.22/0.49  fof(f87,plain,(
% 0.22/0.49    spl9_7 <=> v1_xboole_0(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.22/0.49  fof(f115,plain,(
% 0.22/0.49    spl9_11 <=> v1_xboole_0(sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 0.22/0.49  fof(f138,plain,(
% 0.22/0.49    spl9_15 <=> v1_xboole_0(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 0.22/0.49  fof(f177,plain,(
% 0.22/0.49    spl9_18 <=> m1_subset_1(sK4,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 0.22/0.49  fof(f259,plain,(
% 0.22/0.49    r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3) | (~spl9_2 | ~spl9_5 | spl9_7 | spl9_11 | spl9_15 | ~spl9_18)),
% 0.22/0.49    inference(subsumption_resolution,[],[f258,f178])).
% 0.22/0.49  fof(f178,plain,(
% 0.22/0.49    m1_subset_1(sK4,sK1) | ~spl9_18),
% 0.22/0.49    inference(avatar_component_clause,[],[f177])).
% 0.22/0.49  fof(f258,plain,(
% 0.22/0.49    ~m1_subset_1(sK4,sK1) | r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3) | (~spl9_2 | ~spl9_5 | spl9_7 | spl9_11 | spl9_15)),
% 0.22/0.49    inference(subsumption_resolution,[],[f255,f116])).
% 0.22/0.49  fof(f116,plain,(
% 0.22/0.49    ~v1_xboole_0(sK2) | spl9_11),
% 0.22/0.49    inference(avatar_component_clause,[],[f115])).
% 0.22/0.49  fof(f255,plain,(
% 0.22/0.49    v1_xboole_0(sK2) | ~m1_subset_1(sK4,sK1) | r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3) | (~spl9_2 | ~spl9_5 | spl9_7 | spl9_15)),
% 0.22/0.49    inference(resolution,[],[f238,f81])).
% 0.22/0.49  fof(f81,plain,(
% 0.22/0.49    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~spl9_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f80])).
% 0.22/0.49  fof(f238,plain,(
% 0.22/0.49    ( ! [X4,X3] : (~r2_hidden(X4,k9_relat_1(sK3,X3)) | v1_xboole_0(X3) | ~m1_subset_1(X4,sK1) | r2_hidden(k4_tarski(sK6(X3,sK0,sK3,X4),X4),sK3)) ) | (~spl9_2 | spl9_7 | spl9_15)),
% 0.22/0.49    inference(subsumption_resolution,[],[f162,f139])).
% 0.22/0.49  fof(f139,plain,(
% 0.22/0.49    ~v1_xboole_0(sK1) | spl9_15),
% 0.22/0.49    inference(avatar_component_clause,[],[f138])).
% 0.22/0.49  fof(f162,plain,(
% 0.22/0.49    ( ! [X4,X3] : (~r2_hidden(X4,k9_relat_1(sK3,X3)) | v1_xboole_0(X3) | ~m1_subset_1(X4,sK1) | r2_hidden(k4_tarski(sK6(X3,sK0,sK3,X4),X4),sK3) | v1_xboole_0(sK1)) ) | (~spl9_2 | spl9_7)),
% 0.22/0.49    inference(subsumption_resolution,[],[f161,f61])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl9_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f60])).
% 0.22/0.49  fof(f161,plain,(
% 0.22/0.49    ( ! [X4,X3] : (~r2_hidden(X4,k9_relat_1(sK3,X3)) | v1_xboole_0(X3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X4,sK1) | r2_hidden(k4_tarski(sK6(X3,sK0,sK3,X4),X4),sK3) | v1_xboole_0(sK1)) ) | (~spl9_2 | spl9_7)),
% 0.22/0.49    inference(subsumption_resolution,[],[f156,f88])).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    ~v1_xboole_0(sK0) | spl9_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f87])).
% 0.22/0.49  fof(f156,plain,(
% 0.22/0.49    ( ! [X4,X3] : (~r2_hidden(X4,k9_relat_1(sK3,X3)) | v1_xboole_0(X3) | v1_xboole_0(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X4,sK1) | r2_hidden(k4_tarski(sK6(X3,sK0,sK3,X4),X4),sK3) | v1_xboole_0(sK1)) ) | ~spl9_2),
% 0.22/0.49    inference(superposition,[],[f41,f67])).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    ( ! [X4] : (k7_relset_1(sK0,sK1,sK3,X4) = k9_relat_1(sK3,X4)) ) | ~spl9_2),
% 0.22/0.49    inference(resolution,[],[f61,f33])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.49  % (10384)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~m1_subset_1(X4,X0) | r2_hidden(k4_tarski(sK6(X1,X2,X3,X4),X4),X3) | v1_xboole_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,axiom,(
% 0.22/0.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relset_1)).
% 0.22/0.49  fof(f234,plain,(
% 0.22/0.49    spl9_8 | ~spl9_16),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f232])).
% 0.22/0.49  fof(f232,plain,(
% 0.22/0.49    $false | (spl9_8 | ~spl9_16)),
% 0.22/0.49    inference(subsumption_resolution,[],[f102,f142])).
% 0.22/0.49  fof(f142,plain,(
% 0.22/0.49    ( ! [X0] : (v1_xboole_0(k9_relat_1(sK3,X0))) ) | ~spl9_16),
% 0.22/0.49    inference(avatar_component_clause,[],[f141])).
% 0.22/0.49  fof(f141,plain,(
% 0.22/0.49    spl9_16 <=> ! [X0] : v1_xboole_0(k9_relat_1(sK3,X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 0.22/0.49  fof(f102,plain,(
% 0.22/0.49    ~v1_xboole_0(k9_relat_1(sK3,sK2)) | spl9_8),
% 0.22/0.49    inference(avatar_component_clause,[],[f101])).
% 0.22/0.49  fof(f101,plain,(
% 0.22/0.49    spl9_8 <=> v1_xboole_0(k9_relat_1(sK3,sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.22/0.49  fof(f231,plain,(
% 0.22/0.49    spl9_23 | ~spl9_2 | ~spl9_5 | spl9_7 | spl9_11 | spl9_15 | ~spl9_18),
% 0.22/0.49    inference(avatar_split_clause,[],[f214,f177,f138,f115,f87,f80,f60,f229])).
% 0.22/0.49  fof(f214,plain,(
% 0.22/0.49    r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2) | (~spl9_2 | ~spl9_5 | spl9_7 | spl9_11 | spl9_15 | ~spl9_18)),
% 0.22/0.49    inference(subsumption_resolution,[],[f213,f178])).
% 0.22/0.49  fof(f213,plain,(
% 0.22/0.49    ~m1_subset_1(sK4,sK1) | r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2) | (~spl9_2 | ~spl9_5 | spl9_7 | spl9_11 | spl9_15)),
% 0.22/0.49    inference(subsumption_resolution,[],[f210,f116])).
% 0.22/0.49  fof(f210,plain,(
% 0.22/0.49    v1_xboole_0(sK2) | ~m1_subset_1(sK4,sK1) | r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2) | (~spl9_2 | ~spl9_5 | spl9_7 | spl9_15)),
% 0.22/0.49    inference(resolution,[],[f166,f81])).
% 0.22/0.49  fof(f166,plain,(
% 0.22/0.49    ( ! [X6,X5] : (~r2_hidden(X6,k9_relat_1(sK3,X5)) | v1_xboole_0(X5) | ~m1_subset_1(X6,sK1) | r2_hidden(sK6(X5,sK0,sK3,X6),X5)) ) | (~spl9_2 | spl9_7 | spl9_15)),
% 0.22/0.49    inference(subsumption_resolution,[],[f165,f139])).
% 0.22/0.49  fof(f165,plain,(
% 0.22/0.49    ( ! [X6,X5] : (~r2_hidden(X6,k9_relat_1(sK3,X5)) | v1_xboole_0(X5) | ~m1_subset_1(X6,sK1) | r2_hidden(sK6(X5,sK0,sK3,X6),X5) | v1_xboole_0(sK1)) ) | (~spl9_2 | spl9_7)),
% 0.22/0.49    inference(subsumption_resolution,[],[f164,f61])).
% 0.22/0.49  fof(f164,plain,(
% 0.22/0.49    ( ! [X6,X5] : (~r2_hidden(X6,k9_relat_1(sK3,X5)) | v1_xboole_0(X5) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X6,sK1) | r2_hidden(sK6(X5,sK0,sK3,X6),X5) | v1_xboole_0(sK1)) ) | (~spl9_2 | spl9_7)),
% 0.22/0.49    inference(subsumption_resolution,[],[f157,f88])).
% 0.22/0.49  fof(f157,plain,(
% 0.22/0.49    ( ! [X6,X5] : (~r2_hidden(X6,k9_relat_1(sK3,X5)) | v1_xboole_0(X5) | v1_xboole_0(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X6,sK1) | r2_hidden(sK6(X5,sK0,sK3,X6),X5) | v1_xboole_0(sK1)) ) | ~spl9_2),
% 0.22/0.49    inference(superposition,[],[f42,f67])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~m1_subset_1(X4,X0) | r2_hidden(sK6(X1,X2,X3,X4),X1) | v1_xboole_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f220,plain,(
% 0.22/0.49    spl9_22 | ~spl9_2 | ~spl9_5 | spl9_7 | spl9_11 | spl9_15 | ~spl9_18),
% 0.22/0.49    inference(avatar_split_clause,[],[f207,f177,f138,f115,f87,f80,f60,f218])).
% 0.22/0.49  fof(f207,plain,(
% 0.22/0.49    m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0) | (~spl9_2 | ~spl9_5 | spl9_7 | spl9_11 | spl9_15 | ~spl9_18)),
% 0.22/0.49    inference(subsumption_resolution,[],[f206,f178])).
% 0.22/0.49  fof(f206,plain,(
% 0.22/0.49    ~m1_subset_1(sK4,sK1) | m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0) | (~spl9_2 | ~spl9_5 | spl9_7 | spl9_11 | spl9_15)),
% 0.22/0.49    inference(subsumption_resolution,[],[f203,f116])).
% 0.22/0.49  fof(f203,plain,(
% 0.22/0.49    v1_xboole_0(sK2) | ~m1_subset_1(sK4,sK1) | m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0) | (~spl9_2 | ~spl9_5 | spl9_7 | spl9_15)),
% 0.22/0.49    inference(resolution,[],[f160,f81])).
% 0.22/0.49  fof(f160,plain,(
% 0.22/0.49    ( ! [X2,X1] : (~r2_hidden(X2,k9_relat_1(sK3,X1)) | v1_xboole_0(X1) | ~m1_subset_1(X2,sK1) | m1_subset_1(sK6(X1,sK0,sK3,X2),sK0)) ) | (~spl9_2 | spl9_7 | spl9_15)),
% 0.22/0.49    inference(subsumption_resolution,[],[f159,f139])).
% 0.22/0.49  fof(f159,plain,(
% 0.22/0.49    ( ! [X2,X1] : (~r2_hidden(X2,k9_relat_1(sK3,X1)) | v1_xboole_0(X1) | ~m1_subset_1(X2,sK1) | m1_subset_1(sK6(X1,sK0,sK3,X2),sK0) | v1_xboole_0(sK1)) ) | (~spl9_2 | spl9_7)),
% 0.22/0.49    inference(subsumption_resolution,[],[f158,f61])).
% 0.22/0.49  fof(f158,plain,(
% 0.22/0.49    ( ! [X2,X1] : (~r2_hidden(X2,k9_relat_1(sK3,X1)) | v1_xboole_0(X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X2,sK1) | m1_subset_1(sK6(X1,sK0,sK3,X2),sK0) | v1_xboole_0(sK1)) ) | (~spl9_2 | spl9_7)),
% 0.22/0.49    inference(subsumption_resolution,[],[f155,f88])).
% 0.22/0.49  fof(f155,plain,(
% 0.22/0.49    ( ! [X2,X1] : (~r2_hidden(X2,k9_relat_1(sK3,X1)) | v1_xboole_0(X1) | v1_xboole_0(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X2,sK1) | m1_subset_1(sK6(X1,sK0,sK3,X2),sK0) | v1_xboole_0(sK1)) ) | ~spl9_2),
% 0.22/0.49    inference(superposition,[],[f40,f67])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~m1_subset_1(X4,X0) | m1_subset_1(sK6(X1,X2,X3,X4),X2) | v1_xboole_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f179,plain,(
% 0.22/0.49    spl9_18 | ~spl9_2 | ~spl9_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f170,f80,f60,f177])).
% 0.22/0.49  fof(f170,plain,(
% 0.22/0.49    m1_subset_1(sK4,sK1) | (~spl9_2 | ~spl9_5)),
% 0.22/0.49    inference(resolution,[],[f154,f96])).
% 0.22/0.49  fof(f96,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(X0)) | m1_subset_1(sK4,X0)) ) | ~spl9_5),
% 0.22/0.49    inference(resolution,[],[f81,f37])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.49    inference(flattening,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.22/0.49  fof(f154,plain,(
% 0.22/0.49    ( ! [X0] : (m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(sK1))) ) | ~spl9_2),
% 0.22/0.49    inference(superposition,[],[f65,f67])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    ( ! [X0] : (m1_subset_1(k7_relset_1(sK0,sK1,sK3,X0),k1_zfmisc_1(sK1))) ) | ~spl9_2),
% 0.22/0.49    inference(resolution,[],[f61,f44])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).
% 0.22/0.49  fof(f168,plain,(
% 0.22/0.49    ~spl9_6 | ~spl9_14),
% 0.22/0.49    inference(avatar_split_clause,[],[f148,f134,f84])).
% 0.22/0.49  fof(f84,plain,(
% 0.22/0.49    spl9_6 <=> v1_xboole_0(sK3)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.22/0.49  fof(f134,plain,(
% 0.22/0.49    spl9_14 <=> r2_hidden(k4_tarski(sK8(sK4,sK2,sK3),sK4),sK3)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 0.22/0.49  fof(f148,plain,(
% 0.22/0.49    ~v1_xboole_0(sK3) | ~spl9_14),
% 0.22/0.49    inference(resolution,[],[f135,f39])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.49  fof(f135,plain,(
% 0.22/0.49    r2_hidden(k4_tarski(sK8(sK4,sK2,sK3),sK4),sK3) | ~spl9_14),
% 0.22/0.49    inference(avatar_component_clause,[],[f134])).
% 0.22/0.49  fof(f143,plain,(
% 0.22/0.49    ~spl9_15 | spl9_16 | ~spl9_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f132,f60,f141,f138])).
% 0.22/0.49  fof(f132,plain,(
% 0.22/0.49    ( ! [X0] : (v1_xboole_0(k9_relat_1(sK3,X0)) | ~v1_xboole_0(sK1)) ) | ~spl9_2),
% 0.22/0.49    inference(forward_demodulation,[],[f131,f67])).
% 0.22/0.49  fof(f131,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_xboole_0(sK1) | v1_xboole_0(k7_relset_1(sK0,sK1,sK3,X0))) ) | ~spl9_2),
% 0.22/0.49    inference(resolution,[],[f65,f46])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0) | v1_xboole_0(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.22/0.49  fof(f136,plain,(
% 0.22/0.49    spl9_14 | ~spl9_3 | ~spl9_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f98,f80,f71,f134])).
% 0.22/0.49  fof(f98,plain,(
% 0.22/0.49    r2_hidden(k4_tarski(sK8(sK4,sK2,sK3),sK4),sK3) | (~spl9_3 | ~spl9_5)),
% 0.22/0.49    inference(subsumption_resolution,[],[f93,f72])).
% 0.22/0.49  fof(f93,plain,(
% 0.22/0.49    r2_hidden(k4_tarski(sK8(sK4,sK2,sK3),sK4),sK3) | ~v1_relat_1(sK3) | ~spl9_5),
% 0.22/0.49    inference(resolution,[],[f81,f51])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2) | ~v1_relat_1(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 0.22/0.49  fof(f117,plain,(
% 0.22/0.49    ~spl9_11 | ~spl9_10),
% 0.22/0.49    inference(avatar_split_clause,[],[f112,f109,f115])).
% 0.22/0.49  fof(f109,plain,(
% 0.22/0.49    spl9_10 <=> r2_hidden(sK8(sK4,sK2,sK3),sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 0.22/0.49  fof(f112,plain,(
% 0.22/0.49    ~v1_xboole_0(sK2) | ~spl9_10),
% 0.22/0.49    inference(resolution,[],[f110,f39])).
% 0.22/0.49  fof(f110,plain,(
% 0.22/0.49    r2_hidden(sK8(sK4,sK2,sK3),sK2) | ~spl9_10),
% 0.22/0.49    inference(avatar_component_clause,[],[f109])).
% 0.22/0.49  fof(f111,plain,(
% 0.22/0.49    spl9_10 | ~spl9_3 | ~spl9_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f99,f80,f71,f109])).
% 0.22/0.49  fof(f99,plain,(
% 0.22/0.49    r2_hidden(sK8(sK4,sK2,sK3),sK2) | (~spl9_3 | ~spl9_5)),
% 0.22/0.49    inference(subsumption_resolution,[],[f94,f72])).
% 0.22/0.49  fof(f94,plain,(
% 0.22/0.49    r2_hidden(sK8(sK4,sK2,sK3),sK2) | ~v1_relat_1(sK3) | ~spl9_5),
% 0.22/0.49    inference(resolution,[],[f81,f52])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK8(X0,X1,X2),X1) | ~v1_relat_1(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f103,plain,(
% 0.22/0.49    ~spl9_8 | ~spl9_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f95,f80,f101])).
% 0.22/0.49  fof(f95,plain,(
% 0.22/0.49    ~v1_xboole_0(k9_relat_1(sK3,sK2)) | ~spl9_5),
% 0.22/0.49    inference(resolution,[],[f81,f39])).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    spl9_6 | ~spl9_7 | ~spl9_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f64,f60,f87,f84])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    ~v1_xboole_0(sK0) | v1_xboole_0(sK3) | ~spl9_2),
% 0.22/0.49    inference(resolution,[],[f61,f45])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0) | v1_xboole_0(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    spl9_5 | ~spl9_2 | ~spl9_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f78,f75,f60,f80])).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    spl9_4 <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.22/0.49  fof(f78,plain,(
% 0.22/0.49    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | (~spl9_2 | ~spl9_4)),
% 0.22/0.49    inference(forward_demodulation,[],[f76,f67])).
% 0.22/0.49  fof(f76,plain,(
% 0.22/0.49    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) | ~spl9_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f75])).
% 0.22/0.49  fof(f77,plain,(
% 0.22/0.49    spl9_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f30,f75])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    spl9_3 | ~spl9_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f63,f60,f71])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    v1_relat_1(sK3) | ~spl9_2),
% 0.22/0.49    inference(resolution,[],[f61,f49])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    spl9_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f32,f60])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    spl9_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f31,f56])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    v1_funct_1(sK3)),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (10381)------------------------------
% 0.22/0.49  % (10381)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (10381)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (10381)Memory used [KB]: 6268
% 0.22/0.49  % (10381)Time elapsed: 0.069 s
% 0.22/0.49  % (10381)------------------------------
% 0.22/0.49  % (10381)------------------------------
% 0.22/0.49  % (10380)Success in time 0.134 s
%------------------------------------------------------------------------------
