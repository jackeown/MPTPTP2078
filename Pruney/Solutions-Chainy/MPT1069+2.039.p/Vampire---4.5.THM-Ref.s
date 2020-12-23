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
% DateTime   : Thu Dec  3 13:07:48 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 233 expanded)
%              Number of leaves         :   36 (  99 expanded)
%              Depth                    :    9
%              Number of atoms          :  435 ( 915 expanded)
%              Number of equality atoms :   78 ( 165 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f321,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f86,f91,f96,f101,f106,f112,f117,f126,f130,f141,f151,f162,f177,f221,f231,f238,f255,f259,f283,f289,f305,f312,f320])).

fof(f320,plain,
    ( ~ spl10_14
    | ~ spl10_2
    | ~ spl10_32
    | ~ spl10_9
    | ~ spl10_29
    | spl10_36 ),
    inference(avatar_split_clause,[],[f316,f309,f235,f119,f286,f83,f159])).

fof(f159,plain,
    ( spl10_14
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f83,plain,
    ( spl10_2
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f286,plain,
    ( spl10_32
  <=> r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).

fof(f119,plain,
    ( spl10_9
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f235,plain,
    ( spl10_29
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).

fof(f309,plain,
    ( spl10_36
  <=> r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).

fof(f316,plain,
    ( ~ r2_hidden(sK5,sK1)
    | ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl10_29
    | spl10_36 ),
    inference(forward_demodulation,[],[f314,f237])).

fof(f237,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl10_29 ),
    inference(avatar_component_clause,[],[f235])).

fof(f314,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | ~ v1_funct_1(sK3)
    | ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl10_36 ),
    inference(resolution,[],[f313,f69])).

fof(f69,plain,(
    ! [X0,X3] :
      ( r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | r2_hidden(k1_funct_1(X0,X3),X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f313,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_funct_1(sK3,sK5),X0)
        | ~ r1_tarski(X0,k1_relat_1(sK4)) )
    | spl10_36 ),
    inference(resolution,[],[f311,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f311,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | spl10_36 ),
    inference(avatar_component_clause,[],[f309])).

fof(f312,plain,
    ( ~ spl10_11
    | ~ spl10_36
    | ~ spl10_1
    | ~ spl10_13
    | spl10_35 ),
    inference(avatar_split_clause,[],[f307,f302,f148,f78,f309,f138])).

fof(f138,plain,
    ( spl10_11
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f78,plain,
    ( spl10_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f148,plain,
    ( spl10_13
  <=> v5_relat_1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f302,plain,
    ( spl10_35
  <=> k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_35])])).

fof(f307,plain,
    ( ~ v5_relat_1(sK4,sK0)
    | ~ v1_funct_1(sK4)
    | ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | spl10_35 ),
    inference(trivial_inequality_removal,[],[f306])).

% (2159)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f306,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ v5_relat_1(sK4,sK0)
    | ~ v1_funct_1(sK4)
    | ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | spl10_35 ),
    inference(superposition,[],[f304,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

fof(f304,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | spl10_35 ),
    inference(avatar_component_clause,[],[f302])).

fof(f305,plain,
    ( spl10_3
    | spl10_5
    | ~ spl10_17
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_1
    | ~ spl10_8
    | ~ spl10_6
    | ~ spl10_2
    | ~ spl10_35
    | spl10_26 ),
    inference(avatar_split_clause,[],[f295,f218,f302,f83,f103,f114,f78,f109,f93,f174,f98,f88])).

fof(f88,plain,
    ( spl10_3
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f98,plain,
    ( spl10_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f174,plain,
    ( spl10_17
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f93,plain,
    ( spl10_4
  <=> m1_subset_1(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f109,plain,
    ( spl10_7
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f114,plain,
    ( spl10_8
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f103,plain,
    ( spl10_6
  <=> v1_funct_2(sK3,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f218,plain,
    ( spl10_26
  <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).

fof(f295,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ m1_subset_1(sK5,sK1)
    | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    | k1_xboole_0 = sK1
    | v1_xboole_0(sK2)
    | spl10_26 ),
    inference(superposition,[],[f220,f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ m1_subset_1(X5,X1)
      | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
      | k1_xboole_0 = X1
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

fof(f220,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))
    | spl10_26 ),
    inference(avatar_component_clause,[],[f218])).

fof(f289,plain,
    ( ~ spl10_7
    | spl10_32
    | ~ spl10_31 ),
    inference(avatar_split_clause,[],[f284,f280,f286,f109])).

fof(f280,plain,
    ( spl10_31
  <=> r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_31])])).

fof(f284,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl10_31 ),
    inference(superposition,[],[f282,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f282,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4))
    | ~ spl10_31 ),
    inference(avatar_component_clause,[],[f280])).

fof(f283,plain,
    ( ~ spl10_8
    | spl10_31
    | ~ spl10_17 ),
    inference(avatar_split_clause,[],[f178,f174,f280,f114])).

fof(f178,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl10_17 ),
    inference(superposition,[],[f176,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f176,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    | ~ spl10_17 ),
    inference(avatar_component_clause,[],[f174])).

fof(f259,plain,(
    spl10_30 ),
    inference(avatar_contradiction_clause,[],[f256])).

fof(f256,plain,
    ( $false
    | spl10_30 ),
    inference(unit_resulting_resolution,[],[f43,f254])).

fof(f254,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl10_30 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl10_30
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).

fof(f43,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f255,plain,
    ( ~ spl10_30
    | spl10_3
    | ~ spl10_28 ),
    inference(avatar_split_clause,[],[f239,f228,f88,f252])).

fof(f228,plain,
    ( spl10_28
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).

fof(f239,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl10_3
    | ~ spl10_28 ),
    inference(backward_demodulation,[],[f90,f230])).

fof(f230,plain,
    ( k1_xboole_0 = sK2
    | ~ spl10_28 ),
    inference(avatar_component_clause,[],[f228])).

fof(f90,plain,
    ( ~ v1_xboole_0(sK2)
    | spl10_3 ),
    inference(avatar_component_clause,[],[f88])).

fof(f238,plain,
    ( ~ spl10_8
    | spl10_29
    | ~ spl10_27 ),
    inference(avatar_split_clause,[],[f232,f224,f235,f114])).

fof(f224,plain,
    ( spl10_27
  <=> sK1 = k1_relset_1(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).

fof(f232,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl10_27 ),
    inference(superposition,[],[f226,f59])).

fof(f226,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ spl10_27 ),
    inference(avatar_component_clause,[],[f224])).

fof(f231,plain,
    ( ~ spl10_6
    | spl10_27
    | spl10_28
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f153,f114,f228,f224,f103])).

fof(f153,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ spl10_8 ),
    inference(resolution,[],[f116,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f116,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f114])).

fof(f221,plain,(
    ~ spl10_26 ),
    inference(avatar_split_clause,[],[f36,f218])).

fof(f36,plain,(
    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ v1_xboole_0(X2)
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
           => ! [X4] :
                ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                  & v1_funct_1(X4) )
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                        | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).

fof(f177,plain,(
    spl10_17 ),
    inference(avatar_split_clause,[],[f34,f174])).

fof(f34,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f16])).

fof(f162,plain,
    ( spl10_14
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f156,f114,f159])).

fof(f156,plain,
    ( v1_relat_1(sK3)
    | ~ spl10_8 ),
    inference(resolution,[],[f116,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f151,plain,
    ( spl10_13
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f134,f109,f148])).

fof(f134,plain,
    ( v5_relat_1(sK4,sK0)
    | ~ spl10_7 ),
    inference(resolution,[],[f111,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f111,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f109])).

fof(f141,plain,
    ( spl10_11
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f135,f109,f138])).

fof(f135,plain,
    ( v1_relat_1(sK4)
    | ~ spl10_7 ),
    inference(resolution,[],[f111,f57])).

fof(f130,plain,
    ( spl10_5
    | ~ spl10_10 ),
    inference(avatar_contradiction_clause,[],[f128])).

fof(f128,plain,
    ( $false
    | spl10_5
    | ~ spl10_10 ),
    inference(unit_resulting_resolution,[],[f43,f100,f125,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ v1_xboole_0(X0)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f125,plain,
    ( v1_xboole_0(sK1)
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl10_10
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f100,plain,
    ( k1_xboole_0 != sK1
    | spl10_5 ),
    inference(avatar_component_clause,[],[f98])).

fof(f126,plain,
    ( spl10_9
    | spl10_10
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f107,f93,f123,f119])).

fof(f107,plain,
    ( v1_xboole_0(sK1)
    | r2_hidden(sK5,sK1)
    | ~ spl10_4 ),
    inference(resolution,[],[f95,f50])).

fof(f50,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f95,plain,
    ( m1_subset_1(sK5,sK1)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f93])).

fof(f117,plain,(
    spl10_8 ),
    inference(avatar_split_clause,[],[f41,f114])).

fof(f41,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f16])).

fof(f112,plain,(
    spl10_7 ),
    inference(avatar_split_clause,[],[f38,f109])).

fof(f38,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f106,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f40,f103])).

fof(f40,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f101,plain,(
    ~ spl10_5 ),
    inference(avatar_split_clause,[],[f35,f98])).

fof(f35,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f16])).

fof(f96,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f33,f93])).

fof(f33,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f91,plain,(
    ~ spl10_3 ),
    inference(avatar_split_clause,[],[f42,f88])).

fof(f42,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f86,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f39,f83])).

fof(f39,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f81,plain,(
    spl10_1 ),
    inference(avatar_split_clause,[],[f37,f78])).

fof(f37,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:58:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.48  % (2174)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.48  % (2166)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.50  % (2180)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.50  % (2181)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.50  % (2173)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (2182)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (2171)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (2165)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (2181)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f321,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f81,f86,f91,f96,f101,f106,f112,f117,f126,f130,f141,f151,f162,f177,f221,f231,f238,f255,f259,f283,f289,f305,f312,f320])).
% 0.20/0.52  fof(f320,plain,(
% 0.20/0.52    ~spl10_14 | ~spl10_2 | ~spl10_32 | ~spl10_9 | ~spl10_29 | spl10_36),
% 0.20/0.52    inference(avatar_split_clause,[],[f316,f309,f235,f119,f286,f83,f159])).
% 0.20/0.52  fof(f159,plain,(
% 0.20/0.52    spl10_14 <=> v1_relat_1(sK3)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).
% 0.20/0.52  fof(f83,plain,(
% 0.20/0.52    spl10_2 <=> v1_funct_1(sK3)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.20/0.52  fof(f286,plain,(
% 0.20/0.52    spl10_32 <=> r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).
% 0.20/0.52  fof(f119,plain,(
% 0.20/0.52    spl10_9 <=> r2_hidden(sK5,sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 0.20/0.52  fof(f235,plain,(
% 0.20/0.52    spl10_29 <=> sK1 = k1_relat_1(sK3)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).
% 0.20/0.52  fof(f309,plain,(
% 0.20/0.52    spl10_36 <=> r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).
% 0.20/0.52  fof(f316,plain,(
% 0.20/0.52    ~r2_hidden(sK5,sK1) | ~r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl10_29 | spl10_36)),
% 0.20/0.52    inference(forward_demodulation,[],[f314,f237])).
% 0.20/0.52  fof(f237,plain,(
% 0.20/0.52    sK1 = k1_relat_1(sK3) | ~spl10_29),
% 0.20/0.52    inference(avatar_component_clause,[],[f235])).
% 0.20/0.52  fof(f314,plain,(
% 0.20/0.52    ~r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) | ~v1_funct_1(sK3) | ~r2_hidden(sK5,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | spl10_36),
% 0.20/0.52    inference(resolution,[],[f313,f69])).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    ( ! [X0,X3] : (r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(equality_resolution,[],[f68])).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | r2_hidden(k1_funct_1(X0,X3),X1) | k2_relat_1(X0) != X1) )),
% 0.20/0.52    inference(equality_resolution,[],[f49])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X0,X3) != X2 | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(flattening,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 0.20/0.52  fof(f313,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(k1_funct_1(sK3,sK5),X0) | ~r1_tarski(X0,k1_relat_1(sK4))) ) | spl10_36),
% 0.20/0.52    inference(resolution,[],[f311,f52])).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.52  fof(f311,plain,(
% 0.20/0.52    ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | spl10_36),
% 0.20/0.52    inference(avatar_component_clause,[],[f309])).
% 0.20/0.52  fof(f312,plain,(
% 0.20/0.52    ~spl10_11 | ~spl10_36 | ~spl10_1 | ~spl10_13 | spl10_35),
% 0.20/0.52    inference(avatar_split_clause,[],[f307,f302,f148,f78,f309,f138])).
% 0.20/0.52  fof(f138,plain,(
% 0.20/0.52    spl10_11 <=> v1_relat_1(sK4)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 0.20/0.52  fof(f78,plain,(
% 0.20/0.52    spl10_1 <=> v1_funct_1(sK4)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.20/0.52  fof(f148,plain,(
% 0.20/0.52    spl10_13 <=> v5_relat_1(sK4,sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).
% 0.20/0.52  fof(f302,plain,(
% 0.20/0.52    spl10_35 <=> k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_35])])).
% 0.20/0.52  fof(f307,plain,(
% 0.20/0.52    ~v5_relat_1(sK4,sK0) | ~v1_funct_1(sK4) | ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | ~v1_relat_1(sK4) | spl10_35),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f306])).
% 0.20/0.52  % (2159)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  fof(f306,plain,(
% 0.20/0.52    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~v5_relat_1(sK4,sK0) | ~v1_funct_1(sK4) | ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | ~v1_relat_1(sK4) | spl10_35),
% 0.20/0.52    inference(superposition,[],[f304,f51])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~v5_relat_1(X1,X0) | ~v1_funct_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(flattening,[],[f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.52    inference(ennf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,axiom,(
% 0.20/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).
% 0.20/0.52  fof(f304,plain,(
% 0.20/0.52    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | spl10_35),
% 0.20/0.52    inference(avatar_component_clause,[],[f302])).
% 0.20/0.52  fof(f305,plain,(
% 0.20/0.52    spl10_3 | spl10_5 | ~spl10_17 | ~spl10_4 | ~spl10_7 | ~spl10_1 | ~spl10_8 | ~spl10_6 | ~spl10_2 | ~spl10_35 | spl10_26),
% 0.20/0.52    inference(avatar_split_clause,[],[f295,f218,f302,f83,f103,f114,f78,f109,f93,f174,f98,f88])).
% 0.20/0.52  fof(f88,plain,(
% 0.20/0.52    spl10_3 <=> v1_xboole_0(sK2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.20/0.52  fof(f98,plain,(
% 0.20/0.52    spl10_5 <=> k1_xboole_0 = sK1),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.20/0.52  fof(f174,plain,(
% 0.20/0.52    spl10_17 <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).
% 0.20/0.52  fof(f93,plain,(
% 0.20/0.52    spl10_4 <=> m1_subset_1(sK5,sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.20/0.52  fof(f109,plain,(
% 0.20/0.52    spl10_7 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.20/0.52  fof(f114,plain,(
% 0.20/0.52    spl10_8 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 0.20/0.52  fof(f103,plain,(
% 0.20/0.52    spl10_6 <=> v1_funct_2(sK3,sK1,sK2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.20/0.52  fof(f218,plain,(
% 0.20/0.52    spl10_26 <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).
% 0.20/0.52  fof(f295,plain,(
% 0.20/0.52    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~m1_subset_1(sK5,sK1) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) | k1_xboole_0 = sK1 | v1_xboole_0(sK2) | spl10_26),
% 0.20/0.52    inference(superposition,[],[f220,f56])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~m1_subset_1(X5,X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | k1_xboole_0 = X1 | v1_xboole_0(X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 0.20/0.52    inference(flattening,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 0.20/0.52    inference(ennf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).
% 0.20/0.52  fof(f220,plain,(
% 0.20/0.52    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) | spl10_26),
% 0.20/0.52    inference(avatar_component_clause,[],[f218])).
% 0.20/0.52  fof(f289,plain,(
% 0.20/0.52    ~spl10_7 | spl10_32 | ~spl10_31),
% 0.20/0.52    inference(avatar_split_clause,[],[f284,f280,f286,f109])).
% 0.20/0.52  fof(f280,plain,(
% 0.20/0.52    spl10_31 <=> r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_31])])).
% 0.20/0.52  fof(f284,plain,(
% 0.20/0.52    r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~spl10_31),
% 0.20/0.52    inference(superposition,[],[f282,f59])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.52  fof(f282,plain,(
% 0.20/0.52    r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4)) | ~spl10_31),
% 0.20/0.52    inference(avatar_component_clause,[],[f280])).
% 0.20/0.52  fof(f283,plain,(
% 0.20/0.52    ~spl10_8 | spl10_31 | ~spl10_17),
% 0.20/0.52    inference(avatar_split_clause,[],[f178,f174,f280,f114])).
% 0.20/0.52  fof(f178,plain,(
% 0.20/0.52    r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl10_17),
% 0.20/0.52    inference(superposition,[],[f176,f58])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.52  fof(f176,plain,(
% 0.20/0.52    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) | ~spl10_17),
% 0.20/0.52    inference(avatar_component_clause,[],[f174])).
% 0.20/0.52  fof(f259,plain,(
% 0.20/0.52    spl10_30),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f256])).
% 0.20/0.52  fof(f256,plain,(
% 0.20/0.52    $false | spl10_30),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f43,f254])).
% 0.20/0.52  fof(f254,plain,(
% 0.20/0.52    ~v1_xboole_0(k1_xboole_0) | spl10_30),
% 0.20/0.52    inference(avatar_component_clause,[],[f252])).
% 0.20/0.52  fof(f252,plain,(
% 0.20/0.52    spl10_30 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    v1_xboole_0(k1_xboole_0)),
% 0.20/0.52    inference(cnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    v1_xboole_0(k1_xboole_0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.52  fof(f255,plain,(
% 0.20/0.52    ~spl10_30 | spl10_3 | ~spl10_28),
% 0.20/0.52    inference(avatar_split_clause,[],[f239,f228,f88,f252])).
% 0.20/0.52  fof(f228,plain,(
% 0.20/0.52    spl10_28 <=> k1_xboole_0 = sK2),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).
% 0.20/0.52  fof(f239,plain,(
% 0.20/0.52    ~v1_xboole_0(k1_xboole_0) | (spl10_3 | ~spl10_28)),
% 0.20/0.52    inference(backward_demodulation,[],[f90,f230])).
% 0.20/0.52  fof(f230,plain,(
% 0.20/0.52    k1_xboole_0 = sK2 | ~spl10_28),
% 0.20/0.52    inference(avatar_component_clause,[],[f228])).
% 0.20/0.52  fof(f90,plain,(
% 0.20/0.52    ~v1_xboole_0(sK2) | spl10_3),
% 0.20/0.52    inference(avatar_component_clause,[],[f88])).
% 0.20/0.52  fof(f238,plain,(
% 0.20/0.52    ~spl10_8 | spl10_29 | ~spl10_27),
% 0.20/0.52    inference(avatar_split_clause,[],[f232,f224,f235,f114])).
% 0.20/0.52  fof(f224,plain,(
% 0.20/0.52    spl10_27 <=> sK1 = k1_relset_1(sK1,sK2,sK3)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).
% 0.20/0.52  fof(f232,plain,(
% 0.20/0.52    sK1 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl10_27),
% 0.20/0.52    inference(superposition,[],[f226,f59])).
% 0.20/0.52  fof(f226,plain,(
% 0.20/0.52    sK1 = k1_relset_1(sK1,sK2,sK3) | ~spl10_27),
% 0.20/0.52    inference(avatar_component_clause,[],[f224])).
% 0.20/0.52  fof(f231,plain,(
% 0.20/0.52    ~spl10_6 | spl10_27 | spl10_28 | ~spl10_8),
% 0.20/0.52    inference(avatar_split_clause,[],[f153,f114,f228,f224,f103])).
% 0.20/0.52  fof(f153,plain,(
% 0.20/0.52    k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3) | ~v1_funct_2(sK3,sK1,sK2) | ~spl10_8),
% 0.20/0.52    inference(resolution,[],[f116,f67])).
% 0.20/0.52  fof(f67,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(flattening,[],[f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.52  fof(f116,plain,(
% 0.20/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl10_8),
% 0.20/0.52    inference(avatar_component_clause,[],[f114])).
% 0.20/0.52  fof(f221,plain,(
% 0.20/0.52    ~spl10_26),
% 0.20/0.52    inference(avatar_split_clause,[],[f36,f218])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 0.20/0.52    inference(flattening,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 0.20/0.52    inference(ennf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.20/0.52    inference(negated_conjecture,[],[f13])).
% 0.20/0.52  fof(f13,conjecture,(
% 0.20/0.52    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).
% 0.20/0.52  fof(f177,plain,(
% 0.20/0.52    spl10_17),
% 0.20/0.52    inference(avatar_split_clause,[],[f34,f174])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f162,plain,(
% 0.20/0.52    spl10_14 | ~spl10_8),
% 0.20/0.52    inference(avatar_split_clause,[],[f156,f114,f159])).
% 0.20/0.52  fof(f156,plain,(
% 0.20/0.52    v1_relat_1(sK3) | ~spl10_8),
% 0.20/0.52    inference(resolution,[],[f116,f57])).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.52  fof(f151,plain,(
% 0.20/0.52    spl10_13 | ~spl10_7),
% 0.20/0.52    inference(avatar_split_clause,[],[f134,f109,f148])).
% 0.20/0.52  fof(f134,plain,(
% 0.20/0.52    v5_relat_1(sK4,sK0) | ~spl10_7),
% 0.20/0.52    inference(resolution,[],[f111,f61])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.52  fof(f111,plain,(
% 0.20/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~spl10_7),
% 0.20/0.52    inference(avatar_component_clause,[],[f109])).
% 0.20/0.52  fof(f141,plain,(
% 0.20/0.52    spl10_11 | ~spl10_7),
% 0.20/0.52    inference(avatar_split_clause,[],[f135,f109,f138])).
% 0.20/0.52  fof(f135,plain,(
% 0.20/0.52    v1_relat_1(sK4) | ~spl10_7),
% 0.20/0.52    inference(resolution,[],[f111,f57])).
% 0.20/0.52  fof(f130,plain,(
% 0.20/0.52    spl10_5 | ~spl10_10),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f128])).
% 0.20/0.52  fof(f128,plain,(
% 0.20/0.52    $false | (spl10_5 | ~spl10_10)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f43,f100,f125,f55])).
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    ( ! [X0,X1] : (X0 = X1 | ~v1_xboole_0(X0) | ~v1_xboole_0(X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 0.20/0.52  fof(f125,plain,(
% 0.20/0.52    v1_xboole_0(sK1) | ~spl10_10),
% 0.20/0.52    inference(avatar_component_clause,[],[f123])).
% 0.20/0.52  fof(f123,plain,(
% 0.20/0.52    spl10_10 <=> v1_xboole_0(sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 0.20/0.52  fof(f100,plain,(
% 0.20/0.52    k1_xboole_0 != sK1 | spl10_5),
% 0.20/0.52    inference(avatar_component_clause,[],[f98])).
% 0.20/0.52  fof(f126,plain,(
% 0.20/0.52    spl10_9 | spl10_10 | ~spl10_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f107,f93,f123,f119])).
% 0.20/0.52  fof(f107,plain,(
% 0.20/0.52    v1_xboole_0(sK1) | r2_hidden(sK5,sK1) | ~spl10_4),
% 0.20/0.52    inference(resolution,[],[f95,f50])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.52    inference(flattening,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.52  fof(f95,plain,(
% 0.20/0.52    m1_subset_1(sK5,sK1) | ~spl10_4),
% 0.20/0.52    inference(avatar_component_clause,[],[f93])).
% 0.20/0.52  fof(f117,plain,(
% 0.20/0.52    spl10_8),
% 0.20/0.52    inference(avatar_split_clause,[],[f41,f114])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f112,plain,(
% 0.20/0.52    spl10_7),
% 0.20/0.52    inference(avatar_split_clause,[],[f38,f109])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f106,plain,(
% 0.20/0.52    spl10_6),
% 0.20/0.52    inference(avatar_split_clause,[],[f40,f103])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    v1_funct_2(sK3,sK1,sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f101,plain,(
% 0.20/0.52    ~spl10_5),
% 0.20/0.52    inference(avatar_split_clause,[],[f35,f98])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    k1_xboole_0 != sK1),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f96,plain,(
% 0.20/0.52    spl10_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f33,f93])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    m1_subset_1(sK5,sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f91,plain,(
% 0.20/0.52    ~spl10_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f42,f88])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ~v1_xboole_0(sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f86,plain,(
% 0.20/0.52    spl10_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f39,f83])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    v1_funct_1(sK3)),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f81,plain,(
% 0.20/0.52    spl10_1),
% 0.20/0.52    inference(avatar_split_clause,[],[f37,f78])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    v1_funct_1(sK4)),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (2181)------------------------------
% 0.20/0.52  % (2181)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (2181)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (2181)Memory used [KB]: 11001
% 0.20/0.52  % (2181)Time elapsed: 0.062 s
% 0.20/0.52  % (2181)------------------------------
% 0.20/0.52  % (2181)------------------------------
% 0.20/0.52  % (2164)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (2172)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (2158)Success in time 0.174 s
%------------------------------------------------------------------------------
