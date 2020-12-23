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
% DateTime   : Thu Dec  3 13:06:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 351 expanded)
%              Number of leaves         :   29 ( 158 expanded)
%              Depth                    :   11
%              Number of atoms          :  790 (1587 expanded)
%              Number of equality atoms :  106 ( 233 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f277,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f32,f36,f40,f44,f51,f55,f60,f64,f68,f72,f76,f80,f87,f91,f100,f108,f112,f117,f125,f137,f147,f162,f170,f191,f210,f229,f252,f264,f274])).

fof(f274,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_6
    | spl5_8
    | ~ spl5_12
    | ~ spl5_18
    | ~ spl5_19
    | ~ spl5_20
    | ~ spl5_22 ),
    inference(avatar_contradiction_clause,[],[f270])).

fof(f270,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_6
    | spl5_8
    | ~ spl5_12
    | ~ spl5_18
    | ~ spl5_19
    | ~ spl5_20
    | ~ spl5_22 ),
    inference(unit_resulting_resolution,[],[f31,f27,f56,f107,f136,f54,f116,f111,f71])).

fof(f71,plain,
    ( ! [X4,X2,X3,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,k1_xboole_0,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | ~ r2_hidden(X4,k1_relset_1(k1_xboole_0,X1,X2))
        | k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
        | ~ r1_partfun1(X2,X3) )
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl5_12
  <=> ! [X1,X3,X2,X4] :
        ( ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,k1_xboole_0,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | ~ r2_hidden(X4,k1_relset_1(k1_xboole_0,X1,X2))
        | k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
        | ~ r1_partfun1(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f111,plain,
    ( r2_hidden(sK3,k1_relset_1(k1_xboole_0,k1_xboole_0,sK1))
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl5_19
  <=> r2_hidden(sK3,k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f116,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl5_20
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f54,plain,
    ( k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl5_8
  <=> k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f136,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl5_22
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f107,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl5_18
  <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f56,plain,
    ( r1_partfun1(sK1,sK2)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl5_6
  <=> r1_partfun1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f27,plain,
    ( v1_funct_1(sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl5_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f31,plain,
    ( v1_funct_1(sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl5_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f264,plain,
    ( ~ spl5_1
    | spl5_6
    | ~ spl5_18
    | ~ spl5_22
    | ~ spl5_27
    | ~ spl5_34 ),
    inference(avatar_contradiction_clause,[],[f263])).

fof(f263,plain,
    ( $false
    | ~ spl5_1
    | spl5_6
    | ~ spl5_18
    | ~ spl5_22
    | ~ spl5_27
    | ~ spl5_34 ),
    inference(subsumption_resolution,[],[f262,f47])).

fof(f47,plain,
    ( ~ r1_partfun1(sK1,sK2)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f46])).

fof(f262,plain,
    ( r1_partfun1(sK1,sK2)
    | ~ spl5_1
    | ~ spl5_18
    | ~ spl5_22
    | ~ spl5_27
    | ~ spl5_34 ),
    inference(subsumption_resolution,[],[f261,f27])).

fof(f261,plain,
    ( ~ v1_funct_1(sK2)
    | r1_partfun1(sK1,sK2)
    | ~ spl5_18
    | ~ spl5_22
    | ~ spl5_27
    | ~ spl5_34 ),
    inference(subsumption_resolution,[],[f260,f136])).

fof(f260,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(sK2)
    | r1_partfun1(sK1,sK2)
    | ~ spl5_18
    | ~ spl5_27
    | ~ spl5_34 ),
    inference(subsumption_resolution,[],[f257,f107])).

fof(f257,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(sK2)
    | r1_partfun1(sK1,sK2)
    | ~ spl5_27
    | ~ spl5_34 ),
    inference(trivial_inequality_removal,[],[f255])).

fof(f255,plain,
    ( k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2)) != k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2))
    | ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(sK2)
    | r1_partfun1(sK1,sK2)
    | ~ spl5_27
    | ~ spl5_34 ),
    inference(superposition,[],[f209,f251])).

fof(f251,plain,
    ( k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2)) = k1_funct_1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2))
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f250])).

fof(f250,plain,
    ( spl5_34
  <=> k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2)) = k1_funct_1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f209,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,X0)) != k1_funct_1(X0,sK4(k1_xboole_0,k1_xboole_0,sK1,X0))
        | ~ v1_funct_2(X0,k1_xboole_0,k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_1(X0)
        | r1_partfun1(sK1,X0) )
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl5_27
  <=> ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k1_xboole_0,k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,X0)) != k1_funct_1(X0,sK4(k1_xboole_0,k1_xboole_0,sK1,X0))
        | r1_partfun1(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f252,plain,
    ( spl5_34
    | ~ spl5_1
    | spl5_6
    | ~ spl5_18
    | ~ spl5_22
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f236,f227,f135,f106,f46,f26,f250])).

fof(f227,plain,
    ( spl5_30
  <=> ! [X0] :
        ( k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,X0)) = k1_funct_1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK1,X0))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k1_xboole_0,k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | r1_partfun1(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f236,plain,
    ( k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2)) = k1_funct_1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2))
    | ~ spl5_1
    | spl5_6
    | ~ spl5_18
    | ~ spl5_22
    | ~ spl5_30 ),
    inference(subsumption_resolution,[],[f235,f47])).

fof(f235,plain,
    ( k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2)) = k1_funct_1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2))
    | r1_partfun1(sK1,sK2)
    | ~ spl5_1
    | ~ spl5_18
    | ~ spl5_22
    | ~ spl5_30 ),
    inference(subsumption_resolution,[],[f234,f136])).

fof(f234,plain,
    ( k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2)) = k1_funct_1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | r1_partfun1(sK1,sK2)
    | ~ spl5_1
    | ~ spl5_18
    | ~ spl5_30 ),
    inference(subsumption_resolution,[],[f233,f27])).

fof(f233,plain,
    ( ~ v1_funct_1(sK2)
    | k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2)) = k1_funct_1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | r1_partfun1(sK1,sK2)
    | ~ spl5_18
    | ~ spl5_30 ),
    inference(resolution,[],[f228,f107])).

fof(f228,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,k1_xboole_0,k1_xboole_0)
        | ~ v1_funct_1(X0)
        | k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,X0)) = k1_funct_1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK1,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | r1_partfun1(sK1,X0) )
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f227])).

fof(f229,plain,
    ( spl5_30
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_20
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f193,f160,f115,f62,f30,f227])).

fof(f62,plain,
    ( spl5_10
  <=> ! [X1,X3,X2] :
        ( ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,k1_xboole_0,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | r2_hidden(sK4(k1_xboole_0,X1,X2,X3),k1_relset_1(k1_xboole_0,X1,X2))
        | r1_partfun1(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f160,plain,
    ( spl5_24
  <=> ! [X3] :
        ( ~ r2_hidden(X3,k1_relset_1(k1_xboole_0,k1_xboole_0,sK1))
        | k1_funct_1(sK1,X3) = k1_funct_1(sK2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f193,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,X0)) = k1_funct_1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK1,X0))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k1_xboole_0,k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | r1_partfun1(sK1,X0) )
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_20
    | ~ spl5_24 ),
    inference(subsumption_resolution,[],[f192,f31])).

fof(f192,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,X0)) = k1_funct_1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK1,X0))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k1_xboole_0,k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_1(sK1)
        | r1_partfun1(sK1,X0) )
    | ~ spl5_10
    | ~ spl5_20
    | ~ spl5_24 ),
    inference(subsumption_resolution,[],[f189,f116])).

fof(f189,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,X0)) = k1_funct_1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK1,X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k1_xboole_0,k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_1(sK1)
        | r1_partfun1(sK1,X0) )
    | ~ spl5_10
    | ~ spl5_24 ),
    inference(resolution,[],[f161,f63])).

fof(f63,plain,
    ( ! [X2,X3,X1] :
        ( r2_hidden(sK4(k1_xboole_0,X1,X2,X3),k1_relset_1(k1_xboole_0,X1,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,k1_xboole_0,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | ~ v1_funct_1(X2)
        | r1_partfun1(X2,X3) )
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f62])).

fof(f161,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_relset_1(k1_xboole_0,k1_xboole_0,sK1))
        | k1_funct_1(sK1,X3) = k1_funct_1(sK2,X3) )
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f160])).

fof(f210,plain,
    ( spl5_27
    | ~ spl5_2
    | ~ spl5_13
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f132,f115,f74,f30,f208])).

fof(f74,plain,
    ( spl5_13
  <=> ! [X1,X3,X2] :
        ( ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,k1_xboole_0,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | k1_funct_1(X2,sK4(k1_xboole_0,X1,X2,X3)) != k1_funct_1(X3,sK4(k1_xboole_0,X1,X2,X3))
        | r1_partfun1(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f132,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k1_xboole_0,k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,X0)) != k1_funct_1(X0,sK4(k1_xboole_0,k1_xboole_0,sK1,X0))
        | r1_partfun1(sK1,X0) )
    | ~ spl5_2
    | ~ spl5_13
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f130,f31])).

fof(f130,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK1)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k1_xboole_0,k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,X0)) != k1_funct_1(X0,sK4(k1_xboole_0,k1_xboole_0,sK1,X0))
        | r1_partfun1(sK1,X0) )
    | ~ spl5_13
    | ~ spl5_20 ),
    inference(resolution,[],[f116,f75])).

fof(f75,plain,
    ( ! [X2,X3,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,k1_xboole_0,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | k1_funct_1(X2,sK4(k1_xboole_0,X1,X2,X3)) != k1_funct_1(X3,sK4(k1_xboole_0,X1,X2,X3))
        | r1_partfun1(X2,X3) )
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f74])).

fof(f191,plain,
    ( spl5_17
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_6
    | ~ spl5_15
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f179,f145,f85,f46,f42,f38,f34,f30,f26,f98])).

fof(f98,plain,
    ( spl5_17
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f34,plain,
    ( spl5_3
  <=> v1_funct_2(sK2,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f38,plain,
    ( spl5_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f42,plain,
    ( spl5_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f85,plain,
    ( spl5_15
  <=> ! [X1,X3,X0,X2] :
        ( ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X0,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | k1_funct_1(X2,sK4(X0,X1,X2,X3)) != k1_funct_1(X3,sK4(X0,X1,X2,X3))
        | r1_partfun1(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f145,plain,
    ( spl5_23
  <=> k1_funct_1(sK1,sK4(sK0,sK0,sK1,sK2)) = k1_funct_1(sK2,sK4(sK0,sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f179,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_6
    | ~ spl5_15
    | ~ spl5_23 ),
    inference(subsumption_resolution,[],[f178,f47])).

fof(f178,plain,
    ( k1_xboole_0 = sK0
    | r1_partfun1(sK1,sK2)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_15
    | ~ spl5_23 ),
    inference(subsumption_resolution,[],[f177,f31])).

fof(f177,plain,
    ( k1_xboole_0 = sK0
    | ~ v1_funct_1(sK1)
    | r1_partfun1(sK1,sK2)
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_15
    | ~ spl5_23 ),
    inference(subsumption_resolution,[],[f176,f39])).

fof(f39,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f38])).

fof(f176,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK1)
    | r1_partfun1(sK1,sK2)
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_15
    | ~ spl5_23 ),
    inference(subsumption_resolution,[],[f175,f35])).

fof(f35,plain,
    ( v1_funct_2(sK2,sK0,sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f34])).

fof(f175,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK1)
    | r1_partfun1(sK1,sK2)
    | ~ spl5_1
    | ~ spl5_5
    | ~ spl5_15
    | ~ spl5_23 ),
    inference(subsumption_resolution,[],[f174,f27])).

fof(f174,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK1)
    | r1_partfun1(sK1,sK2)
    | ~ spl5_5
    | ~ spl5_15
    | ~ spl5_23 ),
    inference(subsumption_resolution,[],[f173,f43])).

fof(f43,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f42])).

fof(f173,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK1)
    | r1_partfun1(sK1,sK2)
    | ~ spl5_15
    | ~ spl5_23 ),
    inference(trivial_inequality_removal,[],[f172])).

fof(f172,plain,
    ( k1_funct_1(sK1,sK4(sK0,sK0,sK1,sK2)) != k1_funct_1(sK1,sK4(sK0,sK0,sK1,sK2))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK1)
    | r1_partfun1(sK1,sK2)
    | ~ spl5_15
    | ~ spl5_23 ),
    inference(superposition,[],[f86,f146])).

fof(f146,plain,
    ( k1_funct_1(sK1,sK4(sK0,sK0,sK1,sK2)) = k1_funct_1(sK2,sK4(sK0,sK0,sK1,sK2))
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f145])).

fof(f86,plain,
    ( ! [X2,X0,X3,X1] :
        ( k1_funct_1(X2,sK4(X0,X1,X2,X3)) != k1_funct_1(X3,sK4(X0,X1,X2,X3))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X0,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | ~ v1_funct_1(X2)
        | r1_partfun1(X2,X3) )
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f85])).

fof(f170,plain,
    ( ~ spl5_7
    | spl5_8
    | ~ spl5_9 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | ~ spl5_7
    | spl5_8
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f167,f54])).

fof(f167,plain,
    ( k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(resolution,[],[f59,f50])).

fof(f50,plain,
    ( r2_hidden(sK3,k1_relset_1(sK0,sK0,sK1))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl5_7
  <=> r2_hidden(sK3,k1_relset_1(sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f59,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_relset_1(sK0,sK0,sK1))
        | k1_funct_1(sK1,X3) = k1_funct_1(sK2,X3) )
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl5_9
  <=> ! [X3] :
        ( ~ r2_hidden(X3,k1_relset_1(sK0,sK0,sK1))
        | k1_funct_1(sK1,X3) = k1_funct_1(sK2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f162,plain,
    ( spl5_24
    | ~ spl5_9
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f153,f98,f58,f160])).

fof(f153,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_relset_1(k1_xboole_0,k1_xboole_0,sK1))
        | k1_funct_1(sK1,X3) = k1_funct_1(sK2,X3) )
    | ~ spl5_9
    | ~ spl5_17 ),
    inference(backward_demodulation,[],[f59,f99])).

fof(f99,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f98])).

fof(f147,plain,
    ( spl5_23
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | spl5_6
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f143,f123,f46,f38,f34,f26,f145])).

fof(f123,plain,
    ( spl5_21
  <=> ! [X0] :
        ( k1_funct_1(sK1,sK4(sK0,sK0,sK1,X0)) = k1_funct_1(sK2,sK4(sK0,sK0,sK1,X0))
        | r1_partfun1(sK1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_2(X0,sK0,sK0)
        | ~ v1_funct_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f143,plain,
    ( k1_funct_1(sK1,sK4(sK0,sK0,sK1,sK2)) = k1_funct_1(sK2,sK4(sK0,sK0,sK1,sK2))
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | spl5_6
    | ~ spl5_21 ),
    inference(subsumption_resolution,[],[f142,f27])).

fof(f142,plain,
    ( k1_funct_1(sK1,sK4(sK0,sK0,sK1,sK2)) = k1_funct_1(sK2,sK4(sK0,sK0,sK1,sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl5_3
    | ~ spl5_4
    | spl5_6
    | ~ spl5_21 ),
    inference(subsumption_resolution,[],[f141,f39])).

fof(f141,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_funct_1(sK1,sK4(sK0,sK0,sK1,sK2)) = k1_funct_1(sK2,sK4(sK0,sK0,sK1,sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl5_3
    | spl5_6
    | ~ spl5_21 ),
    inference(subsumption_resolution,[],[f140,f47])).

fof(f140,plain,
    ( r1_partfun1(sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_funct_1(sK1,sK4(sK0,sK0,sK1,sK2)) = k1_funct_1(sK2,sK4(sK0,sK0,sK1,sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl5_3
    | ~ spl5_21 ),
    inference(resolution,[],[f124,f35])).

fof(f124,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,sK0,sK0)
        | r1_partfun1(sK1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_funct_1(sK1,sK4(sK0,sK0,sK1,X0)) = k1_funct_1(sK2,sK4(sK0,sK0,sK1,X0))
        | ~ v1_funct_1(X0) )
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f123])).

fof(f137,plain,
    ( spl5_22
    | ~ spl5_4
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f127,f98,f38,f135])).

fof(f127,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl5_4
    | ~ spl5_17 ),
    inference(backward_demodulation,[],[f39,f99])).

fof(f125,plain,
    ( spl5_17
    | spl5_21
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_9
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f121,f66,f58,f42,f30,f123,f98])).

fof(f66,plain,
    ( spl5_11
  <=> ! [X1,X3,X0,X2] :
        ( ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X0,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | r2_hidden(sK4(X0,X1,X2,X3),k1_relset_1(X0,X1,X2))
        | r1_partfun1(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f121,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,sK4(sK0,sK0,sK1,X0)) = k1_funct_1(sK2,sK4(sK0,sK0,sK1,X0))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,sK0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | r1_partfun1(sK1,X0) )
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_9
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f120,f31])).

fof(f120,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,sK4(sK0,sK0,sK1,X0)) = k1_funct_1(sK2,sK4(sK0,sK0,sK1,X0))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,sK0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | ~ v1_funct_1(sK1)
        | r1_partfun1(sK1,X0) )
    | ~ spl5_5
    | ~ spl5_9
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f119,f43])).

fof(f119,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,sK4(sK0,sK0,sK1,X0)) = k1_funct_1(sK2,sK4(sK0,sK0,sK1,X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,sK0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | ~ v1_funct_1(sK1)
        | r1_partfun1(sK1,X0) )
    | ~ spl5_9
    | ~ spl5_11 ),
    inference(resolution,[],[f59,f67])).

fof(f67,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_hidden(sK4(X0,X1,X2,X3),k1_relset_1(X0,X1,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X0,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | ~ v1_funct_1(X2)
        | r1_partfun1(X2,X3) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f66])).

fof(f117,plain,
    ( spl5_20
    | ~ spl5_5
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f102,f98,f42,f115])).

fof(f102,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl5_5
    | ~ spl5_17 ),
    inference(backward_demodulation,[],[f43,f99])).

fof(f112,plain,
    ( spl5_19
    | ~ spl5_7
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f101,f98,f49,f110])).

fof(f101,plain,
    ( r2_hidden(sK3,k1_relset_1(k1_xboole_0,k1_xboole_0,sK1))
    | ~ spl5_7
    | ~ spl5_17 ),
    inference(backward_demodulation,[],[f50,f99])).

fof(f108,plain,
    ( spl5_18
    | ~ spl5_3
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f104,f98,f34,f106])).

fof(f104,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl5_3
    | ~ spl5_17 ),
    inference(backward_demodulation,[],[f35,f99])).

fof(f100,plain,
    ( spl5_9
    | spl5_17
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f96,f89,f42,f38,f34,f98,f58])).

fof(f89,plain,
    ( spl5_16
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | ~ r2_hidden(X2,k1_relset_1(X0,X1,sK1))
        | k1_funct_1(sK1,X2) = k1_funct_1(sK2,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f96,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK0
        | ~ r2_hidden(X0,k1_relset_1(sK0,sK0,sK1))
        | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) )
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f95,f43])).

fof(f95,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | ~ r2_hidden(X0,k1_relset_1(sK0,sK0,sK1))
        | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) )
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f94,f35])).

fof(f94,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,sK0,sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | ~ r2_hidden(X0,k1_relset_1(sK0,sK0,sK1))
        | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) )
    | ~ spl5_4
    | ~ spl5_16 ),
    inference(resolution,[],[f90,f39])).

fof(f90,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | ~ r2_hidden(X2,k1_relset_1(X0,X1,sK1))
        | k1_funct_1(sK1,X2) = k1_funct_1(sK2,X2) )
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f89])).

fof(f91,plain,
    ( spl5_16
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f83,f78,f46,f30,f26,f89])).

fof(f78,plain,
    ( spl5_14
  <=> ! [X1,X3,X0,X2,X4] :
        ( ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X0,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2))
        | k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
        | ~ r1_partfun1(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f83,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | ~ r2_hidden(X2,k1_relset_1(X0,X1,sK1))
        | k1_funct_1(sK1,X2) = k1_funct_1(sK2,X2) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f82,f31])).

fof(f82,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | ~ r2_hidden(X2,k1_relset_1(X0,X1,sK1))
        | k1_funct_1(sK1,X2) = k1_funct_1(sK2,X2)
        | ~ v1_funct_1(sK1) )
    | ~ spl5_1
    | ~ spl5_6
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f81,f27])).

fof(f81,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | ~ r2_hidden(X2,k1_relset_1(X0,X1,sK1))
        | k1_funct_1(sK1,X2) = k1_funct_1(sK2,X2)
        | ~ v1_funct_1(sK1) )
    | ~ spl5_6
    | ~ spl5_14 ),
    inference(resolution,[],[f79,f56])).

fof(f79,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ r1_partfun1(X2,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X0,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2))
        | k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
        | ~ v1_funct_1(X2) )
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f78])).

fof(f87,plain,(
    spl5_15 ),
    inference(avatar_split_clause,[],[f18,f85])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_funct_1(X2,sK4(X0,X1,X2,X3)) != k1_funct_1(X3,sK4(X0,X1,X2,X3))
      | r1_partfun1(X2,X3) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r1_partfun1(X2,X3)
          <=> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r1_partfun1(X2,X3)
          <=> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ( k1_xboole_0 = X1
             => k1_xboole_0 = X0 )
           => ( r1_partfun1(X2,X3)
            <=> ! [X4] :
                  ( r2_hidden(X4,k1_relset_1(X0,X1,X2))
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_2)).

fof(f80,plain,(
    spl5_14 ),
    inference(avatar_split_clause,[],[f16,f78])).

fof(f16,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2))
      | k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
      | ~ r1_partfun1(X2,X3) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f76,plain,(
    spl5_13 ),
    inference(avatar_split_clause,[],[f22,f74])).

fof(f22,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,k1_xboole_0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_funct_1(X2,sK4(k1_xboole_0,X1,X2,X3)) != k1_funct_1(X3,sK4(k1_xboole_0,X1,X2,X3))
      | r1_partfun1(X2,X3) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_funct_1(X2,sK4(X0,X1,X2,X3)) != k1_funct_1(X3,sK4(X0,X1,X2,X3))
      | r1_partfun1(X2,X3) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f72,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f24,f70])).

fof(f24,plain,(
    ! [X4,X2,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,k1_xboole_0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ r2_hidden(X4,k1_relset_1(k1_xboole_0,X1,X2))
      | k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
      | ~ r1_partfun1(X2,X3) ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2))
      | k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
      | ~ r1_partfun1(X2,X3) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f68,plain,(
    spl5_11 ),
    inference(avatar_split_clause,[],[f17,f66])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | r2_hidden(sK4(X0,X1,X2,X3),k1_relset_1(X0,X1,X2))
      | r1_partfun1(X2,X3) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f64,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f23,f62])).

fof(f23,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,k1_xboole_0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | r2_hidden(sK4(k1_xboole_0,X1,X2,X3),k1_relset_1(k1_xboole_0,X1,X2))
      | r1_partfun1(X2,X3) ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | r2_hidden(sK4(X0,X1,X2,X3),k1_relset_1(X0,X1,X2))
      | r1_partfun1(X2,X3) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f60,plain,
    ( spl5_6
    | spl5_9 ),
    inference(avatar_split_clause,[],[f10,f58,f46])).

fof(f10,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_relset_1(sK0,sK0,sK1))
      | k1_funct_1(sK1,X3) = k1_funct_1(sK2,X3)
      | r1_partfun1(sK1,sK2) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_partfun1(X1,X2)
          <~> ! [X3] :
                ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
                | ~ r2_hidden(X3,k1_relset_1(X0,X0,X1)) ) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f4])).

fof(f4,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_partfun1(X1,X2)
          <~> ! [X3] :
                ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
                | ~ r2_hidden(X3,k1_relset_1(X0,X0,X1)) ) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( r1_partfun1(X1,X2)
            <=> ! [X3] :
                  ( r2_hidden(X3,k1_relset_1(X0,X0,X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) ) ) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( r1_partfun1(X1,X2)
          <=> ! [X3] :
                ( r2_hidden(X3,k1_relset_1(X0,X0,X1))
               => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_2)).

fof(f55,plain,
    ( ~ spl5_6
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f9,f53,f46])).

fof(f9,plain,
    ( k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3)
    | ~ r1_partfun1(sK1,sK2) ),
    inference(cnf_transformation,[],[f5])).

fof(f51,plain,
    ( ~ spl5_6
    | spl5_7 ),
    inference(avatar_split_clause,[],[f8,f49,f46])).

fof(f8,plain,
    ( r2_hidden(sK3,k1_relset_1(sK0,sK0,sK1))
    | ~ r1_partfun1(sK1,sK2) ),
    inference(cnf_transformation,[],[f5])).

fof(f44,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f15,f42])).

fof(f15,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f5])).

fof(f40,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f13,f38])).

fof(f13,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f5])).

fof(f36,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f12,f34])).

fof(f12,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f5])).

fof(f32,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f14,f30])).

fof(f14,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f5])).

fof(f28,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f11,f26])).

fof(f11,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f5])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:57:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.43  % (24251)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.45  % (24251)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f277,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f28,f32,f36,f40,f44,f51,f55,f60,f64,f68,f72,f76,f80,f87,f91,f100,f108,f112,f117,f125,f137,f147,f162,f170,f191,f210,f229,f252,f264,f274])).
% 0.21/0.45  fof(f274,plain,(
% 0.21/0.45    ~spl5_1 | ~spl5_2 | ~spl5_6 | spl5_8 | ~spl5_12 | ~spl5_18 | ~spl5_19 | ~spl5_20 | ~spl5_22),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f270])).
% 0.21/0.45  fof(f270,plain,(
% 0.21/0.45    $false | (~spl5_1 | ~spl5_2 | ~spl5_6 | spl5_8 | ~spl5_12 | ~spl5_18 | ~spl5_19 | ~spl5_20 | ~spl5_22)),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f31,f27,f56,f107,f136,f54,f116,f111,f71])).
% 0.21/0.45  fof(f71,plain,(
% 0.21/0.45    ( ! [X4,X2,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,k1_xboole_0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~r2_hidden(X4,k1_relset_1(k1_xboole_0,X1,X2)) | k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r1_partfun1(X2,X3)) ) | ~spl5_12),
% 0.21/0.45    inference(avatar_component_clause,[],[f70])).
% 0.21/0.45  fof(f70,plain,(
% 0.21/0.45    spl5_12 <=> ! [X1,X3,X2,X4] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,k1_xboole_0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~r2_hidden(X4,k1_relset_1(k1_xboole_0,X1,X2)) | k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r1_partfun1(X2,X3))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.45  fof(f111,plain,(
% 0.21/0.45    r2_hidden(sK3,k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)) | ~spl5_19),
% 0.21/0.45    inference(avatar_component_clause,[],[f110])).
% 0.21/0.45  fof(f110,plain,(
% 0.21/0.45    spl5_19 <=> r2_hidden(sK3,k1_relset_1(k1_xboole_0,k1_xboole_0,sK1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.21/0.45  fof(f116,plain,(
% 0.21/0.45    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl5_20),
% 0.21/0.45    inference(avatar_component_clause,[],[f115])).
% 0.21/0.45  fof(f115,plain,(
% 0.21/0.45    spl5_20 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.21/0.45  fof(f54,plain,(
% 0.21/0.45    k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3) | spl5_8),
% 0.21/0.45    inference(avatar_component_clause,[],[f53])).
% 0.21/0.45  fof(f53,plain,(
% 0.21/0.45    spl5_8 <=> k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.45  fof(f136,plain,(
% 0.21/0.45    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl5_22),
% 0.21/0.45    inference(avatar_component_clause,[],[f135])).
% 0.21/0.45  fof(f135,plain,(
% 0.21/0.45    spl5_22 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.21/0.45  fof(f107,plain,(
% 0.21/0.45    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~spl5_18),
% 0.21/0.45    inference(avatar_component_clause,[],[f106])).
% 0.21/0.45  fof(f106,plain,(
% 0.21/0.45    spl5_18 <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.21/0.45  fof(f56,plain,(
% 0.21/0.45    r1_partfun1(sK1,sK2) | ~spl5_6),
% 0.21/0.45    inference(avatar_component_clause,[],[f46])).
% 0.21/0.45  fof(f46,plain,(
% 0.21/0.45    spl5_6 <=> r1_partfun1(sK1,sK2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    v1_funct_1(sK2) | ~spl5_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f26])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    spl5_1 <=> v1_funct_1(sK2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    v1_funct_1(sK1) | ~spl5_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f30])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    spl5_2 <=> v1_funct_1(sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.45  fof(f264,plain,(
% 0.21/0.45    ~spl5_1 | spl5_6 | ~spl5_18 | ~spl5_22 | ~spl5_27 | ~spl5_34),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f263])).
% 0.21/0.45  fof(f263,plain,(
% 0.21/0.45    $false | (~spl5_1 | spl5_6 | ~spl5_18 | ~spl5_22 | ~spl5_27 | ~spl5_34)),
% 0.21/0.45    inference(subsumption_resolution,[],[f262,f47])).
% 0.21/0.45  fof(f47,plain,(
% 0.21/0.45    ~r1_partfun1(sK1,sK2) | spl5_6),
% 0.21/0.45    inference(avatar_component_clause,[],[f46])).
% 0.21/0.45  fof(f262,plain,(
% 0.21/0.45    r1_partfun1(sK1,sK2) | (~spl5_1 | ~spl5_18 | ~spl5_22 | ~spl5_27 | ~spl5_34)),
% 0.21/0.45    inference(subsumption_resolution,[],[f261,f27])).
% 0.21/0.45  fof(f261,plain,(
% 0.21/0.45    ~v1_funct_1(sK2) | r1_partfun1(sK1,sK2) | (~spl5_18 | ~spl5_22 | ~spl5_27 | ~spl5_34)),
% 0.21/0.45    inference(subsumption_resolution,[],[f260,f136])).
% 0.21/0.45  fof(f260,plain,(
% 0.21/0.45    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_1(sK2) | r1_partfun1(sK1,sK2) | (~spl5_18 | ~spl5_27 | ~spl5_34)),
% 0.21/0.45    inference(subsumption_resolution,[],[f257,f107])).
% 0.21/0.45  fof(f257,plain,(
% 0.21/0.45    ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_1(sK2) | r1_partfun1(sK1,sK2) | (~spl5_27 | ~spl5_34)),
% 0.21/0.45    inference(trivial_inequality_removal,[],[f255])).
% 0.21/0.45  fof(f255,plain,(
% 0.21/0.45    k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2)) != k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2)) | ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_1(sK2) | r1_partfun1(sK1,sK2) | (~spl5_27 | ~spl5_34)),
% 0.21/0.45    inference(superposition,[],[f209,f251])).
% 0.21/0.45  fof(f251,plain,(
% 0.21/0.45    k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2)) = k1_funct_1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2)) | ~spl5_34),
% 0.21/0.45    inference(avatar_component_clause,[],[f250])).
% 0.21/0.45  fof(f250,plain,(
% 0.21/0.45    spl5_34 <=> k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2)) = k1_funct_1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 0.21/0.45  fof(f209,plain,(
% 0.21/0.45    ( ! [X0] : (k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,X0)) != k1_funct_1(X0,sK4(k1_xboole_0,k1_xboole_0,sK1,X0)) | ~v1_funct_2(X0,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_1(X0) | r1_partfun1(sK1,X0)) ) | ~spl5_27),
% 0.21/0.45    inference(avatar_component_clause,[],[f208])).
% 0.21/0.45  fof(f208,plain,(
% 0.21/0.45    spl5_27 <=> ! [X0] : (~v1_funct_1(X0) | ~v1_funct_2(X0,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,X0)) != k1_funct_1(X0,sK4(k1_xboole_0,k1_xboole_0,sK1,X0)) | r1_partfun1(sK1,X0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.21/0.45  fof(f252,plain,(
% 0.21/0.45    spl5_34 | ~spl5_1 | spl5_6 | ~spl5_18 | ~spl5_22 | ~spl5_30),
% 0.21/0.45    inference(avatar_split_clause,[],[f236,f227,f135,f106,f46,f26,f250])).
% 0.21/0.45  fof(f227,plain,(
% 0.21/0.45    spl5_30 <=> ! [X0] : (k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,X0)) = k1_funct_1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK1,X0)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | r1_partfun1(sK1,X0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 0.21/0.45  fof(f236,plain,(
% 0.21/0.45    k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2)) = k1_funct_1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2)) | (~spl5_1 | spl5_6 | ~spl5_18 | ~spl5_22 | ~spl5_30)),
% 0.21/0.45    inference(subsumption_resolution,[],[f235,f47])).
% 0.21/0.45  fof(f235,plain,(
% 0.21/0.45    k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2)) = k1_funct_1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2)) | r1_partfun1(sK1,sK2) | (~spl5_1 | ~spl5_18 | ~spl5_22 | ~spl5_30)),
% 0.21/0.45    inference(subsumption_resolution,[],[f234,f136])).
% 0.21/0.45  fof(f234,plain,(
% 0.21/0.45    k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2)) = k1_funct_1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | r1_partfun1(sK1,sK2) | (~spl5_1 | ~spl5_18 | ~spl5_30)),
% 0.21/0.45    inference(subsumption_resolution,[],[f233,f27])).
% 0.21/0.45  fof(f233,plain,(
% 0.21/0.45    ~v1_funct_1(sK2) | k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2)) = k1_funct_1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | r1_partfun1(sK1,sK2) | (~spl5_18 | ~spl5_30)),
% 0.21/0.45    inference(resolution,[],[f228,f107])).
% 0.21/0.45  fof(f228,plain,(
% 0.21/0.45    ( ! [X0] : (~v1_funct_2(X0,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(X0) | k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,X0)) = k1_funct_1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK1,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | r1_partfun1(sK1,X0)) ) | ~spl5_30),
% 0.21/0.45    inference(avatar_component_clause,[],[f227])).
% 0.21/0.45  fof(f229,plain,(
% 0.21/0.45    spl5_30 | ~spl5_2 | ~spl5_10 | ~spl5_20 | ~spl5_24),
% 0.21/0.45    inference(avatar_split_clause,[],[f193,f160,f115,f62,f30,f227])).
% 0.21/0.45  fof(f62,plain,(
% 0.21/0.45    spl5_10 <=> ! [X1,X3,X2] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,k1_xboole_0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | r2_hidden(sK4(k1_xboole_0,X1,X2,X3),k1_relset_1(k1_xboole_0,X1,X2)) | r1_partfun1(X2,X3))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.45  fof(f160,plain,(
% 0.21/0.45    spl5_24 <=> ! [X3] : (~r2_hidden(X3,k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)) | k1_funct_1(sK1,X3) = k1_funct_1(sK2,X3))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.21/0.45  fof(f193,plain,(
% 0.21/0.45    ( ! [X0] : (k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,X0)) = k1_funct_1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK1,X0)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | r1_partfun1(sK1,X0)) ) | (~spl5_2 | ~spl5_10 | ~spl5_20 | ~spl5_24)),
% 0.21/0.45    inference(subsumption_resolution,[],[f192,f31])).
% 0.21/0.45  fof(f192,plain,(
% 0.21/0.45    ( ! [X0] : (k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,X0)) = k1_funct_1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK1,X0)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_1(sK1) | r1_partfun1(sK1,X0)) ) | (~spl5_10 | ~spl5_20 | ~spl5_24)),
% 0.21/0.45    inference(subsumption_resolution,[],[f189,f116])).
% 0.21/0.45  fof(f189,plain,(
% 0.21/0.45    ( ! [X0] : (k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,X0)) = k1_funct_1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK1,X0)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_1(sK1) | r1_partfun1(sK1,X0)) ) | (~spl5_10 | ~spl5_24)),
% 0.21/0.45    inference(resolution,[],[f161,f63])).
% 0.21/0.45  fof(f63,plain,(
% 0.21/0.45    ( ! [X2,X3,X1] : (r2_hidden(sK4(k1_xboole_0,X1,X2,X3),k1_relset_1(k1_xboole_0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,k1_xboole_0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X2) | r1_partfun1(X2,X3)) ) | ~spl5_10),
% 0.21/0.45    inference(avatar_component_clause,[],[f62])).
% 0.21/0.45  fof(f161,plain,(
% 0.21/0.45    ( ! [X3] : (~r2_hidden(X3,k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)) | k1_funct_1(sK1,X3) = k1_funct_1(sK2,X3)) ) | ~spl5_24),
% 0.21/0.45    inference(avatar_component_clause,[],[f160])).
% 0.21/0.45  fof(f210,plain,(
% 0.21/0.45    spl5_27 | ~spl5_2 | ~spl5_13 | ~spl5_20),
% 0.21/0.45    inference(avatar_split_clause,[],[f132,f115,f74,f30,f208])).
% 0.21/0.45  fof(f74,plain,(
% 0.21/0.45    spl5_13 <=> ! [X1,X3,X2] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,k1_xboole_0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_funct_1(X2,sK4(k1_xboole_0,X1,X2,X3)) != k1_funct_1(X3,sK4(k1_xboole_0,X1,X2,X3)) | r1_partfun1(X2,X3))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.45  fof(f132,plain,(
% 0.21/0.45    ( ! [X0] : (~v1_funct_1(X0) | ~v1_funct_2(X0,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,X0)) != k1_funct_1(X0,sK4(k1_xboole_0,k1_xboole_0,sK1,X0)) | r1_partfun1(sK1,X0)) ) | (~spl5_2 | ~spl5_13 | ~spl5_20)),
% 0.21/0.45    inference(subsumption_resolution,[],[f130,f31])).
% 0.21/0.45  fof(f130,plain,(
% 0.21/0.45    ( ! [X0] : (~v1_funct_1(sK1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,X0)) != k1_funct_1(X0,sK4(k1_xboole_0,k1_xboole_0,sK1,X0)) | r1_partfun1(sK1,X0)) ) | (~spl5_13 | ~spl5_20)),
% 0.21/0.45    inference(resolution,[],[f116,f75])).
% 0.21/0.45  fof(f75,plain,(
% 0.21/0.45    ( ! [X2,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,k1_xboole_0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_funct_1(X2,sK4(k1_xboole_0,X1,X2,X3)) != k1_funct_1(X3,sK4(k1_xboole_0,X1,X2,X3)) | r1_partfun1(X2,X3)) ) | ~spl5_13),
% 0.21/0.45    inference(avatar_component_clause,[],[f74])).
% 0.21/0.45  fof(f191,plain,(
% 0.21/0.45    spl5_17 | ~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | spl5_6 | ~spl5_15 | ~spl5_23),
% 0.21/0.45    inference(avatar_split_clause,[],[f179,f145,f85,f46,f42,f38,f34,f30,f26,f98])).
% 0.21/0.45  fof(f98,plain,(
% 0.21/0.45    spl5_17 <=> k1_xboole_0 = sK0),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    spl5_3 <=> v1_funct_2(sK2,sK0,sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.45  fof(f38,plain,(
% 0.21/0.45    spl5_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.45  fof(f42,plain,(
% 0.21/0.45    spl5_5 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.45  fof(f85,plain,(
% 0.21/0.45    spl5_15 <=> ! [X1,X3,X0,X2] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_funct_1(X2,sK4(X0,X1,X2,X3)) != k1_funct_1(X3,sK4(X0,X1,X2,X3)) | r1_partfun1(X2,X3))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.45  fof(f145,plain,(
% 0.21/0.45    spl5_23 <=> k1_funct_1(sK1,sK4(sK0,sK0,sK1,sK2)) = k1_funct_1(sK2,sK4(sK0,sK0,sK1,sK2))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.21/0.45  fof(f179,plain,(
% 0.21/0.45    k1_xboole_0 = sK0 | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | spl5_6 | ~spl5_15 | ~spl5_23)),
% 0.21/0.45    inference(subsumption_resolution,[],[f178,f47])).
% 0.21/0.45  fof(f178,plain,(
% 0.21/0.45    k1_xboole_0 = sK0 | r1_partfun1(sK1,sK2) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_15 | ~spl5_23)),
% 0.21/0.45    inference(subsumption_resolution,[],[f177,f31])).
% 0.21/0.45  fof(f177,plain,(
% 0.21/0.45    k1_xboole_0 = sK0 | ~v1_funct_1(sK1) | r1_partfun1(sK1,sK2) | (~spl5_1 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_15 | ~spl5_23)),
% 0.21/0.45    inference(subsumption_resolution,[],[f176,f39])).
% 0.21/0.45  fof(f39,plain,(
% 0.21/0.45    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl5_4),
% 0.21/0.45    inference(avatar_component_clause,[],[f38])).
% 0.21/0.45  fof(f176,plain,(
% 0.21/0.45    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_xboole_0 = sK0 | ~v1_funct_1(sK1) | r1_partfun1(sK1,sK2) | (~spl5_1 | ~spl5_3 | ~spl5_5 | ~spl5_15 | ~spl5_23)),
% 0.21/0.45    inference(subsumption_resolution,[],[f175,f35])).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    v1_funct_2(sK2,sK0,sK0) | ~spl5_3),
% 0.21/0.45    inference(avatar_component_clause,[],[f34])).
% 0.21/0.45  fof(f175,plain,(
% 0.21/0.45    ~v1_funct_2(sK2,sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_xboole_0 = sK0 | ~v1_funct_1(sK1) | r1_partfun1(sK1,sK2) | (~spl5_1 | ~spl5_5 | ~spl5_15 | ~spl5_23)),
% 0.21/0.45    inference(subsumption_resolution,[],[f174,f27])).
% 0.21/0.45  fof(f174,plain,(
% 0.21/0.45    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_xboole_0 = sK0 | ~v1_funct_1(sK1) | r1_partfun1(sK1,sK2) | (~spl5_5 | ~spl5_15 | ~spl5_23)),
% 0.21/0.45    inference(subsumption_resolution,[],[f173,f43])).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl5_5),
% 0.21/0.45    inference(avatar_component_clause,[],[f42])).
% 0.21/0.45  fof(f173,plain,(
% 0.21/0.45    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_xboole_0 = sK0 | ~v1_funct_1(sK1) | r1_partfun1(sK1,sK2) | (~spl5_15 | ~spl5_23)),
% 0.21/0.45    inference(trivial_inequality_removal,[],[f172])).
% 0.21/0.45  fof(f172,plain,(
% 0.21/0.45    k1_funct_1(sK1,sK4(sK0,sK0,sK1,sK2)) != k1_funct_1(sK1,sK4(sK0,sK0,sK1,sK2)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_xboole_0 = sK0 | ~v1_funct_1(sK1) | r1_partfun1(sK1,sK2) | (~spl5_15 | ~spl5_23)),
% 0.21/0.45    inference(superposition,[],[f86,f146])).
% 0.21/0.45  fof(f146,plain,(
% 0.21/0.45    k1_funct_1(sK1,sK4(sK0,sK0,sK1,sK2)) = k1_funct_1(sK2,sK4(sK0,sK0,sK1,sK2)) | ~spl5_23),
% 0.21/0.45    inference(avatar_component_clause,[],[f145])).
% 0.21/0.45  fof(f86,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (k1_funct_1(X2,sK4(X0,X1,X2,X3)) != k1_funct_1(X3,sK4(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~v1_funct_1(X2) | r1_partfun1(X2,X3)) ) | ~spl5_15),
% 0.21/0.45    inference(avatar_component_clause,[],[f85])).
% 0.21/0.45  fof(f170,plain,(
% 0.21/0.45    ~spl5_7 | spl5_8 | ~spl5_9),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f169])).
% 0.21/0.45  fof(f169,plain,(
% 0.21/0.45    $false | (~spl5_7 | spl5_8 | ~spl5_9)),
% 0.21/0.45    inference(subsumption_resolution,[],[f167,f54])).
% 0.21/0.45  fof(f167,plain,(
% 0.21/0.45    k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3) | (~spl5_7 | ~spl5_9)),
% 0.21/0.45    inference(resolution,[],[f59,f50])).
% 0.21/0.45  fof(f50,plain,(
% 0.21/0.45    r2_hidden(sK3,k1_relset_1(sK0,sK0,sK1)) | ~spl5_7),
% 0.21/0.45    inference(avatar_component_clause,[],[f49])).
% 0.21/0.45  fof(f49,plain,(
% 0.21/0.45    spl5_7 <=> r2_hidden(sK3,k1_relset_1(sK0,sK0,sK1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.45  fof(f59,plain,(
% 0.21/0.45    ( ! [X3] : (~r2_hidden(X3,k1_relset_1(sK0,sK0,sK1)) | k1_funct_1(sK1,X3) = k1_funct_1(sK2,X3)) ) | ~spl5_9),
% 0.21/0.45    inference(avatar_component_clause,[],[f58])).
% 0.21/0.45  fof(f58,plain,(
% 0.21/0.45    spl5_9 <=> ! [X3] : (~r2_hidden(X3,k1_relset_1(sK0,sK0,sK1)) | k1_funct_1(sK1,X3) = k1_funct_1(sK2,X3))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.45  fof(f162,plain,(
% 0.21/0.45    spl5_24 | ~spl5_9 | ~spl5_17),
% 0.21/0.45    inference(avatar_split_clause,[],[f153,f98,f58,f160])).
% 0.21/0.45  fof(f153,plain,(
% 0.21/0.45    ( ! [X3] : (~r2_hidden(X3,k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)) | k1_funct_1(sK1,X3) = k1_funct_1(sK2,X3)) ) | (~spl5_9 | ~spl5_17)),
% 0.21/0.45    inference(backward_demodulation,[],[f59,f99])).
% 0.21/0.45  fof(f99,plain,(
% 0.21/0.45    k1_xboole_0 = sK0 | ~spl5_17),
% 0.21/0.45    inference(avatar_component_clause,[],[f98])).
% 0.21/0.45  fof(f147,plain,(
% 0.21/0.45    spl5_23 | ~spl5_1 | ~spl5_3 | ~spl5_4 | spl5_6 | ~spl5_21),
% 0.21/0.45    inference(avatar_split_clause,[],[f143,f123,f46,f38,f34,f26,f145])).
% 0.21/0.45  fof(f123,plain,(
% 0.21/0.45    spl5_21 <=> ! [X0] : (k1_funct_1(sK1,sK4(sK0,sK0,sK1,X0)) = k1_funct_1(sK2,sK4(sK0,sK0,sK1,X0)) | r1_partfun1(sK1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(X0,sK0,sK0) | ~v1_funct_1(X0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.21/0.45  fof(f143,plain,(
% 0.21/0.45    k1_funct_1(sK1,sK4(sK0,sK0,sK1,sK2)) = k1_funct_1(sK2,sK4(sK0,sK0,sK1,sK2)) | (~spl5_1 | ~spl5_3 | ~spl5_4 | spl5_6 | ~spl5_21)),
% 0.21/0.45    inference(subsumption_resolution,[],[f142,f27])).
% 0.21/0.45  fof(f142,plain,(
% 0.21/0.45    k1_funct_1(sK1,sK4(sK0,sK0,sK1,sK2)) = k1_funct_1(sK2,sK4(sK0,sK0,sK1,sK2)) | ~v1_funct_1(sK2) | (~spl5_3 | ~spl5_4 | spl5_6 | ~spl5_21)),
% 0.21/0.45    inference(subsumption_resolution,[],[f141,f39])).
% 0.21/0.45  fof(f141,plain,(
% 0.21/0.45    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_funct_1(sK1,sK4(sK0,sK0,sK1,sK2)) = k1_funct_1(sK2,sK4(sK0,sK0,sK1,sK2)) | ~v1_funct_1(sK2) | (~spl5_3 | spl5_6 | ~spl5_21)),
% 0.21/0.45    inference(subsumption_resolution,[],[f140,f47])).
% 0.21/0.45  fof(f140,plain,(
% 0.21/0.45    r1_partfun1(sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_funct_1(sK1,sK4(sK0,sK0,sK1,sK2)) = k1_funct_1(sK2,sK4(sK0,sK0,sK1,sK2)) | ~v1_funct_1(sK2) | (~spl5_3 | ~spl5_21)),
% 0.21/0.45    inference(resolution,[],[f124,f35])).
% 0.21/0.45  fof(f124,plain,(
% 0.21/0.45    ( ! [X0] : (~v1_funct_2(X0,sK0,sK0) | r1_partfun1(sK1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_funct_1(sK1,sK4(sK0,sK0,sK1,X0)) = k1_funct_1(sK2,sK4(sK0,sK0,sK1,X0)) | ~v1_funct_1(X0)) ) | ~spl5_21),
% 0.21/0.45    inference(avatar_component_clause,[],[f123])).
% 0.21/0.45  fof(f137,plain,(
% 0.21/0.45    spl5_22 | ~spl5_4 | ~spl5_17),
% 0.21/0.45    inference(avatar_split_clause,[],[f127,f98,f38,f135])).
% 0.21/0.45  fof(f127,plain,(
% 0.21/0.45    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl5_4 | ~spl5_17)),
% 0.21/0.45    inference(backward_demodulation,[],[f39,f99])).
% 0.21/0.45  fof(f125,plain,(
% 0.21/0.45    spl5_17 | spl5_21 | ~spl5_2 | ~spl5_5 | ~spl5_9 | ~spl5_11),
% 0.21/0.45    inference(avatar_split_clause,[],[f121,f66,f58,f42,f30,f123,f98])).
% 0.21/0.45  fof(f66,plain,(
% 0.21/0.45    spl5_11 <=> ! [X1,X3,X0,X2] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | r2_hidden(sK4(X0,X1,X2,X3),k1_relset_1(X0,X1,X2)) | r1_partfun1(X2,X3))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.45  fof(f121,plain,(
% 0.21/0.45    ( ! [X0] : (k1_funct_1(sK1,sK4(sK0,sK0,sK1,X0)) = k1_funct_1(sK2,sK4(sK0,sK0,sK1,X0)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_xboole_0 = sK0 | r1_partfun1(sK1,X0)) ) | (~spl5_2 | ~spl5_5 | ~spl5_9 | ~spl5_11)),
% 0.21/0.45    inference(subsumption_resolution,[],[f120,f31])).
% 0.21/0.45  fof(f120,plain,(
% 0.21/0.45    ( ! [X0] : (k1_funct_1(sK1,sK4(sK0,sK0,sK1,X0)) = k1_funct_1(sK2,sK4(sK0,sK0,sK1,X0)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_xboole_0 = sK0 | ~v1_funct_1(sK1) | r1_partfun1(sK1,X0)) ) | (~spl5_5 | ~spl5_9 | ~spl5_11)),
% 0.21/0.45    inference(subsumption_resolution,[],[f119,f43])).
% 0.21/0.45  fof(f119,plain,(
% 0.21/0.45    ( ! [X0] : (k1_funct_1(sK1,sK4(sK0,sK0,sK1,X0)) = k1_funct_1(sK2,sK4(sK0,sK0,sK1,X0)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_xboole_0 = sK0 | ~v1_funct_1(sK1) | r1_partfun1(sK1,X0)) ) | (~spl5_9 | ~spl5_11)),
% 0.21/0.45    inference(resolution,[],[f59,f67])).
% 0.21/0.45  fof(f67,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (r2_hidden(sK4(X0,X1,X2,X3),k1_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~v1_funct_1(X2) | r1_partfun1(X2,X3)) ) | ~spl5_11),
% 0.21/0.45    inference(avatar_component_clause,[],[f66])).
% 0.21/0.45  fof(f117,plain,(
% 0.21/0.45    spl5_20 | ~spl5_5 | ~spl5_17),
% 0.21/0.45    inference(avatar_split_clause,[],[f102,f98,f42,f115])).
% 0.21/0.45  fof(f102,plain,(
% 0.21/0.45    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl5_5 | ~spl5_17)),
% 0.21/0.45    inference(backward_demodulation,[],[f43,f99])).
% 0.21/0.45  fof(f112,plain,(
% 0.21/0.45    spl5_19 | ~spl5_7 | ~spl5_17),
% 0.21/0.45    inference(avatar_split_clause,[],[f101,f98,f49,f110])).
% 0.21/0.45  fof(f101,plain,(
% 0.21/0.45    r2_hidden(sK3,k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)) | (~spl5_7 | ~spl5_17)),
% 0.21/0.45    inference(backward_demodulation,[],[f50,f99])).
% 0.21/0.45  fof(f108,plain,(
% 0.21/0.45    spl5_18 | ~spl5_3 | ~spl5_17),
% 0.21/0.45    inference(avatar_split_clause,[],[f104,f98,f34,f106])).
% 0.21/0.45  fof(f104,plain,(
% 0.21/0.45    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl5_3 | ~spl5_17)),
% 0.21/0.45    inference(backward_demodulation,[],[f35,f99])).
% 0.21/0.45  fof(f100,plain,(
% 0.21/0.45    spl5_9 | spl5_17 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_16),
% 0.21/0.45    inference(avatar_split_clause,[],[f96,f89,f42,f38,f34,f98,f58])).
% 0.21/0.45  fof(f89,plain,(
% 0.21/0.45    spl5_16 <=> ! [X1,X0,X2] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r2_hidden(X2,k1_relset_1(X0,X1,sK1)) | k1_funct_1(sK1,X2) = k1_funct_1(sK2,X2))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.45  fof(f96,plain,(
% 0.21/0.45    ( ! [X0] : (k1_xboole_0 = sK0 | ~r2_hidden(X0,k1_relset_1(sK0,sK0,sK1)) | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)) ) | (~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_16)),
% 0.21/0.45    inference(subsumption_resolution,[],[f95,f43])).
% 0.21/0.45  fof(f95,plain,(
% 0.21/0.45    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_xboole_0 = sK0 | ~r2_hidden(X0,k1_relset_1(sK0,sK0,sK1)) | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)) ) | (~spl5_3 | ~spl5_4 | ~spl5_16)),
% 0.21/0.45    inference(subsumption_resolution,[],[f94,f35])).
% 0.21/0.45  fof(f94,plain,(
% 0.21/0.45    ( ! [X0] : (~v1_funct_2(sK2,sK0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_xboole_0 = sK0 | ~r2_hidden(X0,k1_relset_1(sK0,sK0,sK1)) | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)) ) | (~spl5_4 | ~spl5_16)),
% 0.21/0.45    inference(resolution,[],[f90,f39])).
% 0.21/0.45  fof(f90,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r2_hidden(X2,k1_relset_1(X0,X1,sK1)) | k1_funct_1(sK1,X2) = k1_funct_1(sK2,X2)) ) | ~spl5_16),
% 0.21/0.45    inference(avatar_component_clause,[],[f89])).
% 0.21/0.45  fof(f91,plain,(
% 0.21/0.45    spl5_16 | ~spl5_1 | ~spl5_2 | ~spl5_6 | ~spl5_14),
% 0.21/0.45    inference(avatar_split_clause,[],[f83,f78,f46,f30,f26,f89])).
% 0.21/0.45  fof(f78,plain,(
% 0.21/0.45    spl5_14 <=> ! [X1,X3,X0,X2,X4] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r2_hidden(X4,k1_relset_1(X0,X1,X2)) | k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r1_partfun1(X2,X3))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.45  fof(f83,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r2_hidden(X2,k1_relset_1(X0,X1,sK1)) | k1_funct_1(sK1,X2) = k1_funct_1(sK2,X2)) ) | (~spl5_1 | ~spl5_2 | ~spl5_6 | ~spl5_14)),
% 0.21/0.45    inference(subsumption_resolution,[],[f82,f31])).
% 0.21/0.45  fof(f82,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r2_hidden(X2,k1_relset_1(X0,X1,sK1)) | k1_funct_1(sK1,X2) = k1_funct_1(sK2,X2) | ~v1_funct_1(sK1)) ) | (~spl5_1 | ~spl5_6 | ~spl5_14)),
% 0.21/0.45    inference(subsumption_resolution,[],[f81,f27])).
% 0.21/0.45  fof(f81,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r2_hidden(X2,k1_relset_1(X0,X1,sK1)) | k1_funct_1(sK1,X2) = k1_funct_1(sK2,X2) | ~v1_funct_1(sK1)) ) | (~spl5_6 | ~spl5_14)),
% 0.21/0.45    inference(resolution,[],[f79,f56])).
% 0.21/0.45  fof(f79,plain,(
% 0.21/0.45    ( ! [X4,X2,X0,X3,X1] : (~r1_partfun1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r2_hidden(X4,k1_relset_1(X0,X1,X2)) | k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~v1_funct_1(X2)) ) | ~spl5_14),
% 0.21/0.45    inference(avatar_component_clause,[],[f78])).
% 0.21/0.45  fof(f87,plain,(
% 0.21/0.45    spl5_15),
% 0.21/0.45    inference(avatar_split_clause,[],[f18,f85])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_funct_1(X2,sK4(X0,X1,X2,X3)) != k1_funct_1(X3,sK4(X0,X1,X2,X3)) | r1_partfun1(X2,X3)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (! [X3] : ((r1_partfun1(X2,X3) <=> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2)))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.45    inference(flattening,[],[f6])).
% 0.21/0.45  fof(f6,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (! [X3] : (((r1_partfun1(X2,X3) <=> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2)))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.45    inference(ennf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (r1_partfun1(X2,X3) <=> ! [X4] : (r2_hidden(X4,k1_relset_1(X0,X1,X2)) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4))))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_2)).
% 0.21/0.45  fof(f80,plain,(
% 0.21/0.45    spl5_14),
% 0.21/0.45    inference(avatar_split_clause,[],[f16,f78])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r2_hidden(X4,k1_relset_1(X0,X1,X2)) | k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r1_partfun1(X2,X3)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f7])).
% 0.21/0.45  fof(f76,plain,(
% 0.21/0.45    spl5_13),
% 0.21/0.45    inference(avatar_split_clause,[],[f22,f74])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    ( ! [X2,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,k1_xboole_0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_funct_1(X2,sK4(k1_xboole_0,X1,X2,X3)) != k1_funct_1(X3,sK4(k1_xboole_0,X1,X2,X3)) | r1_partfun1(X2,X3)) )),
% 0.21/0.45    inference(equality_resolution,[],[f21])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_funct_1(X2,sK4(X0,X1,X2,X3)) != k1_funct_1(X3,sK4(X0,X1,X2,X3)) | r1_partfun1(X2,X3)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f7])).
% 0.21/0.45  fof(f72,plain,(
% 0.21/0.45    spl5_12),
% 0.21/0.45    inference(avatar_split_clause,[],[f24,f70])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ( ! [X4,X2,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,k1_xboole_0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~r2_hidden(X4,k1_relset_1(k1_xboole_0,X1,X2)) | k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r1_partfun1(X2,X3)) )),
% 0.21/0.45    inference(equality_resolution,[],[f19])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | ~r2_hidden(X4,k1_relset_1(X0,X1,X2)) | k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r1_partfun1(X2,X3)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f7])).
% 0.21/0.45  fof(f68,plain,(
% 0.21/0.45    spl5_11),
% 0.21/0.45    inference(avatar_split_clause,[],[f17,f66])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | r2_hidden(sK4(X0,X1,X2,X3),k1_relset_1(X0,X1,X2)) | r1_partfun1(X2,X3)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f7])).
% 0.21/0.45  fof(f64,plain,(
% 0.21/0.45    spl5_10),
% 0.21/0.45    inference(avatar_split_clause,[],[f23,f62])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ( ! [X2,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,k1_xboole_0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | r2_hidden(sK4(k1_xboole_0,X1,X2,X3),k1_relset_1(k1_xboole_0,X1,X2)) | r1_partfun1(X2,X3)) )),
% 0.21/0.45    inference(equality_resolution,[],[f20])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | r2_hidden(sK4(X0,X1,X2,X3),k1_relset_1(X0,X1,X2)) | r1_partfun1(X2,X3)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f7])).
% 0.21/0.45  fof(f60,plain,(
% 0.21/0.45    spl5_6 | spl5_9),
% 0.21/0.45    inference(avatar_split_clause,[],[f10,f58,f46])).
% 0.21/0.45  fof(f10,plain,(
% 0.21/0.45    ( ! [X3] : (~r2_hidden(X3,k1_relset_1(sK0,sK0,sK1)) | k1_funct_1(sK1,X3) = k1_funct_1(sK2,X3) | r1_partfun1(sK1,sK2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,plain,(
% 0.21/0.45    ? [X0,X1] : (? [X2] : ((r1_partfun1(X1,X2) <~> ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X2,X3) | ~r2_hidden(X3,k1_relset_1(X0,X0,X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1))),
% 0.21/0.45    inference(flattening,[],[f4])).
% 0.21/0.45  fof(f4,plain,(
% 0.21/0.45    ? [X0,X1] : (? [X2] : ((r1_partfun1(X1,X2) <~> ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X2,X3) | ~r2_hidden(X3,k1_relset_1(X0,X0,X1)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)))),
% 0.21/0.45    inference(ennf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_partfun1(X1,X2) <=> ! [X3] : (r2_hidden(X3,k1_relset_1(X0,X0,X1)) => k1_funct_1(X1,X3) = k1_funct_1(X2,X3)))))),
% 0.21/0.45    inference(negated_conjecture,[],[f2])).
% 0.21/0.45  fof(f2,conjecture,(
% 0.21/0.45    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_partfun1(X1,X2) <=> ! [X3] : (r2_hidden(X3,k1_relset_1(X0,X0,X1)) => k1_funct_1(X1,X3) = k1_funct_1(X2,X3)))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_2)).
% 0.21/0.45  fof(f55,plain,(
% 0.21/0.45    ~spl5_6 | ~spl5_8),
% 0.21/0.45    inference(avatar_split_clause,[],[f9,f53,f46])).
% 0.21/0.45  fof(f9,plain,(
% 0.21/0.45    k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3) | ~r1_partfun1(sK1,sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f5])).
% 0.21/0.45  fof(f51,plain,(
% 0.21/0.45    ~spl5_6 | spl5_7),
% 0.21/0.45    inference(avatar_split_clause,[],[f8,f49,f46])).
% 0.21/0.45  fof(f8,plain,(
% 0.21/0.45    r2_hidden(sK3,k1_relset_1(sK0,sK0,sK1)) | ~r1_partfun1(sK1,sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f5])).
% 0.21/0.45  fof(f44,plain,(
% 0.21/0.45    spl5_5),
% 0.21/0.45    inference(avatar_split_clause,[],[f15,f42])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.45    inference(cnf_transformation,[],[f5])).
% 0.21/0.45  fof(f40,plain,(
% 0.21/0.45    spl5_4),
% 0.21/0.45    inference(avatar_split_clause,[],[f13,f38])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.45    inference(cnf_transformation,[],[f5])).
% 0.21/0.45  fof(f36,plain,(
% 0.21/0.45    spl5_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f12,f34])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    v1_funct_2(sK2,sK0,sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f5])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    spl5_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f14,f30])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    v1_funct_1(sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f5])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    spl5_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f11,f26])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    v1_funct_1(sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f5])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (24251)------------------------------
% 0.21/0.45  % (24251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (24251)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (24251)Memory used [KB]: 10746
% 0.21/0.45  % (24251)Time elapsed: 0.048 s
% 0.21/0.45  % (24251)------------------------------
% 0.21/0.45  % (24251)------------------------------
% 0.21/0.46  % (24241)Success in time 0.095 s
%------------------------------------------------------------------------------
