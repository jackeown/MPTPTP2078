%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  206 ( 387 expanded)
%              Number of leaves         :   47 ( 163 expanded)
%              Depth                    :   16
%              Number of atoms          :  759 (1421 expanded)
%              Number of equality atoms :  105 ( 204 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f647,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f82,f86,f90,f94,f101,f108,f112,f115,f119,f137,f158,f164,f168,f178,f182,f204,f208,f217,f225,f229,f233,f252,f259,f276,f300,f506,f527,f533,f575,f645,f646])).

fof(f646,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f645,plain,
    ( spl6_78
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_23
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f557,f227,f215,f166,f117,f110,f99,f92,f88,f84,f80,f76,f643])).

fof(f643,plain,
    ( spl6_78
  <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).

fof(f76,plain,
    ( spl6_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f80,plain,
    ( spl6_2
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f84,plain,
    ( spl6_3
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f88,plain,
    ( spl6_4
  <=> m1_subset_1(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f92,plain,
    ( spl6_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f99,plain,
    ( spl6_6
  <=> v1_funct_2(sK3,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f110,plain,
    ( spl6_9
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f117,plain,
    ( spl6_10
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f166,plain,
    ( spl6_14
  <=> r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f215,plain,
    ( spl6_23
  <=> k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f227,plain,
    ( spl6_26
  <=> k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f557,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_23
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f556,f111])).

fof(f111,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f110])).

fof(f556,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_23
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f555,f77])).

fof(f77,plain,
    ( v1_funct_1(sK4)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f555,plain,
    ( ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_23
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f554,f167])).

fof(f167,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f166])).

fof(f554,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_23
    | ~ spl6_26 ),
    inference(superposition,[],[f370,f216])).

fof(f216,plain,
    ( k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4)
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f215])).

fof(f370,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5)) )
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f369,f81])).

fof(f81,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f369,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | ~ v1_funct_1(sK3)
        | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5)) )
    | spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f368,f85])).

fof(f85,plain,
    ( ~ v1_xboole_0(sK2)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f84])).

fof(f368,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | v1_xboole_0(sK2)
        | ~ v1_funct_1(sK3)
        | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5)) )
    | ~ spl6_4
    | spl6_5
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f367,f118])).

fof(f118,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f117])).

fof(f367,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | v1_xboole_0(sK2)
        | ~ v1_funct_1(sK3)
        | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5)) )
    | ~ spl6_4
    | spl6_5
    | ~ spl6_6
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f363,f100])).

fof(f100,plain,
    ( v1_funct_2(sK3,sK1,sK2)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f99])).

fof(f363,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1))
        | ~ v1_funct_2(sK3,sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | v1_xboole_0(sK2)
        | ~ v1_funct_1(sK3)
        | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5)) )
    | ~ spl6_4
    | spl6_5
    | ~ spl6_26 ),
    inference(superposition,[],[f97,f228])).

fof(f228,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f227])).

fof(f97,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_tarski(k2_relset_1(sK1,X1,X0),k1_relset_1(X1,X3,X2))
        | ~ v1_funct_2(X0,sK1,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
        | v1_xboole_0(X1)
        | ~ v1_funct_1(X0)
        | k1_funct_1(k8_funct_2(sK1,X1,X3,X0,X2),sK5) = k1_funct_1(X2,k1_funct_1(X0,sK5)) )
    | ~ spl6_4
    | spl6_5 ),
    inference(subsumption_resolution,[],[f96,f93])).

fof(f93,plain,
    ( k1_xboole_0 != sK1
    | spl6_5 ),
    inference(avatar_component_clause,[],[f92])).

fof(f96,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,sK1,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
        | v1_xboole_0(X1)
        | ~ r1_tarski(k2_relset_1(sK1,X1,X0),k1_relset_1(X1,X3,X2))
        | k1_xboole_0 = sK1
        | k1_funct_1(k8_funct_2(sK1,X1,X3,X0,X2),sK5) = k1_funct_1(X2,k1_funct_1(X0,sK5)) )
    | ~ spl6_4 ),
    inference(resolution,[],[f89,f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
      | k1_xboole_0 = X1
      | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) ) ),
    inference(cnf_transformation,[],[f25])).

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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).

fof(f89,plain,
    ( m1_subset_1(sK5,sK1)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f88])).

fof(f575,plain,
    ( spl6_71
    | ~ spl6_1
    | ~ spl6_11
    | ~ spl6_15
    | ~ spl6_63 ),
    inference(avatar_split_clause,[],[f542,f531,f176,f135,f76,f573])).

fof(f573,plain,
    ( spl6_71
  <=> k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_71])])).

fof(f135,plain,
    ( spl6_11
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f176,plain,
    ( spl6_15
  <=> v5_relat_1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f531,plain,
    ( spl6_63
  <=> r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).

fof(f542,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ spl6_1
    | ~ spl6_11
    | ~ spl6_15
    | ~ spl6_63 ),
    inference(resolution,[],[f532,f189])).

fof(f189,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK4))
        | k1_funct_1(sK4,X0) = k7_partfun1(sK0,sK4,X0) )
    | ~ spl6_1
    | ~ spl6_11
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f188,f77])).

fof(f188,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK4)
        | ~ r2_hidden(X0,k1_relat_1(sK4))
        | k1_funct_1(sK4,X0) = k7_partfun1(sK0,sK4,X0) )
    | ~ spl6_11
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f187,f136])).

fof(f136,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f135])).

fof(f187,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK4)
        | ~ v1_funct_1(sK4)
        | ~ r2_hidden(X0,k1_relat_1(sK4))
        | k1_funct_1(sK4,X0) = k7_partfun1(sK0,sK4,X0) )
    | ~ spl6_15 ),
    inference(resolution,[],[f177,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

fof(f177,plain,
    ( v5_relat_1(sK4,sK0)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f176])).

fof(f532,plain,
    ( r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ spl6_63 ),
    inference(avatar_component_clause,[],[f531])).

fof(f533,plain,
    ( spl6_63
    | ~ spl6_7
    | ~ spl6_31
    | ~ spl6_60 ),
    inference(avatar_split_clause,[],[f529,f504,f261,f103,f531])).

fof(f103,plain,
    ( spl6_7
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f261,plain,
    ( spl6_31
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f504,plain,
    ( spl6_60
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK3))
        | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).

fof(f529,plain,
    ( r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ spl6_7
    | ~ spl6_31
    | ~ spl6_60 ),
    inference(resolution,[],[f528,f104])).

fof(f104,plain,
    ( r2_hidden(sK5,sK1)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f103])).

fof(f528,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) )
    | ~ spl6_31
    | ~ spl6_60 ),
    inference(forward_demodulation,[],[f505,f262])).

fof(f262,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f261])).

fof(f505,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK3))
        | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) )
    | ~ spl6_60 ),
    inference(avatar_component_clause,[],[f504])).

fof(f527,plain,
    ( spl6_28
    | ~ spl6_59 ),
    inference(avatar_contradiction_clause,[],[f526])).

fof(f526,plain,
    ( $false
    | spl6_28
    | ~ spl6_59 ),
    inference(subsumption_resolution,[],[f517,f60])).

fof(f60,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f517,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl6_28
    | ~ spl6_59 ),
    inference(superposition,[],[f251,f502])).

fof(f502,plain,
    ( k1_xboole_0 = k1_relat_1(sK4)
    | ~ spl6_59 ),
    inference(avatar_component_clause,[],[f501])).

fof(f501,plain,
    ( spl6_59
  <=> k1_xboole_0 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).

fof(f251,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK4))
    | spl6_28 ),
    inference(avatar_component_clause,[],[f250])).

fof(f250,plain,
    ( spl6_28
  <=> v1_xboole_0(k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f506,plain,
    ( spl6_59
    | spl6_60
    | ~ spl6_2
    | ~ spl6_21
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f246,f231,f206,f80,f504,f501])).

fof(f206,plain,
    ( spl6_21
  <=> v1_funct_2(sK3,k1_relat_1(sK3),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f231,plain,
    ( spl6_27
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_relat_1(sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f246,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK3))
        | k1_xboole_0 = k1_relat_1(sK4)
        | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) )
    | ~ spl6_2
    | ~ spl6_21
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f245,f81])).

fof(f245,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK3)
        | ~ r2_hidden(X0,k1_relat_1(sK3))
        | k1_xboole_0 = k1_relat_1(sK4)
        | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) )
    | ~ spl6_21
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f234,f207])).

fof(f207,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),k1_relat_1(sK4))
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f206])).

fof(f234,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK3,k1_relat_1(sK3),k1_relat_1(sK4))
        | ~ v1_funct_1(sK3)
        | ~ r2_hidden(X0,k1_relat_1(sK3))
        | k1_xboole_0 = k1_relat_1(sK4)
        | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) )
    | ~ spl6_27 ),
    inference(resolution,[],[f232,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | r2_hidden(k1_funct_1(X3,X2),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

fof(f232,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_relat_1(sK4))))
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f231])).

fof(f300,plain,
    ( spl6_3
    | ~ spl6_30 ),
    inference(avatar_contradiction_clause,[],[f299])).

fof(f299,plain,
    ( $false
    | spl6_3
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f289,f60])).

fof(f289,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl6_3
    | ~ spl6_30 ),
    inference(superposition,[],[f85,f258])).

fof(f258,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f257])).

fof(f257,plain,
    ( spl6_30
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f276,plain,
    ( spl6_31
    | ~ spl6_25
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f263,f254,f223,f261])).

fof(f223,plain,
    ( spl6_25
  <=> k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f254,plain,
    ( spl6_29
  <=> sK1 = k1_relset_1(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f263,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl6_25
    | ~ spl6_29 ),
    inference(superposition,[],[f255,f224])).

fof(f224,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3)
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f223])).

fof(f255,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f254])).

fof(f259,plain,
    ( spl6_29
    | spl6_30
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f151,f117,f99,f257,f254])).

fof(f151,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f140,f100])).

fof(f140,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ spl6_10 ),
    inference(resolution,[],[f118,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f252,plain,
    ( ~ spl6_28
    | spl6_20
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f248,f231,f202,f250])).

fof(f202,plain,
    ( spl6_20
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f248,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK4))
    | spl6_20
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f240,f203])).

fof(f203,plain,
    ( ~ v1_xboole_0(sK3)
    | spl6_20 ),
    inference(avatar_component_clause,[],[f202])).

fof(f240,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK4))
    | v1_xboole_0(sK3)
    | ~ spl6_27 ),
    inference(resolution,[],[f232,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f233,plain,
    ( spl6_27
    | ~ spl6_2
    | ~ spl6_13
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f174,f166,f162,f80,f231])).

fof(f162,plain,
    ( spl6_13
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f174,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_relat_1(sK4))))
    | ~ spl6_2
    | ~ spl6_13
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f173,f163])).

fof(f163,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f162])).

fof(f173,plain,
    ( ~ v1_relat_1(sK3)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_relat_1(sK4))))
    | ~ spl6_2
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f170,f81])).

fof(f170,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_relat_1(sK4))))
    | ~ spl6_14 ),
    inference(resolution,[],[f167,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f229,plain,
    ( spl6_26
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f142,f117,f227])).

fof(f142,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)
    | ~ spl6_10 ),
    inference(resolution,[],[f118,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f225,plain,
    ( spl6_25
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f141,f117,f223])).

fof(f141,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3)
    | ~ spl6_10 ),
    inference(resolution,[],[f118,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f217,plain,
    ( spl6_23
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f123,f110,f215])).

fof(f123,plain,
    ( k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4)
    | ~ spl6_9 ),
    inference(resolution,[],[f111,f63])).

fof(f208,plain,
    ( spl6_21
    | ~ spl6_2
    | ~ spl6_13
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f172,f166,f162,f80,f206])).

fof(f172,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),k1_relat_1(sK4))
    | ~ spl6_2
    | ~ spl6_13
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f171,f163])).

fof(f171,plain,
    ( ~ v1_relat_1(sK3)
    | v1_funct_2(sK3,k1_relat_1(sK3),k1_relat_1(sK4))
    | ~ spl6_2
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f169,f81])).

fof(f169,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | v1_funct_2(sK3,k1_relat_1(sK3),k1_relat_1(sK4))
    | ~ spl6_14 ),
    inference(resolution,[],[f167,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | v1_funct_2(X1,k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f204,plain,
    ( ~ spl6_20
    | spl6_8
    | ~ spl6_2
    | spl6_3
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f154,f117,f99,f84,f80,f106,f202])).

fof(f106,plain,
    ( spl6_8
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f154,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_xboole_0(sK3)
    | ~ spl6_2
    | spl6_3
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f153,f100])).

fof(f153,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_xboole_0(sK3)
    | ~ spl6_2
    | spl6_3
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f152,f81])).

fof(f152,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_xboole_0(sK3)
    | spl6_3
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f143,f85])).

fof(f143,plain,
    ( v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_xboole_0(sK3)
    | ~ spl6_10 ),
    inference(resolution,[],[f118,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_funct_2(X2,X0,X1)
            & ~ v1_xboole_0(X2)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_funct_2(X2,X0,X1)
            & ~ v1_xboole_0(X2)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_funct_2(X2,X0,X1)
              & ~ v1_xboole_0(X2)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_funct_2)).

fof(f182,plain,(
    ~ spl6_16 ),
    inference(avatar_split_clause,[],[f43,f180])).

fof(f180,plain,
    ( spl6_16
  <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f43,plain,(
    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_funct_2)).

fof(f178,plain,
    ( spl6_15
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f127,f110,f176])).

fof(f127,plain,
    ( v5_relat_1(sK4,sK0)
    | ~ spl6_9 ),
    inference(resolution,[],[f111,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f168,plain,
    ( spl6_14
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f160,f156,f117,f110,f166])).

fof(f156,plain,
    ( spl6_12
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f160,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(forward_demodulation,[],[f159,f142])).

fof(f159,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))
    | ~ spl6_9
    | ~ spl6_12 ),
    inference(forward_demodulation,[],[f157,f123])).

fof(f157,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f156])).

fof(f164,plain,
    ( spl6_13
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f146,f117,f162])).

fof(f146,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_10 ),
    inference(resolution,[],[f118,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f158,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f41,f156])).

fof(f41,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f19])).

fof(f137,plain,
    ( spl6_11
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f128,f110,f135])).

fof(f128,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_9 ),
    inference(resolution,[],[f111,f69])).

fof(f119,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f48,f117])).

fof(f48,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f19])).

fof(f115,plain,
    ( spl6_5
    | ~ spl6_8 ),
    inference(avatar_contradiction_clause,[],[f114])).

fof(f114,plain,
    ( $false
    | spl6_5
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f113,f93])).

fof(f113,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_8 ),
    inference(resolution,[],[f107,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f107,plain,
    ( v1_xboole_0(sK1)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f106])).

fof(f112,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f45,f110])).

fof(f45,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f108,plain,
    ( spl6_7
    | spl6_8
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f95,f88,f106,f103])).

fof(f95,plain,
    ( v1_xboole_0(sK1)
    | r2_hidden(sK5,sK1)
    | ~ spl6_4 ),
    inference(resolution,[],[f89,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
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

fof(f101,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f47,f99])).

fof(f47,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f94,plain,(
    ~ spl6_5 ),
    inference(avatar_split_clause,[],[f42,f92])).

fof(f42,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f19])).

fof(f90,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f40,f88])).

fof(f40,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f86,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f49,f84])).

fof(f49,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f82,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f46,f80])).

fof(f46,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f78,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f44,f76])).

fof(f44,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:12:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.43  % (17176)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.46  % (17192)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.46  % (17191)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.46  % (17182)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (17180)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (17176)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f647,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f78,f82,f86,f90,f94,f101,f108,f112,f115,f119,f137,f158,f164,f168,f178,f182,f204,f208,f217,f225,f229,f233,f252,f259,f276,f300,f506,f527,f533,f575,f645,f646])).
% 0.21/0.48  fof(f646,plain,(
% 0.21/0.48    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.48  fof(f645,plain,(
% 0.21/0.48    spl6_78 | ~spl6_1 | ~spl6_2 | spl6_3 | ~spl6_4 | spl6_5 | ~spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_14 | ~spl6_23 | ~spl6_26),
% 0.21/0.48    inference(avatar_split_clause,[],[f557,f227,f215,f166,f117,f110,f99,f92,f88,f84,f80,f76,f643])).
% 0.21/0.48  fof(f643,plain,(
% 0.21/0.48    spl6_78 <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    spl6_1 <=> v1_funct_1(sK4)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    spl6_2 <=> v1_funct_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    spl6_3 <=> v1_xboole_0(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    spl6_4 <=> m1_subset_1(sK5,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    spl6_5 <=> k1_xboole_0 = sK1),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    spl6_6 <=> v1_funct_2(sK3,sK1,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    spl6_9 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    spl6_10 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.48  fof(f166,plain,(
% 0.21/0.48    spl6_14 <=> r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.21/0.48  fof(f215,plain,(
% 0.21/0.48    spl6_23 <=> k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.21/0.48  fof(f227,plain,(
% 0.21/0.48    spl6_26 <=> k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.21/0.48  fof(f557,plain,(
% 0.21/0.48    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | (~spl6_1 | ~spl6_2 | spl6_3 | ~spl6_4 | spl6_5 | ~spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_14 | ~spl6_23 | ~spl6_26)),
% 0.21/0.48    inference(subsumption_resolution,[],[f556,f111])).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~spl6_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f110])).
% 0.21/0.48  fof(f556,plain,(
% 0.21/0.48    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | (~spl6_1 | ~spl6_2 | spl6_3 | ~spl6_4 | spl6_5 | ~spl6_6 | ~spl6_10 | ~spl6_14 | ~spl6_23 | ~spl6_26)),
% 0.21/0.48    inference(subsumption_resolution,[],[f555,f77])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    v1_funct_1(sK4) | ~spl6_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f76])).
% 0.21/0.48  fof(f555,plain,(
% 0.21/0.48    ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | (~spl6_2 | spl6_3 | ~spl6_4 | spl6_5 | ~spl6_6 | ~spl6_10 | ~spl6_14 | ~spl6_23 | ~spl6_26)),
% 0.21/0.48    inference(subsumption_resolution,[],[f554,f167])).
% 0.21/0.48  fof(f167,plain,(
% 0.21/0.48    r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) | ~spl6_14),
% 0.21/0.48    inference(avatar_component_clause,[],[f166])).
% 0.21/0.48  fof(f554,plain,(
% 0.21/0.48    ~r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | (~spl6_2 | spl6_3 | ~spl6_4 | spl6_5 | ~spl6_6 | ~spl6_10 | ~spl6_23 | ~spl6_26)),
% 0.21/0.48    inference(superposition,[],[f370,f216])).
% 0.21/0.48  fof(f216,plain,(
% 0.21/0.48    k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) | ~spl6_23),
% 0.21/0.48    inference(avatar_component_clause,[],[f215])).
% 0.21/0.48  fof(f370,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1)) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5))) ) | (~spl6_2 | spl6_3 | ~spl6_4 | spl6_5 | ~spl6_6 | ~spl6_10 | ~spl6_26)),
% 0.21/0.48    inference(subsumption_resolution,[],[f369,f81])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    v1_funct_1(sK3) | ~spl6_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f80])).
% 0.21/0.48  fof(f369,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1)) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(sK3) | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5))) ) | (spl6_3 | ~spl6_4 | spl6_5 | ~spl6_6 | ~spl6_10 | ~spl6_26)),
% 0.21/0.48    inference(subsumption_resolution,[],[f368,f85])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    ~v1_xboole_0(sK2) | spl6_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f84])).
% 0.21/0.48  fof(f368,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1)) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | v1_xboole_0(sK2) | ~v1_funct_1(sK3) | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5))) ) | (~spl6_4 | spl6_5 | ~spl6_6 | ~spl6_10 | ~spl6_26)),
% 0.21/0.48    inference(subsumption_resolution,[],[f367,f118])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl6_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f117])).
% 0.21/0.48  fof(f367,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | v1_xboole_0(sK2) | ~v1_funct_1(sK3) | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5))) ) | (~spl6_4 | spl6_5 | ~spl6_6 | ~spl6_26)),
% 0.21/0.48    inference(subsumption_resolution,[],[f363,f100])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    v1_funct_2(sK3,sK1,sK2) | ~spl6_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f99])).
% 0.21/0.48  fof(f363,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1)) | ~v1_funct_2(sK3,sK1,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | v1_xboole_0(sK2) | ~v1_funct_1(sK3) | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5))) ) | (~spl6_4 | spl6_5 | ~spl6_26)),
% 0.21/0.48    inference(superposition,[],[f97,f228])).
% 0.21/0.48  fof(f228,plain,(
% 0.21/0.48    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) | ~spl6_26),
% 0.21/0.48    inference(avatar_component_clause,[],[f227])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_relset_1(sK1,X1,X0),k1_relset_1(X1,X3,X2)) | ~v1_funct_2(X0,sK1,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | v1_xboole_0(X1) | ~v1_funct_1(X0) | k1_funct_1(k8_funct_2(sK1,X1,X3,X0,X2),sK5) = k1_funct_1(X2,k1_funct_1(X0,sK5))) ) | (~spl6_4 | spl6_5)),
% 0.21/0.48    inference(subsumption_resolution,[],[f96,f93])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    k1_xboole_0 != sK1 | spl6_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f92])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X0) | ~v1_funct_2(X0,sK1,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | v1_xboole_0(X1) | ~r1_tarski(k2_relset_1(sK1,X1,X0),k1_relset_1(X1,X3,X2)) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,X1,X3,X0,X2),sK5) = k1_funct_1(X2,k1_funct_1(X0,sK5))) ) | ~spl6_4),
% 0.21/0.48    inference(resolution,[],[f89,f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | k1_xboole_0 = X1 | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 0.21/0.48    inference(flattening,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    m1_subset_1(sK5,sK1) | ~spl6_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f88])).
% 0.21/0.48  fof(f575,plain,(
% 0.21/0.48    spl6_71 | ~spl6_1 | ~spl6_11 | ~spl6_15 | ~spl6_63),
% 0.21/0.48    inference(avatar_split_clause,[],[f542,f531,f176,f135,f76,f573])).
% 0.21/0.48  fof(f573,plain,(
% 0.21/0.48    spl6_71 <=> k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_71])])).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    spl6_11 <=> v1_relat_1(sK4)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.21/0.48  fof(f176,plain,(
% 0.21/0.48    spl6_15 <=> v5_relat_1(sK4,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.21/0.48  fof(f531,plain,(
% 0.21/0.48    spl6_63 <=> r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).
% 0.21/0.48  fof(f542,plain,(
% 0.21/0.48    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | (~spl6_1 | ~spl6_11 | ~spl6_15 | ~spl6_63)),
% 0.21/0.48    inference(resolution,[],[f532,f189])).
% 0.21/0.48  fof(f189,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK4)) | k1_funct_1(sK4,X0) = k7_partfun1(sK0,sK4,X0)) ) | (~spl6_1 | ~spl6_11 | ~spl6_15)),
% 0.21/0.48    inference(subsumption_resolution,[],[f188,f77])).
% 0.21/0.48  fof(f188,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_funct_1(sK4) | ~r2_hidden(X0,k1_relat_1(sK4)) | k1_funct_1(sK4,X0) = k7_partfun1(sK0,sK4,X0)) ) | (~spl6_11 | ~spl6_15)),
% 0.21/0.48    inference(subsumption_resolution,[],[f187,f136])).
% 0.21/0.48  fof(f136,plain,(
% 0.21/0.48    v1_relat_1(sK4) | ~spl6_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f135])).
% 0.21/0.48  fof(f187,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(sK4) | ~v1_funct_1(sK4) | ~r2_hidden(X0,k1_relat_1(sK4)) | k1_funct_1(sK4,X0) = k7_partfun1(sK0,sK4,X0)) ) | ~spl6_15),
% 0.21/0.48    inference(resolution,[],[f177,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v5_relat_1(X1,X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).
% 0.21/0.48  fof(f177,plain,(
% 0.21/0.48    v5_relat_1(sK4,sK0) | ~spl6_15),
% 0.21/0.48    inference(avatar_component_clause,[],[f176])).
% 0.21/0.48  fof(f532,plain,(
% 0.21/0.48    r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | ~spl6_63),
% 0.21/0.48    inference(avatar_component_clause,[],[f531])).
% 0.21/0.48  fof(f533,plain,(
% 0.21/0.48    spl6_63 | ~spl6_7 | ~spl6_31 | ~spl6_60),
% 0.21/0.48    inference(avatar_split_clause,[],[f529,f504,f261,f103,f531])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    spl6_7 <=> r2_hidden(sK5,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.48  fof(f261,plain,(
% 0.21/0.48    spl6_31 <=> sK1 = k1_relat_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 0.21/0.48  fof(f504,plain,(
% 0.21/0.48    spl6_60 <=> ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).
% 0.21/0.48  fof(f529,plain,(
% 0.21/0.48    r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | (~spl6_7 | ~spl6_31 | ~spl6_60)),
% 0.21/0.48    inference(resolution,[],[f528,f104])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    r2_hidden(sK5,sK1) | ~spl6_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f103])).
% 0.21/0.48  fof(f528,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4))) ) | (~spl6_31 | ~spl6_60)),
% 0.21/0.48    inference(forward_demodulation,[],[f505,f262])).
% 0.21/0.48  fof(f262,plain,(
% 0.21/0.48    sK1 = k1_relat_1(sK3) | ~spl6_31),
% 0.21/0.48    inference(avatar_component_clause,[],[f261])).
% 0.21/0.48  fof(f505,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4))) ) | ~spl6_60),
% 0.21/0.48    inference(avatar_component_clause,[],[f504])).
% 0.21/0.48  fof(f527,plain,(
% 0.21/0.48    spl6_28 | ~spl6_59),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f526])).
% 0.21/0.48  fof(f526,plain,(
% 0.21/0.48    $false | (spl6_28 | ~spl6_59)),
% 0.21/0.48    inference(subsumption_resolution,[],[f517,f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.48  fof(f517,plain,(
% 0.21/0.48    ~v1_xboole_0(k1_xboole_0) | (spl6_28 | ~spl6_59)),
% 0.21/0.48    inference(superposition,[],[f251,f502])).
% 0.21/0.48  fof(f502,plain,(
% 0.21/0.48    k1_xboole_0 = k1_relat_1(sK4) | ~spl6_59),
% 0.21/0.48    inference(avatar_component_clause,[],[f501])).
% 0.21/0.48  fof(f501,plain,(
% 0.21/0.48    spl6_59 <=> k1_xboole_0 = k1_relat_1(sK4)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).
% 0.21/0.48  fof(f251,plain,(
% 0.21/0.48    ~v1_xboole_0(k1_relat_1(sK4)) | spl6_28),
% 0.21/0.48    inference(avatar_component_clause,[],[f250])).
% 0.21/0.48  fof(f250,plain,(
% 0.21/0.48    spl6_28 <=> v1_xboole_0(k1_relat_1(sK4))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.21/0.48  fof(f506,plain,(
% 0.21/0.48    spl6_59 | spl6_60 | ~spl6_2 | ~spl6_21 | ~spl6_27),
% 0.21/0.48    inference(avatar_split_clause,[],[f246,f231,f206,f80,f504,f501])).
% 0.21/0.48  fof(f206,plain,(
% 0.21/0.48    spl6_21 <=> v1_funct_2(sK3,k1_relat_1(sK3),k1_relat_1(sK4))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.21/0.48  fof(f231,plain,(
% 0.21/0.48    spl6_27 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_relat_1(sK4))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.21/0.48  fof(f246,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | k1_xboole_0 = k1_relat_1(sK4) | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4))) ) | (~spl6_2 | ~spl6_21 | ~spl6_27)),
% 0.21/0.48    inference(subsumption_resolution,[],[f245,f81])).
% 0.21/0.48  fof(f245,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_funct_1(sK3) | ~r2_hidden(X0,k1_relat_1(sK3)) | k1_xboole_0 = k1_relat_1(sK4) | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4))) ) | (~spl6_21 | ~spl6_27)),
% 0.21/0.48    inference(subsumption_resolution,[],[f234,f207])).
% 0.21/0.48  fof(f207,plain,(
% 0.21/0.48    v1_funct_2(sK3,k1_relat_1(sK3),k1_relat_1(sK4)) | ~spl6_21),
% 0.21/0.48    inference(avatar_component_clause,[],[f206])).
% 0.21/0.48  fof(f234,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_funct_2(sK3,k1_relat_1(sK3),k1_relat_1(sK4)) | ~v1_funct_1(sK3) | ~r2_hidden(X0,k1_relat_1(sK3)) | k1_xboole_0 = k1_relat_1(sK4) | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4))) ) | ~spl6_27),
% 0.21/0.48    inference(resolution,[],[f232,f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | r2_hidden(k1_funct_1(X3,X2),X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.48    inference(flattening,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.48    inference(ennf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).
% 0.21/0.48  fof(f232,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_relat_1(sK4)))) | ~spl6_27),
% 0.21/0.48    inference(avatar_component_clause,[],[f231])).
% 0.21/0.48  fof(f300,plain,(
% 0.21/0.48    spl6_3 | ~spl6_30),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f299])).
% 0.21/0.48  fof(f299,plain,(
% 0.21/0.48    $false | (spl6_3 | ~spl6_30)),
% 0.21/0.48    inference(subsumption_resolution,[],[f289,f60])).
% 0.21/0.48  fof(f289,plain,(
% 0.21/0.48    ~v1_xboole_0(k1_xboole_0) | (spl6_3 | ~spl6_30)),
% 0.21/0.48    inference(superposition,[],[f85,f258])).
% 0.21/0.48  fof(f258,plain,(
% 0.21/0.48    k1_xboole_0 = sK2 | ~spl6_30),
% 0.21/0.48    inference(avatar_component_clause,[],[f257])).
% 0.21/0.48  fof(f257,plain,(
% 0.21/0.48    spl6_30 <=> k1_xboole_0 = sK2),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.21/0.48  fof(f276,plain,(
% 0.21/0.48    spl6_31 | ~spl6_25 | ~spl6_29),
% 0.21/0.48    inference(avatar_split_clause,[],[f263,f254,f223,f261])).
% 0.21/0.48  fof(f223,plain,(
% 0.21/0.48    spl6_25 <=> k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.21/0.48  fof(f254,plain,(
% 0.21/0.48    spl6_29 <=> sK1 = k1_relset_1(sK1,sK2,sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.21/0.48  fof(f263,plain,(
% 0.21/0.48    sK1 = k1_relat_1(sK3) | (~spl6_25 | ~spl6_29)),
% 0.21/0.48    inference(superposition,[],[f255,f224])).
% 0.21/0.48  fof(f224,plain,(
% 0.21/0.48    k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) | ~spl6_25),
% 0.21/0.48    inference(avatar_component_clause,[],[f223])).
% 0.21/0.48  fof(f255,plain,(
% 0.21/0.48    sK1 = k1_relset_1(sK1,sK2,sK3) | ~spl6_29),
% 0.21/0.48    inference(avatar_component_clause,[],[f254])).
% 0.21/0.48  fof(f259,plain,(
% 0.21/0.48    spl6_29 | spl6_30 | ~spl6_6 | ~spl6_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f151,f117,f99,f257,f254])).
% 0.21/0.48  fof(f151,plain,(
% 0.21/0.48    k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3) | (~spl6_6 | ~spl6_10)),
% 0.21/0.48    inference(subsumption_resolution,[],[f140,f100])).
% 0.21/0.48  fof(f140,plain,(
% 0.21/0.48    k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3) | ~v1_funct_2(sK3,sK1,sK2) | ~spl6_10),
% 0.21/0.48    inference(resolution,[],[f118,f58])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(flattening,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.48  fof(f252,plain,(
% 0.21/0.48    ~spl6_28 | spl6_20 | ~spl6_27),
% 0.21/0.48    inference(avatar_split_clause,[],[f248,f231,f202,f250])).
% 0.21/0.48  fof(f202,plain,(
% 0.21/0.48    spl6_20 <=> v1_xboole_0(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.21/0.48  fof(f248,plain,(
% 0.21/0.48    ~v1_xboole_0(k1_relat_1(sK4)) | (spl6_20 | ~spl6_27)),
% 0.21/0.48    inference(subsumption_resolution,[],[f240,f203])).
% 0.21/0.48  fof(f203,plain,(
% 0.21/0.48    ~v1_xboole_0(sK3) | spl6_20),
% 0.21/0.48    inference(avatar_component_clause,[],[f202])).
% 0.21/0.48  fof(f240,plain,(
% 0.21/0.48    ~v1_xboole_0(k1_relat_1(sK4)) | v1_xboole_0(sK3) | ~spl6_27),
% 0.21/0.48    inference(resolution,[],[f232,f66])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0) | v1_xboole_0(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).
% 0.21/0.48  fof(f233,plain,(
% 0.21/0.48    spl6_27 | ~spl6_2 | ~spl6_13 | ~spl6_14),
% 0.21/0.48    inference(avatar_split_clause,[],[f174,f166,f162,f80,f231])).
% 0.21/0.48  fof(f162,plain,(
% 0.21/0.48    spl6_13 <=> v1_relat_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.21/0.48  fof(f174,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_relat_1(sK4)))) | (~spl6_2 | ~spl6_13 | ~spl6_14)),
% 0.21/0.48    inference(subsumption_resolution,[],[f173,f163])).
% 0.21/0.48  fof(f163,plain,(
% 0.21/0.48    v1_relat_1(sK3) | ~spl6_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f162])).
% 0.21/0.48  fof(f173,plain,(
% 0.21/0.48    ~v1_relat_1(sK3) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_relat_1(sK4)))) | (~spl6_2 | ~spl6_14)),
% 0.21/0.48    inference(subsumption_resolution,[],[f170,f81])).
% 0.21/0.48  fof(f170,plain,(
% 0.21/0.48    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_relat_1(sK4)))) | ~spl6_14),
% 0.21/0.48    inference(resolution,[],[f167,f62])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 0.21/0.48  fof(f229,plain,(
% 0.21/0.48    spl6_26 | ~spl6_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f142,f117,f227])).
% 0.21/0.48  fof(f142,plain,(
% 0.21/0.48    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) | ~spl6_10),
% 0.21/0.48    inference(resolution,[],[f118,f64])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.48  fof(f225,plain,(
% 0.21/0.48    spl6_25 | ~spl6_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f141,f117,f223])).
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) | ~spl6_10),
% 0.21/0.48    inference(resolution,[],[f118,f63])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.48  fof(f217,plain,(
% 0.21/0.48    spl6_23 | ~spl6_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f123,f110,f215])).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) | ~spl6_9),
% 0.21/0.48    inference(resolution,[],[f111,f63])).
% 0.21/0.48  fof(f208,plain,(
% 0.21/0.48    spl6_21 | ~spl6_2 | ~spl6_13 | ~spl6_14),
% 0.21/0.48    inference(avatar_split_clause,[],[f172,f166,f162,f80,f206])).
% 0.21/0.48  fof(f172,plain,(
% 0.21/0.48    v1_funct_2(sK3,k1_relat_1(sK3),k1_relat_1(sK4)) | (~spl6_2 | ~spl6_13 | ~spl6_14)),
% 0.21/0.48    inference(subsumption_resolution,[],[f171,f163])).
% 0.21/0.48  fof(f171,plain,(
% 0.21/0.48    ~v1_relat_1(sK3) | v1_funct_2(sK3,k1_relat_1(sK3),k1_relat_1(sK4)) | (~spl6_2 | ~spl6_14)),
% 0.21/0.48    inference(subsumption_resolution,[],[f169,f81])).
% 0.21/0.48  fof(f169,plain,(
% 0.21/0.48    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | v1_funct_2(sK3,k1_relat_1(sK3),k1_relat_1(sK4)) | ~spl6_14),
% 0.21/0.48    inference(resolution,[],[f167,f61])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | v1_funct_2(X1,k1_relat_1(X1),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f204,plain,(
% 0.21/0.48    ~spl6_20 | spl6_8 | ~spl6_2 | spl6_3 | ~spl6_6 | ~spl6_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f154,f117,f99,f84,f80,f106,f202])).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    spl6_8 <=> v1_xboole_0(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.48  fof(f154,plain,(
% 0.21/0.48    v1_xboole_0(sK1) | ~v1_xboole_0(sK3) | (~spl6_2 | spl6_3 | ~spl6_6 | ~spl6_10)),
% 0.21/0.48    inference(subsumption_resolution,[],[f153,f100])).
% 0.21/0.48  fof(f153,plain,(
% 0.21/0.48    v1_xboole_0(sK1) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_xboole_0(sK3) | (~spl6_2 | spl6_3 | ~spl6_10)),
% 0.21/0.48    inference(subsumption_resolution,[],[f152,f81])).
% 0.21/0.48  fof(f152,plain,(
% 0.21/0.48    v1_xboole_0(sK1) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_xboole_0(sK3) | (spl6_3 | ~spl6_10)),
% 0.21/0.48    inference(subsumption_resolution,[],[f143,f85])).
% 0.21/0.48  fof(f143,plain,(
% 0.21/0.48    v1_xboole_0(sK2) | v1_xboole_0(sK1) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_xboole_0(sK3) | ~spl6_10),
% 0.21/0.48    inference(resolution,[],[f118,f65])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~v1_xboole_0(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : ((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.21/0.48    inference(flattening,[],[f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_funct_2)).
% 0.21/0.48  fof(f182,plain,(
% 0.21/0.48    ~spl6_16),
% 0.21/0.48    inference(avatar_split_clause,[],[f43,f180])).
% 0.21/0.48  fof(f180,plain,(
% 0.21/0.48    spl6_16 <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 0.21/0.48    inference(flattening,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 0.21/0.48    inference(ennf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.21/0.48    inference(negated_conjecture,[],[f15])).
% 0.21/0.48  fof(f15,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_funct_2)).
% 0.21/0.48  fof(f178,plain,(
% 0.21/0.48    spl6_15 | ~spl6_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f127,f110,f176])).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    v5_relat_1(sK4,sK0) | ~spl6_9),
% 0.21/0.48    inference(resolution,[],[f111,f68])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.21/0.48    inference(pure_predicate_removal,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.48  fof(f168,plain,(
% 0.21/0.48    spl6_14 | ~spl6_9 | ~spl6_10 | ~spl6_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f160,f156,f117,f110,f166])).
% 0.21/0.48  fof(f156,plain,(
% 0.21/0.48    spl6_12 <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.21/0.48  fof(f160,plain,(
% 0.21/0.48    r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) | (~spl6_9 | ~spl6_10 | ~spl6_12)),
% 0.21/0.48    inference(forward_demodulation,[],[f159,f142])).
% 0.21/0.48  fof(f159,plain,(
% 0.21/0.48    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) | (~spl6_9 | ~spl6_12)),
% 0.21/0.48    inference(forward_demodulation,[],[f157,f123])).
% 0.21/0.48  fof(f157,plain,(
% 0.21/0.48    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) | ~spl6_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f156])).
% 0.21/0.48  fof(f164,plain,(
% 0.21/0.48    spl6_13 | ~spl6_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f146,f117,f162])).
% 0.21/0.48  fof(f146,plain,(
% 0.21/0.48    v1_relat_1(sK3) | ~spl6_10),
% 0.21/0.48    inference(resolution,[],[f118,f69])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.48  fof(f158,plain,(
% 0.21/0.48    spl6_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f41,f156])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f137,plain,(
% 0.21/0.48    spl6_11 | ~spl6_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f128,f110,f135])).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    v1_relat_1(sK4) | ~spl6_9),
% 0.21/0.48    inference(resolution,[],[f111,f69])).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    spl6_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f48,f117])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    spl6_5 | ~spl6_8),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f114])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    $false | (spl6_5 | ~spl6_8)),
% 0.21/0.48    inference(subsumption_resolution,[],[f113,f93])).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | ~spl6_8),
% 0.21/0.48    inference(resolution,[],[f107,f59])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    v1_xboole_0(sK1) | ~spl6_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f106])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    spl6_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f45,f110])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    spl6_7 | spl6_8 | ~spl6_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f95,f88,f106,f103])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    v1_xboole_0(sK1) | r2_hidden(sK5,sK1) | ~spl6_4),
% 0.21/0.48    inference(resolution,[],[f89,f67])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    spl6_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f47,f99])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    v1_funct_2(sK3,sK1,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    ~spl6_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f42,f92])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    k1_xboole_0 != sK1),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    spl6_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f40,f88])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    m1_subset_1(sK5,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    ~spl6_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f49,f84])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ~v1_xboole_0(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    spl6_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f46,f80])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    v1_funct_1(sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    spl6_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f44,f76])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    v1_funct_1(sK4)),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (17176)------------------------------
% 0.21/0.48  % (17176)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (17176)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (17176)Memory used [KB]: 6652
% 0.21/0.48  % (17176)Time elapsed: 0.092 s
% 0.21/0.48  % (17176)------------------------------
% 0.21/0.48  % (17176)------------------------------
% 0.21/0.48  % (17174)Success in time 0.124 s
%------------------------------------------------------------------------------
