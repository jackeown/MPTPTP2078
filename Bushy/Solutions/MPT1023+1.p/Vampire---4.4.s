%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t113_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:29 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  280 ( 845 expanded)
%              Number of leaves         :   76 ( 322 expanded)
%              Depth                    :   14
%              Number of atoms          :  916 (2641 expanded)
%              Number of equality atoms :   44 ( 137 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f631,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f85,f92,f99,f106,f113,f120,f128,f144,f151,f162,f163,f184,f191,f203,f216,f229,f236,f243,f253,f260,f271,f282,f307,f327,f328,f347,f360,f376,f411,f431,f444,f451,f458,f466,f483,f505,f525,f546,f557,f564,f573,f587,f598,f605,f614,f630])).

fof(f630,plain,
    ( ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | spl8_59
    | ~ spl8_110 ),
    inference(avatar_contradiction_clause,[],[f629])).

fof(f629,plain,
    ( $false
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_59
    | ~ spl8_110 ),
    inference(subsumption_resolution,[],[f628,f340])).

fof(f340,plain,
    ( ~ r2_relset_1(sK0,sK1,sK3,sK2)
    | ~ spl8_59 ),
    inference(avatar_component_clause,[],[f339])).

fof(f339,plain,
    ( spl8_59
  <=> ~ r2_relset_1(sK0,sK1,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_59])])).

fof(f628,plain,
    ( r2_relset_1(sK0,sK1,sK3,sK2)
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_110 ),
    inference(subsumption_resolution,[],[f627,f77])).

fof(f77,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_0 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl8_0
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_0])])).

fof(f627,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r2_relset_1(sK0,sK1,sK3,sK2)
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_110 ),
    inference(subsumption_resolution,[],[f626,f84])).

fof(f84,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl8_2
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f626,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r2_relset_1(sK0,sK1,sK3,sK2)
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_110 ),
    inference(subsumption_resolution,[],[f625,f112])).

fof(f112,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl8_10
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f625,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r2_relset_1(sK0,sK1,sK3,sK2)
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_12
    | ~ spl8_110 ),
    inference(resolution,[],[f622,f105])).

fof(f105,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl8_8
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f622,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_funct_2(sK3,sK0,X0)
        | ~ v1_funct_2(sK2,sK0,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | r2_relset_1(sK0,X0,sK3,sK2) )
    | ~ spl8_4
    | ~ spl8_12
    | ~ spl8_110 ),
    inference(subsumption_resolution,[],[f621,f119])).

fof(f119,plain,
    ( v1_funct_1(sK3)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl8_12
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f621,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK3,sK0,X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_funct_2(sK2,sK0,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_funct_1(sK3)
        | r2_relset_1(sK0,X0,sK3,sK2) )
    | ~ spl8_4
    | ~ spl8_110 ),
    inference(subsumption_resolution,[],[f620,f91])).

fof(f91,plain,
    ( v1_funct_1(sK2)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl8_4
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f620,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK3,sK0,X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,sK0,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_funct_1(sK3)
        | r2_relset_1(sK0,X0,sK3,sK2) )
    | ~ spl8_110 ),
    inference(trivial_inequality_removal,[],[f615])).

fof(f615,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,sK4(sK0,sK3,sK2)) != k1_funct_1(sK2,sK4(sK0,sK3,sK2))
        | ~ v1_funct_2(sK3,sK0,X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,sK0,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_funct_1(sK3)
        | r2_relset_1(sK0,X0,sK3,sK2) )
    | ~ spl8_110 ),
    inference(superposition,[],[f58,f572])).

fof(f572,plain,
    ( k1_funct_1(sK2,sK4(sK0,sK3,sK2)) = k1_funct_1(sK3,sK4(sK0,sK3,sK2))
    | ~ spl8_110 ),
    inference(avatar_component_clause,[],[f571])).

fof(f571,plain,
    ( spl8_110
  <=> k1_funct_1(sK2,sK4(sK0,sK3,sK2)) = k1_funct_1(sK3,sK4(sK0,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_110])])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,sK4(X0,X2,X3)) != k1_funct_1(X3,sK4(X0,X2,X3))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ? [X4] :
              ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
              & r2_hidden(X4,X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ? [X4] :
              ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
              & r2_hidden(X4,X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( r2_hidden(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t113_funct_2.p',t18_funct_2)).

fof(f614,plain,
    ( spl8_118
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f606,f603,f612])).

fof(f612,plain,
    ( spl8_118
  <=> k1_funct_1(sK2,sK4(sK0,sK2,sK3)) = k1_funct_1(sK3,sK4(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_118])])).

fof(f603,plain,
    ( spl8_116
  <=> m1_subset_1(sK4(sK0,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_116])])).

fof(f606,plain,
    ( k1_funct_1(sK2,sK4(sK0,sK2,sK3)) = k1_funct_1(sK3,sK4(sK0,sK2,sK3))
    | ~ spl8_116 ),
    inference(resolution,[],[f604,f44])).

fof(f44,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK0)
      | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ! [X4] :
                  ( m1_subset_1(X4,X0)
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( m1_subset_1(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t113_funct_2.p',t113_funct_2)).

fof(f604,plain,
    ( m1_subset_1(sK4(sK0,sK2,sK3),sK0)
    | ~ spl8_116 ),
    inference(avatar_component_clause,[],[f603])).

fof(f605,plain,
    ( spl8_116
    | ~ spl8_112 ),
    inference(avatar_split_clause,[],[f589,f585,f603])).

fof(f585,plain,
    ( spl8_112
  <=> r2_hidden(sK4(sK0,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_112])])).

fof(f589,plain,
    ( m1_subset_1(sK4(sK0,sK2,sK3),sK0)
    | ~ spl8_112 ),
    inference(resolution,[],[f586,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t113_funct_2.p',t1_subset)).

fof(f586,plain,
    ( r2_hidden(sK4(sK0,sK2,sK3),sK0)
    | ~ spl8_112 ),
    inference(avatar_component_clause,[],[f585])).

fof(f598,plain,
    ( ~ spl8_115
    | ~ spl8_112 ),
    inference(avatar_split_clause,[],[f588,f585,f596])).

fof(f596,plain,
    ( spl8_115
  <=> ~ r2_hidden(sK0,sK4(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_115])])).

fof(f588,plain,
    ( ~ r2_hidden(sK0,sK4(sK0,sK2,sK3))
    | ~ spl8_112 ),
    inference(resolution,[],[f586,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t113_funct_2.p',antisymmetry_r2_hidden)).

fof(f587,plain,
    ( spl8_112
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | spl8_7
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f580,f118,f111,f104,f97,f90,f83,f76,f585])).

fof(f97,plain,
    ( spl8_7
  <=> ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f580,plain,
    ( r2_hidden(sK4(sK0,sK2,sK3),sK0)
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f579,f98])).

fof(f98,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f97])).

fof(f579,plain,
    ( r2_hidden(sK4(sK0,sK2,sK3),sK0)
    | r2_relset_1(sK0,sK1,sK2,sK3)
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f578,f91])).

fof(f578,plain,
    ( ~ v1_funct_1(sK2)
    | r2_hidden(sK4(sK0,sK2,sK3),sK0)
    | r2_relset_1(sK0,sK1,sK2,sK3)
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f574,f84])).

fof(f574,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | r2_hidden(sK4(sK0,sK2,sK3),sK0)
    | r2_relset_1(sK0,sK1,sK2,sK3)
    | ~ spl8_0
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12 ),
    inference(resolution,[],[f491,f77])).

fof(f491,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(X1,sK0,sK1)
        | ~ v1_funct_1(X1)
        | r2_hidden(sK4(sK0,X1,sK3),sK0)
        | r2_relset_1(sK0,sK1,X1,sK3) )
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f490,f112])).

fof(f490,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(X1,sK0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(sK3,sK0,sK1)
        | ~ v1_funct_1(X1)
        | r2_hidden(sK4(sK0,X1,sK3),sK0)
        | r2_relset_1(sK0,sK1,X1,sK3) )
    | ~ spl8_8
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f485,f119])).

fof(f485,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(X1,sK0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,sK0,sK1)
        | ~ v1_funct_1(X1)
        | r2_hidden(sK4(sK0,X1,sK3),sK0)
        | r2_relset_1(sK0,sK1,X1,sK3) )
    | ~ spl8_8 ),
    inference(resolution,[],[f57,f105])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X2)
      | r2_hidden(sK4(X0,X2,X3),X0)
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f573,plain,
    ( spl8_110
    | ~ spl8_108 ),
    inference(avatar_split_clause,[],[f565,f562,f571])).

fof(f562,plain,
    ( spl8_108
  <=> m1_subset_1(sK4(sK0,sK3,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_108])])).

fof(f565,plain,
    ( k1_funct_1(sK2,sK4(sK0,sK3,sK2)) = k1_funct_1(sK3,sK4(sK0,sK3,sK2))
    | ~ spl8_108 ),
    inference(resolution,[],[f563,f44])).

fof(f563,plain,
    ( m1_subset_1(sK4(sK0,sK3,sK2),sK0)
    | ~ spl8_108 ),
    inference(avatar_component_clause,[],[f562])).

fof(f564,plain,
    ( spl8_108
    | ~ spl8_92 ),
    inference(avatar_split_clause,[],[f548,f503,f562])).

fof(f503,plain,
    ( spl8_92
  <=> r2_hidden(sK4(sK0,sK3,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_92])])).

fof(f548,plain,
    ( m1_subset_1(sK4(sK0,sK3,sK2),sK0)
    | ~ spl8_92 ),
    inference(resolution,[],[f504,f64])).

fof(f504,plain,
    ( r2_hidden(sK4(sK0,sK3,sK2),sK0)
    | ~ spl8_92 ),
    inference(avatar_component_clause,[],[f503])).

fof(f557,plain,
    ( ~ spl8_107
    | ~ spl8_92 ),
    inference(avatar_split_clause,[],[f547,f503,f555])).

fof(f555,plain,
    ( spl8_107
  <=> ~ r2_hidden(sK0,sK4(sK0,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_107])])).

fof(f547,plain,
    ( ~ r2_hidden(sK0,sK4(sK0,sK3,sK2))
    | ~ spl8_92 ),
    inference(resolution,[],[f504,f65])).

fof(f546,plain,
    ( spl8_100
    | ~ spl8_103
    | ~ spl8_105
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | spl8_79
    | spl8_83 ),
    inference(avatar_split_clause,[],[f527,f442,f426,f90,f83,f76,f544,f538,f532])).

fof(f532,plain,
    ( spl8_100
  <=> r2_hidden(sK4(sK0,sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_100])])).

fof(f538,plain,
    ( spl8_103
  <=> ~ v1_funct_1(sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_103])])).

fof(f544,plain,
    ( spl8_105
  <=> ~ v1_funct_2(sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_105])])).

fof(f426,plain,
    ( spl8_79
  <=> ~ v1_xboole_0(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_79])])).

fof(f442,plain,
    ( spl8_83
  <=> ~ r2_relset_1(sK0,sK1,sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_83])])).

fof(f527,plain,
    ( ~ v1_funct_2(sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),sK0,sK1)
    | ~ v1_funct_1(sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))))
    | r2_hidden(sK4(sK0,sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),sK2),sK0)
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_79
    | ~ spl8_83 ),
    inference(subsumption_resolution,[],[f526,f427])).

fof(f427,plain,
    ( ~ v1_xboole_0(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))))
    | ~ spl8_79 ),
    inference(avatar_component_clause,[],[f426])).

fof(f526,plain,
    ( ~ v1_funct_2(sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),sK0,sK1)
    | ~ v1_funct_1(sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))))
    | r2_hidden(sK4(sK0,sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),sK2),sK0)
    | v1_xboole_0(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))))
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_83 ),
    inference(subsumption_resolution,[],[f495,f443])).

fof(f443,plain,
    ( ~ r2_relset_1(sK0,sK1,sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),sK2)
    | ~ spl8_83 ),
    inference(avatar_component_clause,[],[f442])).

fof(f495,plain,
    ( ~ v1_funct_2(sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),sK0,sK1)
    | ~ v1_funct_1(sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))))
    | r2_hidden(sK4(sK0,sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),sK2),sK0)
    | r2_relset_1(sK0,sK1,sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),sK2)
    | v1_xboole_0(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))))
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(resolution,[],[f489,f377])).

fof(f377,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(sK5(k1_zfmisc_1(X0))),X0)
      | v1_xboole_0(sK5(k1_zfmisc_1(X0))) ) ),
    inference(resolution,[],[f286,f131])).

fof(f131,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f62,f59])).

fof(f59,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t113_funct_2.p',existence_m1_subset_1)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t113_funct_2.p',t2_subset)).

fof(f286,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,sK5(k1_zfmisc_1(X3)))
      | m1_subset_1(X2,X3) ) ),
    inference(resolution,[],[f63,f59])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t113_funct_2.p',t4_subset)).

fof(f489,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(X0,sK0,sK1)
        | ~ v1_funct_1(X0)
        | r2_hidden(sK4(sK0,X0,sK2),sK0)
        | r2_relset_1(sK0,sK1,X0,sK2) )
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f488,f84])).

fof(f488,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,sK0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(X0)
        | r2_hidden(sK4(sK0,X0,sK2),sK0)
        | r2_relset_1(sK0,sK1,X0,sK2) )
    | ~ spl8_0
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f484,f91])).

fof(f484,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,sK0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(X0)
        | r2_hidden(sK4(sK0,X0,sK2),sK0)
        | r2_relset_1(sK0,sK1,X0,sK2) )
    | ~ spl8_0 ),
    inference(resolution,[],[f57,f77])).

fof(f525,plain,
    ( spl8_94
    | ~ spl8_97
    | ~ spl8_99
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | spl8_63 ),
    inference(avatar_split_clause,[],[f506,f352,f90,f83,f76,f523,f517,f511])).

fof(f511,plain,
    ( spl8_94
  <=> r2_hidden(sK4(sK0,sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))),sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_94])])).

fof(f517,plain,
    ( spl8_97
  <=> ~ v1_funct_1(sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_97])])).

fof(f523,plain,
    ( spl8_99
  <=> ~ v1_funct_2(sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_99])])).

fof(f352,plain,
    ( spl8_63
  <=> ~ r2_relset_1(sK0,sK1,sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_63])])).

fof(f506,plain,
    ( ~ v1_funct_2(sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))),sK0,sK1)
    | ~ v1_funct_1(sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))
    | r2_hidden(sK4(sK0,sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))),sK2),sK0)
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_63 ),
    inference(subsumption_resolution,[],[f494,f353])).

fof(f353,plain,
    ( ~ r2_relset_1(sK0,sK1,sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))),sK2)
    | ~ spl8_63 ),
    inference(avatar_component_clause,[],[f352])).

fof(f494,plain,
    ( ~ v1_funct_2(sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))),sK0,sK1)
    | ~ v1_funct_1(sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))
    | r2_hidden(sK4(sK0,sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))),sK2),sK0)
    | r2_relset_1(sK0,sK1,sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))),sK2)
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(resolution,[],[f489,f59])).

fof(f505,plain,
    ( spl8_92
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | spl8_59 ),
    inference(avatar_split_clause,[],[f498,f339,f118,f111,f104,f90,f83,f76,f503])).

fof(f498,plain,
    ( r2_hidden(sK4(sK0,sK3,sK2),sK0)
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_59 ),
    inference(subsumption_resolution,[],[f497,f340])).

fof(f497,plain,
    ( r2_hidden(sK4(sK0,sK3,sK2),sK0)
    | r2_relset_1(sK0,sK1,sK3,sK2)
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f496,f119])).

fof(f496,plain,
    ( ~ v1_funct_1(sK3)
    | r2_hidden(sK4(sK0,sK3,sK2),sK0)
    | r2_relset_1(sK0,sK1,sK3,sK2)
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f493,f112])).

fof(f493,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | ~ v1_funct_1(sK3)
    | r2_hidden(sK4(sK0,sK3,sK2),sK0)
    | r2_relset_1(sK0,sK1,sK3,sK2)
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(resolution,[],[f489,f105])).

fof(f483,plain,
    ( ~ spl8_91
    | spl8_73 ),
    inference(avatar_split_clause,[],[f473,f406,f481])).

fof(f481,plain,
    ( spl8_91
  <=> ~ sP7(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_91])])).

fof(f406,plain,
    ( spl8_73
  <=> ~ v1_xboole_0(sK5(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_73])])).

fof(f473,plain,
    ( ~ sP7(sK0)
    | ~ spl8_73 ),
    inference(resolution,[],[f470,f407])).

fof(f407,plain,
    ( ~ v1_xboole_0(sK5(k1_zfmisc_1(sK0)))
    | ~ spl8_73 ),
    inference(avatar_component_clause,[],[f406])).

fof(f470,plain,(
    ! [X2] :
      ( v1_xboole_0(sK5(k1_zfmisc_1(X2)))
      | ~ sP7(X2) ) ),
    inference(resolution,[],[f412,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP7(X1) ) ),
    inference(general_splitting,[],[f60,f69_D])).

fof(f69,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | sP7(X1) ) ),
    inference(cnf_transformation,[],[f69_D])).

fof(f69_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP7(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t113_funct_2.p',t5_subset)).

fof(f412,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK5(k1_zfmisc_1(X0))),X0)
      | v1_xboole_0(sK5(k1_zfmisc_1(X0))) ) ),
    inference(subsumption_resolution,[],[f388,f192])).

fof(f192,plain,(
    ! [X0] :
      ( v1_xboole_0(sK5(k1_zfmisc_1(X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f171,f167])).

fof(f167,plain,(
    ! [X2] :
      ( ~ sP7(X2)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f131,f70])).

fof(f171,plain,(
    ! [X0] :
      ( sP7(sK5(k1_zfmisc_1(X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f69,f59])).

fof(f388,plain,(
    ! [X0] :
      ( v1_xboole_0(sK5(k1_zfmisc_1(X0)))
      | v1_xboole_0(X0)
      | r2_hidden(sK5(sK5(k1_zfmisc_1(X0))),X0) ) ),
    inference(resolution,[],[f377,f62])).

fof(f466,plain,
    ( ~ spl8_89
    | spl8_73 ),
    inference(avatar_split_clause,[],[f459,f406,f464])).

fof(f464,plain,
    ( spl8_89
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_89])])).

fof(f459,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl8_73 ),
    inference(resolution,[],[f407,f192])).

fof(f458,plain,
    ( ~ spl8_83
    | spl8_86
    | spl8_78
    | ~ spl8_0 ),
    inference(avatar_split_clause,[],[f396,f76,f429,f456,f442])).

fof(f456,plain,
    ( spl8_86
  <=> sK2 = sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_86])])).

fof(f429,plain,
    ( spl8_78
  <=> v1_xboole_0(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_78])])).

fof(f396,plain,
    ( v1_xboole_0(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))))
    | sK2 = sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))))
    | ~ r2_relset_1(sK0,sK1,sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),sK2)
    | ~ spl8_0 ),
    inference(resolution,[],[f377,f291])).

fof(f291,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | sK2 = X0
        | ~ r2_relset_1(sK0,sK1,X0,sK2) )
    | ~ spl8_0 ),
    inference(resolution,[],[f53,f77])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t113_funct_2.p',redefinition_r2_relset_1)).

fof(f451,plain,
    ( ~ spl8_77
    | spl8_84
    | spl8_78
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f395,f104,f429,f449,f423])).

fof(f423,plain,
    ( spl8_77
  <=> ~ r2_relset_1(sK0,sK1,sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_77])])).

fof(f449,plain,
    ( spl8_84
  <=> sK3 = sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_84])])).

fof(f395,plain,
    ( v1_xboole_0(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))))
    | sK3 = sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))))
    | ~ r2_relset_1(sK0,sK1,sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),sK3)
    | ~ spl8_8 ),
    inference(resolution,[],[f377,f292])).

fof(f292,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | sK3 = X1
        | ~ r2_relset_1(sK0,sK1,X1,sK3) )
    | ~ spl8_8 ),
    inference(resolution,[],[f53,f105])).

fof(f444,plain,
    ( spl8_80
    | ~ spl8_83
    | spl8_78
    | ~ spl8_0 ),
    inference(avatar_split_clause,[],[f394,f76,f429,f442,f436])).

fof(f436,plain,
    ( spl8_80
  <=> r2_relset_1(sK0,sK1,sK2,sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_80])])).

fof(f394,plain,
    ( v1_xboole_0(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))))
    | ~ r2_relset_1(sK0,sK1,sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),sK2)
    | r2_relset_1(sK0,sK1,sK2,sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))))
    | ~ spl8_0 ),
    inference(resolution,[],[f377,f378])).

fof(f378,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ r2_relset_1(sK0,sK1,X0,sK2)
        | r2_relset_1(sK0,sK1,sK2,X0) )
    | ~ spl8_0 ),
    inference(resolution,[],[f54,f77])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | r2_relset_1(X0,X1,X3,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X3,X2)
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X3,X2)
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
       => r2_relset_1(X0,X1,X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t113_funct_2.p',symmetry_r2_relset_1)).

fof(f431,plain,
    ( spl8_74
    | ~ spl8_77
    | spl8_78
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f393,f104,f429,f423,f417])).

fof(f417,plain,
    ( spl8_74
  <=> r2_relset_1(sK0,sK1,sK3,sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_74])])).

fof(f393,plain,
    ( v1_xboole_0(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))))
    | ~ r2_relset_1(sK0,sK1,sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),sK3)
    | r2_relset_1(sK0,sK1,sK3,sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))))
    | ~ spl8_8 ),
    inference(resolution,[],[f377,f379])).

fof(f379,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ r2_relset_1(sK0,sK1,X1,sK3)
        | r2_relset_1(sK0,sK1,sK3,X1) )
    | ~ spl8_8 ),
    inference(resolution,[],[f54,f105])).

fof(f411,plain,
    ( spl8_70
    | spl8_72 ),
    inference(avatar_split_clause,[],[f387,f409,f403])).

fof(f403,plain,
    ( spl8_70
  <=> k1_funct_1(sK2,sK5(sK5(k1_zfmisc_1(sK0)))) = k1_funct_1(sK3,sK5(sK5(k1_zfmisc_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_70])])).

fof(f409,plain,
    ( spl8_72
  <=> v1_xboole_0(sK5(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_72])])).

fof(f387,plain,
    ( v1_xboole_0(sK5(k1_zfmisc_1(sK0)))
    | k1_funct_1(sK2,sK5(sK5(k1_zfmisc_1(sK0)))) = k1_funct_1(sK3,sK5(sK5(k1_zfmisc_1(sK0)))) ),
    inference(resolution,[],[f377,f44])).

fof(f376,plain,
    ( ~ spl8_67
    | spl8_68
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f363,f104,f374,f368])).

fof(f368,plain,
    ( spl8_67
  <=> ~ r2_relset_1(sK0,sK1,sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_67])])).

fof(f374,plain,
    ( spl8_68
  <=> sK3 = sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_68])])).

fof(f363,plain,
    ( sK3 = sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ r2_relset_1(sK0,sK1,sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))),sK3)
    | ~ spl8_8 ),
    inference(resolution,[],[f292,f59])).

fof(f360,plain,
    ( ~ spl8_63
    | spl8_64
    | ~ spl8_0 ),
    inference(avatar_split_clause,[],[f334,f76,f358,f352])).

fof(f358,plain,
    ( spl8_64
  <=> sK2 = sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_64])])).

fof(f334,plain,
    ( sK2 = sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ r2_relset_1(sK0,sK1,sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))),sK2)
    | ~ spl8_0 ),
    inference(resolution,[],[f291,f59])).

fof(f347,plain,
    ( ~ spl8_59
    | spl8_60
    | ~ spl8_0
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f333,f104,f76,f345,f339])).

fof(f345,plain,
    ( spl8_60
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_60])])).

fof(f333,plain,
    ( sK2 = sK3
    | ~ r2_relset_1(sK0,sK1,sK3,sK2)
    | ~ spl8_0
    | ~ spl8_8 ),
    inference(resolution,[],[f291,f105])).

fof(f328,plain,
    ( ~ spl8_57
    | ~ spl8_0
    | spl8_27 ),
    inference(avatar_split_clause,[],[f314,f182,f76,f325])).

fof(f325,plain,
    ( spl8_57
  <=> ~ r2_hidden(k2_zfmisc_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_57])])).

fof(f182,plain,
    ( spl8_27
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f314,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl8_0
    | ~ spl8_27 ),
    inference(duplicate_literal_removal,[],[f313])).

fof(f313,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ r2_hidden(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl8_0
    | ~ spl8_27 ),
    inference(resolution,[],[f294,f288])).

fof(f288,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(X0,sK2) )
    | ~ spl8_0
    | ~ spl8_27 ),
    inference(subsumption_resolution,[],[f287,f183])).

fof(f183,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f182])).

fof(f287,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | v1_xboole_0(k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) )
    | ~ spl8_0 ),
    inference(resolution,[],[f284,f62])).

fof(f284,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(X0,sK2) )
    | ~ spl8_0 ),
    inference(resolution,[],[f63,f77])).

fof(f294,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k2_zfmisc_1(sK0,sK1),X0)
        | ~ r2_hidden(X0,sK2) )
    | ~ spl8_0
    | ~ spl8_27 ),
    inference(resolution,[],[f288,f65])).

fof(f327,plain,
    ( ~ spl8_55
    | ~ spl8_57
    | ~ spl8_0
    | ~ spl8_8
    | spl8_27 ),
    inference(avatar_split_clause,[],[f312,f182,f104,f76,f325,f319])).

fof(f319,plain,
    ( spl8_55
  <=> ~ r2_hidden(k2_zfmisc_1(sK0,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_55])])).

fof(f312,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ r2_hidden(k2_zfmisc_1(sK0,sK1),sK3)
    | ~ spl8_0
    | ~ spl8_8
    | ~ spl8_27 ),
    inference(resolution,[],[f294,f290])).

fof(f290,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(X0,sK3) )
    | ~ spl8_8
    | ~ spl8_27 ),
    inference(subsumption_resolution,[],[f289,f183])).

fof(f289,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | v1_xboole_0(k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) )
    | ~ spl8_8 ),
    inference(resolution,[],[f285,f62])).

fof(f285,plain,
    ( ! [X1] :
        ( m1_subset_1(X1,k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(X1,sK3) )
    | ~ spl8_8 ),
    inference(resolution,[],[f63,f105])).

fof(f307,plain,
    ( ~ spl8_51
    | spl8_52
    | ~ spl8_0
    | spl8_27 ),
    inference(avatar_split_clause,[],[f296,f182,f76,f305,f302])).

fof(f302,plain,
    ( spl8_51
  <=> ~ sP7(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_51])])).

fof(f305,plain,
    ( spl8_52
  <=> ! [X2] : ~ r2_hidden(X2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).

fof(f296,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK2)
        | ~ sP7(k2_zfmisc_1(sK0,sK1)) )
    | ~ spl8_0
    | ~ spl8_27 ),
    inference(resolution,[],[f288,f70])).

fof(f282,plain,
    ( ~ spl8_49
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f272,f149,f280])).

fof(f280,plain,
    ( spl8_49
  <=> ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).

fof(f149,plain,
    ( spl8_20
  <=> r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f272,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)),sK3)
    | ~ spl8_20 ),
    inference(resolution,[],[f150,f65])).

fof(f150,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f149])).

fof(f271,plain,
    ( ~ spl8_47
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f261,f136,f269])).

fof(f269,plain,
    ( spl8_47
  <=> ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).

fof(f136,plain,
    ( spl8_16
  <=> r2_hidden(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f261,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)),sK2)
    | ~ spl8_16 ),
    inference(resolution,[],[f137,f65])).

fof(f137,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f136])).

fof(f260,plain,
    ( spl8_44
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f245,f104,f258])).

fof(f258,plain,
    ( spl8_44
  <=> r2_relset_1(sK0,sK1,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_44])])).

fof(f245,plain,
    ( r2_relset_1(sK0,sK1,sK3,sK3)
    | ~ spl8_8 ),
    inference(resolution,[],[f71,f105])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f66])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f253,plain,
    ( spl8_42
    | ~ spl8_0 ),
    inference(avatar_split_clause,[],[f244,f76,f251])).

fof(f251,plain,
    ( spl8_42
  <=> r2_relset_1(sK0,sK1,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f244,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl8_0 ),
    inference(resolution,[],[f71,f77])).

fof(f243,plain,
    ( spl8_40
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f208,f201,f241])).

fof(f241,plain,
    ( spl8_40
  <=> m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f201,plain,
    ( spl8_30
  <=> k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) = sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f208,plain,
    ( m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))
    | ~ spl8_30 ),
    inference(superposition,[],[f59,f202])).

fof(f202,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) = sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f201])).

fof(f236,plain,
    ( spl8_34
    | spl8_38
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f207,f201,f234,f221])).

fof(f221,plain,
    ( spl8_34
  <=> v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f234,plain,
    ( spl8_38
  <=> r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f207,plain,
    ( r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))
    | ~ spl8_30 ),
    inference(superposition,[],[f131,f202])).

fof(f229,plain,
    ( spl8_34
    | ~ spl8_37
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f206,f201,f227,f221])).

fof(f227,plain,
    ( spl8_37
  <=> ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f206,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))
    | ~ spl8_30 ),
    inference(superposition,[],[f165,f202])).

fof(f165,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK5(X0))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f131,f65])).

fof(f216,plain,
    ( spl8_32
    | ~ spl8_18
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f209,f201,f142,f214])).

fof(f214,plain,
    ( spl8_32
  <=> sP7(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f142,plain,
    ( spl8_18
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f209,plain,
    ( sP7(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_18
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f205,f143])).

fof(f143,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f142])).

fof(f205,plain,
    ( sP7(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_30 ),
    inference(superposition,[],[f171,f202])).

fof(f203,plain,
    ( spl8_30
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f195,f142,f201])).

fof(f195,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) = sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))
    | ~ spl8_18 ),
    inference(resolution,[],[f193,f143])).

fof(f193,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) = sK5(k1_zfmisc_1(X0)) )
    | ~ spl8_18 ),
    inference(resolution,[],[f192,f152])).

fof(f152,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) = X0 )
    | ~ spl8_18 ),
    inference(resolution,[],[f143,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t113_funct_2.p',t8_boole)).

fof(f191,plain,
    ( spl8_28
    | ~ spl8_27
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f170,f104,f182,f189])).

fof(f189,plain,
    ( spl8_28
  <=> sP7(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f170,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | sP7(sK3)
    | ~ spl8_8 ),
    inference(resolution,[],[f69,f105])).

fof(f184,plain,
    ( spl8_24
    | ~ spl8_27
    | ~ spl8_0 ),
    inference(avatar_split_clause,[],[f169,f76,f182,f176])).

fof(f176,plain,
    ( spl8_24
  <=> sP7(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f169,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | sP7(sK2)
    | ~ spl8_0 ),
    inference(resolution,[],[f69,f77])).

fof(f163,plain,
    ( ~ spl8_23
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f154,f104,f160])).

fof(f160,plain,
    ( spl8_23
  <=> ~ sP6(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f154,plain,
    ( ~ sP6(sK1,sK0)
    | ~ spl8_8 ),
    inference(resolution,[],[f68,f105])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ sP6(X1,X0) ) ),
    inference(general_splitting,[],[f55,f67_D])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2)
      | sP6(X1,X0) ) ),
    inference(cnf_transformation,[],[f67_D])).

fof(f67_D,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | r2_relset_1(X0,X1,X2,X2) )
    <=> ~ sP6(X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t113_funct_2.p',reflexivity_r2_relset_1)).

fof(f162,plain,
    ( ~ spl8_23
    | ~ spl8_0 ),
    inference(avatar_split_clause,[],[f153,f76,f160])).

fof(f153,plain,
    ( ~ sP6(sK1,sK0)
    | ~ spl8_0 ),
    inference(resolution,[],[f68,f77])).

fof(f151,plain,
    ( spl8_20
    | spl8_18
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f130,f104,f142,f149])).

fof(f130,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_8 ),
    inference(resolution,[],[f62,f105])).

fof(f144,plain,
    ( spl8_16
    | spl8_18
    | ~ spl8_0 ),
    inference(avatar_split_clause,[],[f129,f76,f142,f136])).

fof(f129,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r2_hidden(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_0 ),
    inference(resolution,[],[f62,f77])).

fof(f128,plain,(
    spl8_14 ),
    inference(avatar_split_clause,[],[f121,f126])).

fof(f126,plain,
    ( spl8_14
  <=> k1_funct_1(sK2,sK5(sK0)) = k1_funct_1(sK3,sK5(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f121,plain,(
    k1_funct_1(sK2,sK5(sK0)) = k1_funct_1(sK3,sK5(sK0)) ),
    inference(resolution,[],[f59,f44])).

fof(f120,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f45,f118])).

fof(f45,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f113,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f46,f111])).

fof(f46,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f106,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f47,f104])).

fof(f47,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f99,plain,(
    ~ spl8_7 ),
    inference(avatar_split_clause,[],[f48,f97])).

fof(f48,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f92,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f49,f90])).

fof(f49,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f85,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f50,f83])).

fof(f50,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f78,plain,(
    spl8_0 ),
    inference(avatar_split_clause,[],[f51,f76])).

fof(f51,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
