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
% DateTime   : Thu Dec  3 13:01:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 311 expanded)
%              Number of leaves         :   39 ( 131 expanded)
%              Depth                    :   15
%              Number of atoms          :  586 (1377 expanded)
%              Number of equality atoms :  137 ( 272 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1514,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f69,f74,f79,f84,f89,f94,f107,f112,f118,f128,f149,f159,f369,f408,f560,f572,f604,f610,f629,f814,f878,f900,f1402,f1405,f1513])).

fof(f1513,plain,
    ( ~ spl5_4
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_37
    | ~ spl5_41
    | ~ spl5_84
    | spl5_93
    | ~ spl5_107 ),
    inference(avatar_contradiction_clause,[],[f1512])).

fof(f1512,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_37
    | ~ spl5_41
    | ~ spl5_84
    | spl5_93
    | ~ spl5_107 ),
    inference(subsumption_resolution,[],[f1511,f303])).

fof(f303,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl5_37 ),
    inference(avatar_component_clause,[],[f301])).

fof(f301,plain,
    ( spl5_37
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f1511,plain,
    ( sK0 != k1_relat_1(sK3)
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_41
    | ~ spl5_84
    | spl5_93
    | ~ spl5_107 ),
    inference(forward_demodulation,[],[f1510,f830])).

fof(f830,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl5_84 ),
    inference(avatar_component_clause,[],[f828])).

fof(f828,plain,
    ( spl5_84
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_84])])).

fof(f1510,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK2)
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_41
    | spl5_93
    | ~ spl5_107 ),
    inference(subsumption_resolution,[],[f1509,f373])).

fof(f373,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_41 ),
    inference(avatar_component_clause,[],[f371])).

fof(f371,plain,
    ( spl5_41
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f1509,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_9
    | spl5_93
    | ~ spl5_107 ),
    inference(subsumption_resolution,[],[f1508,f93])).

fof(f93,plain,
    ( v1_funct_1(sK2)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl5_7
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f1508,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl5_4
    | ~ spl5_9
    | spl5_93
    | ~ spl5_107 ),
    inference(subsumption_resolution,[],[f1507,f111])).

fof(f111,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl5_9
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f1507,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl5_4
    | spl5_93
    | ~ spl5_107 ),
    inference(subsumption_resolution,[],[f1506,f78])).

fof(f78,plain,
    ( v1_funct_1(sK3)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl5_4
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f1506,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl5_93
    | ~ spl5_107 ),
    inference(subsumption_resolution,[],[f1502,f1219])).

fof(f1219,plain,
    ( sK2 != sK3
    | spl5_93 ),
    inference(avatar_component_clause,[],[f1218])).

fof(f1218,plain,
    ( spl5_93
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_93])])).

fof(f1502,plain,
    ( sK2 = sK3
    | k1_relat_1(sK3) != k1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl5_107 ),
    inference(trivial_inequality_removal,[],[f1501])).

fof(f1501,plain,
    ( k1_funct_1(sK2,sK4(sK2,sK3)) != k1_funct_1(sK2,sK4(sK2,sK3))
    | sK2 = sK3
    | k1_relat_1(sK3) != k1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl5_107 ),
    inference(superposition,[],[f41,f1401])).

fof(f1401,plain,
    ( k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3))
    | ~ spl5_107 ),
    inference(avatar_component_clause,[],[f1399])).

fof(f1399,plain,
    ( spl5_107
  <=> k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_107])])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | X0 = X1
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
            & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

fof(f1405,plain,
    ( sK2 != sK3
    | r2_relset_1(sK0,sK1,sK2,sK3)
    | ~ r2_relset_1(sK0,sK1,sK3,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1402,plain,
    ( spl5_107
    | spl5_93
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_37
    | ~ spl5_41
    | ~ spl5_84 ),
    inference(avatar_split_clause,[],[f1397,f828,f371,f301,f109,f91,f76,f1218,f1399])).

fof(f1397,plain,
    ( sK2 = sK3
    | k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3))
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_37
    | ~ spl5_41
    | ~ spl5_84 ),
    inference(subsumption_resolution,[],[f1396,f111])).

fof(f1396,plain,
    ( sK2 = sK3
    | k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_37
    | ~ spl5_41
    | ~ spl5_84 ),
    inference(subsumption_resolution,[],[f1389,f78])).

fof(f1389,plain,
    ( sK2 = sK3
    | k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl5_7
    | ~ spl5_37
    | ~ spl5_41
    | ~ spl5_84 ),
    inference(trivial_inequality_removal,[],[f1388])).

fof(f1388,plain,
    ( sK0 != sK0
    | sK2 = sK3
    | k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl5_7
    | ~ spl5_37
    | ~ spl5_41
    | ~ spl5_84 ),
    inference(superposition,[],[f1280,f303])).

fof(f1280,plain,
    ( ! [X1] :
        ( k1_relat_1(X1) != sK0
        | sK2 = X1
        | k1_funct_1(sK2,sK4(sK2,X1)) = k1_funct_1(sK3,sK4(sK2,X1))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl5_7
    | ~ spl5_41
    | ~ spl5_84 ),
    inference(resolution,[],[f36,f1138])).

fof(f1138,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK2,X0),sK0)
        | sK2 = X0
        | k1_relat_1(X0) != sK0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl5_7
    | ~ spl5_41
    | ~ spl5_84 ),
    inference(subsumption_resolution,[],[f1137,f373])).

fof(f1137,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK2,X0),sK0)
        | sK2 = X0
        | k1_relat_1(X0) != sK0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl5_7
    | ~ spl5_84 ),
    inference(subsumption_resolution,[],[f1136,f93])).

fof(f1136,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK2,X0),sK0)
        | sK2 = X0
        | k1_relat_1(X0) != sK0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl5_84 ),
    inference(superposition,[],[f40,f830])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | X0 = X1
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f36,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK0)
      | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
    & ! [X4] :
        ( k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
        | ~ r2_hidden(X4,sK0) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f24,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,X0) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK0,sK1,sK2,X3)
          & ! [X4] :
              ( k1_funct_1(X3,X4) = k1_funct_1(sK2,X4)
              | ~ r2_hidden(X4,sK0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_2(X3,sK0,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X3] :
        ( ~ r2_relset_1(sK0,sK1,sK2,X3)
        & ! [X4] :
            ( k1_funct_1(X3,X4) = k1_funct_1(sK2,X4)
            | ~ r2_hidden(X4,sK0) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        & v1_funct_2(X3,sK0,sK1)
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
      & ! [X4] :
          ( k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
          | ~ r2_hidden(X4,sK0) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
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
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).

fof(f900,plain,
    ( ~ spl5_40
    | spl5_43 ),
    inference(avatar_contradiction_clause,[],[f899])).

fof(f899,plain,
    ( $false
    | ~ spl5_40
    | spl5_43 ),
    inference(subsumption_resolution,[],[f891,f383])).

fof(f383,plain,
    ( k1_xboole_0 != sK2
    | spl5_43 ),
    inference(avatar_component_clause,[],[f382])).

fof(f382,plain,
    ( spl5_43
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f891,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_40 ),
    inference(unit_resulting_resolution,[],[f50,f368,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f368,plain,
    ( v1_xboole_0(sK2)
    | ~ spl5_40 ),
    inference(avatar_component_clause,[],[f366])).

fof(f366,plain,
    ( spl5_40
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f50,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f878,plain,
    ( spl5_84
    | ~ spl5_73
    | ~ spl5_74 ),
    inference(avatar_split_clause,[],[f877,f614,f606,f828])).

fof(f606,plain,
    ( spl5_73
  <=> k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).

fof(f614,plain,
    ( spl5_74
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).

fof(f877,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl5_73
    | ~ spl5_74 ),
    inference(backward_demodulation,[],[f608,f616])).

fof(f616,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl5_74 ),
    inference(avatar_component_clause,[],[f614])).

fof(f608,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)
    | ~ spl5_73 ),
    inference(avatar_component_clause,[],[f606])).

fof(f814,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != sK3
    | r2_relset_1(sK0,sK1,sK2,sK3)
    | ~ r2_relset_1(sK0,sK1,sK3,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f629,plain,
    ( spl5_74
    | spl5_12
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f611,f86,f81,f125,f614])).

fof(f125,plain,
    ( spl5_12
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f81,plain,
    ( spl5_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f86,plain,
    ( spl5_6
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f611,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f595,f88])).

fof(f88,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f86])).

fof(f595,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl5_5 ),
    inference(resolution,[],[f83,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f83,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f610,plain,
    ( spl5_73
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f594,f81,f606])).

fof(f594,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)
    | ~ spl5_5 ),
    inference(resolution,[],[f83,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f604,plain,
    ( spl5_41
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f592,f81,f371])).

fof(f592,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f83,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f572,plain,
    ( ~ spl5_20
    | spl5_21 ),
    inference(avatar_contradiction_clause,[],[f571])).

fof(f571,plain,
    ( $false
    | ~ spl5_20
    | spl5_21 ),
    inference(subsumption_resolution,[],[f563,f193])).

fof(f193,plain,
    ( k1_xboole_0 != sK3
    | spl5_21 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl5_21
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f563,plain,
    ( k1_xboole_0 = sK3
    | ~ spl5_20 ),
    inference(unit_resulting_resolution,[],[f50,f188,f51])).

fof(f188,plain,
    ( v1_xboole_0(sK3)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl5_20
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f560,plain,
    ( spl5_37
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f304,f121,f114,f301])).

fof(f114,plain,
    ( spl5_10
  <=> k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f121,plain,
    ( spl5_11
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f304,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f116,f123])).

fof(f123,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f121])).

fof(f116,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f114])).

fof(f408,plain,
    ( spl5_20
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f177,f146,f186])).

fof(f146,plain,
    ( spl5_15
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f177,plain,
    ( v1_xboole_0(sK3)
    | ~ spl5_15 ),
    inference(unit_resulting_resolution,[],[f50,f148,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f148,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f146])).

fof(f369,plain,
    ( spl5_40
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f352,f156,f366])).

fof(f156,plain,
    ( spl5_17
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f352,plain,
    ( v1_xboole_0(sK2)
    | ~ spl5_17 ),
    inference(unit_resulting_resolution,[],[f50,f158,f52])).

fof(f158,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f156])).

fof(f159,plain,
    ( spl5_17
    | ~ spl5_5
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f136,f125,f81,f156])).

fof(f136,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl5_5
    | ~ spl5_12 ),
    inference(backward_demodulation,[],[f83,f127])).

fof(f127,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f125])).

fof(f149,plain,
    ( spl5_15
    | ~ spl5_2
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f134,f125,f66,f146])).

fof(f66,plain,
    ( spl5_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f134,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl5_2
    | ~ spl5_12 ),
    inference(backward_demodulation,[],[f68,f127])).

fof(f68,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f128,plain,
    ( spl5_11
    | spl5_12
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f119,f71,f66,f125,f121])).

fof(f71,plain,
    ( spl5_3
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f119,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f99,f73])).

fof(f73,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f99,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl5_2 ),
    inference(resolution,[],[f68,f42])).

fof(f118,plain,
    ( spl5_10
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f98,f66,f114])).

fof(f98,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl5_2 ),
    inference(resolution,[],[f68,f48])).

fof(f112,plain,
    ( spl5_9
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f96,f66,f109])).

fof(f96,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f68,f49])).

fof(f107,plain,
    ( spl5_8
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f97,f66,f104])).

fof(f104,plain,
    ( spl5_8
  <=> r2_relset_1(sK0,sK1,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f97,plain,
    ( r2_relset_1(sK0,sK1,sK3,sK3)
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f68,f59])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f53])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f94,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f30,f91])).

fof(f30,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f89,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f31,f86])).

fof(f31,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f84,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f32,f81])).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f79,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f33,f76])).

fof(f33,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f74,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f34,f71])).

fof(f34,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f69,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f35,f66])).

fof(f35,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f64,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f37,f61])).

fof(f61,plain,
    ( spl5_1
  <=> r2_relset_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f37,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:18:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (344)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (344)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f1514,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f64,f69,f74,f79,f84,f89,f94,f107,f112,f118,f128,f149,f159,f369,f408,f560,f572,f604,f610,f629,f814,f878,f900,f1402,f1405,f1513])).
% 0.21/0.48  fof(f1513,plain,(
% 0.21/0.48    ~spl5_4 | ~spl5_7 | ~spl5_9 | ~spl5_37 | ~spl5_41 | ~spl5_84 | spl5_93 | ~spl5_107),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f1512])).
% 0.21/0.48  fof(f1512,plain,(
% 0.21/0.48    $false | (~spl5_4 | ~spl5_7 | ~spl5_9 | ~spl5_37 | ~spl5_41 | ~spl5_84 | spl5_93 | ~spl5_107)),
% 0.21/0.48    inference(subsumption_resolution,[],[f1511,f303])).
% 0.21/0.48  fof(f303,plain,(
% 0.21/0.48    sK0 = k1_relat_1(sK3) | ~spl5_37),
% 0.21/0.48    inference(avatar_component_clause,[],[f301])).
% 0.21/0.48  fof(f301,plain,(
% 0.21/0.48    spl5_37 <=> sK0 = k1_relat_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 0.21/0.48  fof(f1511,plain,(
% 0.21/0.48    sK0 != k1_relat_1(sK3) | (~spl5_4 | ~spl5_7 | ~spl5_9 | ~spl5_41 | ~spl5_84 | spl5_93 | ~spl5_107)),
% 0.21/0.48    inference(forward_demodulation,[],[f1510,f830])).
% 0.21/0.48  fof(f830,plain,(
% 0.21/0.48    sK0 = k1_relat_1(sK2) | ~spl5_84),
% 0.21/0.48    inference(avatar_component_clause,[],[f828])).
% 0.21/0.48  fof(f828,plain,(
% 0.21/0.48    spl5_84 <=> sK0 = k1_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_84])])).
% 0.21/0.48  fof(f1510,plain,(
% 0.21/0.48    k1_relat_1(sK3) != k1_relat_1(sK2) | (~spl5_4 | ~spl5_7 | ~spl5_9 | ~spl5_41 | spl5_93 | ~spl5_107)),
% 0.21/0.48    inference(subsumption_resolution,[],[f1509,f373])).
% 0.21/0.48  fof(f373,plain,(
% 0.21/0.48    v1_relat_1(sK2) | ~spl5_41),
% 0.21/0.48    inference(avatar_component_clause,[],[f371])).
% 0.21/0.48  fof(f371,plain,(
% 0.21/0.48    spl5_41 <=> v1_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).
% 0.21/0.48  fof(f1509,plain,(
% 0.21/0.48    k1_relat_1(sK3) != k1_relat_1(sK2) | ~v1_relat_1(sK2) | (~spl5_4 | ~spl5_7 | ~spl5_9 | spl5_93 | ~spl5_107)),
% 0.21/0.48    inference(subsumption_resolution,[],[f1508,f93])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    v1_funct_1(sK2) | ~spl5_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f91])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    spl5_7 <=> v1_funct_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.48  fof(f1508,plain,(
% 0.21/0.48    k1_relat_1(sK3) != k1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl5_4 | ~spl5_9 | spl5_93 | ~spl5_107)),
% 0.21/0.48    inference(subsumption_resolution,[],[f1507,f111])).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    v1_relat_1(sK3) | ~spl5_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f109])).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    spl5_9 <=> v1_relat_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.48  fof(f1507,plain,(
% 0.21/0.48    k1_relat_1(sK3) != k1_relat_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl5_4 | spl5_93 | ~spl5_107)),
% 0.21/0.48    inference(subsumption_resolution,[],[f1506,f78])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    v1_funct_1(sK3) | ~spl5_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f76])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    spl5_4 <=> v1_funct_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.48  fof(f1506,plain,(
% 0.21/0.48    k1_relat_1(sK3) != k1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl5_93 | ~spl5_107)),
% 0.21/0.48    inference(subsumption_resolution,[],[f1502,f1219])).
% 0.21/0.48  fof(f1219,plain,(
% 0.21/0.48    sK2 != sK3 | spl5_93),
% 0.21/0.48    inference(avatar_component_clause,[],[f1218])).
% 0.21/0.48  fof(f1218,plain,(
% 0.21/0.48    spl5_93 <=> sK2 = sK3),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_93])])).
% 0.21/0.48  fof(f1502,plain,(
% 0.21/0.48    sK2 = sK3 | k1_relat_1(sK3) != k1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl5_107),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f1501])).
% 0.21/0.48  fof(f1501,plain,(
% 0.21/0.48    k1_funct_1(sK2,sK4(sK2,sK3)) != k1_funct_1(sK2,sK4(sK2,sK3)) | sK2 = sK3 | k1_relat_1(sK3) != k1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl5_107),
% 0.21/0.48    inference(superposition,[],[f41,f1401])).
% 0.21/0.48  fof(f1401,plain,(
% 0.21/0.48    k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3)) | ~spl5_107),
% 0.21/0.48    inference(avatar_component_clause,[],[f1399])).
% 0.21/0.48  fof(f1399,plain,(
% 0.21/0.48    spl5_107 <=> k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_107])])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) | X0 = X1 | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).
% 0.21/0.48  fof(f1405,plain,(
% 0.21/0.48    sK2 != sK3 | r2_relset_1(sK0,sK1,sK2,sK3) | ~r2_relset_1(sK0,sK1,sK3,sK3)),
% 0.21/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.48  fof(f1402,plain,(
% 0.21/0.48    spl5_107 | spl5_93 | ~spl5_4 | ~spl5_7 | ~spl5_9 | ~spl5_37 | ~spl5_41 | ~spl5_84),
% 0.21/0.48    inference(avatar_split_clause,[],[f1397,f828,f371,f301,f109,f91,f76,f1218,f1399])).
% 0.21/0.48  fof(f1397,plain,(
% 0.21/0.48    sK2 = sK3 | k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3)) | (~spl5_4 | ~spl5_7 | ~spl5_9 | ~spl5_37 | ~spl5_41 | ~spl5_84)),
% 0.21/0.48    inference(subsumption_resolution,[],[f1396,f111])).
% 0.21/0.48  fof(f1396,plain,(
% 0.21/0.48    sK2 = sK3 | k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3)) | ~v1_relat_1(sK3) | (~spl5_4 | ~spl5_7 | ~spl5_37 | ~spl5_41 | ~spl5_84)),
% 0.21/0.48    inference(subsumption_resolution,[],[f1389,f78])).
% 0.21/0.48  fof(f1389,plain,(
% 0.21/0.48    sK2 = sK3 | k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl5_7 | ~spl5_37 | ~spl5_41 | ~spl5_84)),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f1388])).
% 0.21/0.48  fof(f1388,plain,(
% 0.21/0.48    sK0 != sK0 | sK2 = sK3 | k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl5_7 | ~spl5_37 | ~spl5_41 | ~spl5_84)),
% 0.21/0.48    inference(superposition,[],[f1280,f303])).
% 0.21/0.48  fof(f1280,plain,(
% 0.21/0.48    ( ! [X1] : (k1_relat_1(X1) != sK0 | sK2 = X1 | k1_funct_1(sK2,sK4(sK2,X1)) = k1_funct_1(sK3,sK4(sK2,X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) ) | (~spl5_7 | ~spl5_41 | ~spl5_84)),
% 0.21/0.48    inference(resolution,[],[f36,f1138])).
% 0.21/0.48  fof(f1138,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(sK4(sK2,X0),sK0) | sK2 = X0 | k1_relat_1(X0) != sK0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl5_7 | ~spl5_41 | ~spl5_84)),
% 0.21/0.48    inference(subsumption_resolution,[],[f1137,f373])).
% 0.21/0.48  fof(f1137,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(sK4(sK2,X0),sK0) | sK2 = X0 | k1_relat_1(X0) != sK0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK2)) ) | (~spl5_7 | ~spl5_84)),
% 0.21/0.48    inference(subsumption_resolution,[],[f1136,f93])).
% 0.21/0.48  fof(f1136,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(sK4(sK2,X0),sK0) | sK2 = X0 | k1_relat_1(X0) != sK0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl5_84),
% 0.21/0.48    inference(superposition,[],[f40,f830])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | X0 = X1 | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X4] : (~r2_hidden(X4,sK0) | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    (~r2_relset_1(sK0,sK1,sK2,sK3) & ! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f24,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK2,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK2,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) => (~r2_relset_1(sK0,sK1,sK2,sK3) & ! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.48    inference(flattening,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.21/0.48    inference(negated_conjecture,[],[f9])).
% 0.21/0.48  fof(f9,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).
% 0.21/0.48  fof(f900,plain,(
% 0.21/0.48    ~spl5_40 | spl5_43),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f899])).
% 0.21/0.48  fof(f899,plain,(
% 0.21/0.48    $false | (~spl5_40 | spl5_43)),
% 0.21/0.48    inference(subsumption_resolution,[],[f891,f383])).
% 0.21/0.48  fof(f383,plain,(
% 0.21/0.48    k1_xboole_0 != sK2 | spl5_43),
% 0.21/0.48    inference(avatar_component_clause,[],[f382])).
% 0.21/0.48  fof(f382,plain,(
% 0.21/0.48    spl5_43 <=> k1_xboole_0 = sK2),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).
% 0.21/0.48  fof(f891,plain,(
% 0.21/0.48    k1_xboole_0 = sK2 | ~spl5_40),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f50,f368,f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~v1_xboole_0(X0) | X0 = X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 0.21/0.48  fof(f368,plain,(
% 0.21/0.48    v1_xboole_0(sK2) | ~spl5_40),
% 0.21/0.48    inference(avatar_component_clause,[],[f366])).
% 0.21/0.48  fof(f366,plain,(
% 0.21/0.48    spl5_40 <=> v1_xboole_0(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.48  fof(f878,plain,(
% 0.21/0.48    spl5_84 | ~spl5_73 | ~spl5_74),
% 0.21/0.48    inference(avatar_split_clause,[],[f877,f614,f606,f828])).
% 0.21/0.48  fof(f606,plain,(
% 0.21/0.48    spl5_73 <=> k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).
% 0.21/0.48  fof(f614,plain,(
% 0.21/0.48    spl5_74 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).
% 0.21/0.48  fof(f877,plain,(
% 0.21/0.48    sK0 = k1_relat_1(sK2) | (~spl5_73 | ~spl5_74)),
% 0.21/0.48    inference(backward_demodulation,[],[f608,f616])).
% 0.21/0.48  fof(f616,plain,(
% 0.21/0.48    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl5_74),
% 0.21/0.48    inference(avatar_component_clause,[],[f614])).
% 0.21/0.48  fof(f608,plain,(
% 0.21/0.48    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) | ~spl5_73),
% 0.21/0.48    inference(avatar_component_clause,[],[f606])).
% 0.21/0.48  fof(f814,plain,(
% 0.21/0.48    k1_xboole_0 != sK2 | k1_xboole_0 != sK3 | r2_relset_1(sK0,sK1,sK2,sK3) | ~r2_relset_1(sK0,sK1,sK3,sK3)),
% 0.21/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.48  fof(f629,plain,(
% 0.21/0.48    spl5_74 | spl5_12 | ~spl5_5 | ~spl5_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f611,f86,f81,f125,f614])).
% 0.21/0.48  fof(f125,plain,(
% 0.21/0.48    spl5_12 <=> k1_xboole_0 = sK1),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    spl5_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    spl5_6 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.48  fof(f611,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | (~spl5_5 | ~spl5_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f595,f88])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    v1_funct_2(sK2,sK0,sK1) | ~spl5_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f86])).
% 0.21/0.48  fof(f595,plain,(
% 0.21/0.48    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl5_5),
% 0.21/0.48    inference(resolution,[],[f83,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(nnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(flattening,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f81])).
% 0.21/0.48  fof(f610,plain,(
% 0.21/0.48    spl5_73 | ~spl5_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f594,f81,f606])).
% 0.21/0.48  fof(f594,plain,(
% 0.21/0.48    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) | ~spl5_5),
% 0.21/0.48    inference(resolution,[],[f83,f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.48  fof(f604,plain,(
% 0.21/0.48    spl5_41 | ~spl5_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f592,f81,f371])).
% 0.21/0.48  fof(f592,plain,(
% 0.21/0.48    v1_relat_1(sK2) | ~spl5_5),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f83,f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.48  fof(f572,plain,(
% 0.21/0.48    ~spl5_20 | spl5_21),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f571])).
% 0.21/0.48  fof(f571,plain,(
% 0.21/0.48    $false | (~spl5_20 | spl5_21)),
% 0.21/0.48    inference(subsumption_resolution,[],[f563,f193])).
% 0.21/0.48  fof(f193,plain,(
% 0.21/0.48    k1_xboole_0 != sK3 | spl5_21),
% 0.21/0.48    inference(avatar_component_clause,[],[f192])).
% 0.21/0.48  fof(f192,plain,(
% 0.21/0.48    spl5_21 <=> k1_xboole_0 = sK3),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.21/0.48  fof(f563,plain,(
% 0.21/0.48    k1_xboole_0 = sK3 | ~spl5_20),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f50,f188,f51])).
% 0.21/0.48  fof(f188,plain,(
% 0.21/0.48    v1_xboole_0(sK3) | ~spl5_20),
% 0.21/0.48    inference(avatar_component_clause,[],[f186])).
% 0.21/0.49  fof(f186,plain,(
% 0.21/0.49    spl5_20 <=> v1_xboole_0(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.21/0.49  fof(f560,plain,(
% 0.21/0.49    spl5_37 | ~spl5_10 | ~spl5_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f304,f121,f114,f301])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    spl5_10 <=> k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    spl5_11 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.49  fof(f304,plain,(
% 0.21/0.49    sK0 = k1_relat_1(sK3) | (~spl5_10 | ~spl5_11)),
% 0.21/0.49    inference(forward_demodulation,[],[f116,f123])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl5_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f121])).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) | ~spl5_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f114])).
% 0.21/0.49  fof(f408,plain,(
% 0.21/0.49    spl5_20 | ~spl5_15),
% 0.21/0.49    inference(avatar_split_clause,[],[f177,f146,f186])).
% 0.21/0.49  fof(f146,plain,(
% 0.21/0.49    spl5_15 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.49  fof(f177,plain,(
% 0.21/0.49    v1_xboole_0(sK3) | ~spl5_15),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f50,f148,f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).
% 0.21/0.49  fof(f148,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl5_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f146])).
% 0.21/0.49  fof(f369,plain,(
% 0.21/0.49    spl5_40 | ~spl5_17),
% 0.21/0.49    inference(avatar_split_clause,[],[f352,f156,f366])).
% 0.21/0.49  fof(f156,plain,(
% 0.21/0.49    spl5_17 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.49  fof(f352,plain,(
% 0.21/0.49    v1_xboole_0(sK2) | ~spl5_17),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f50,f158,f52])).
% 0.21/0.49  fof(f158,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl5_17),
% 0.21/0.49    inference(avatar_component_clause,[],[f156])).
% 0.21/0.49  fof(f159,plain,(
% 0.21/0.49    spl5_17 | ~spl5_5 | ~spl5_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f136,f125,f81,f156])).
% 0.21/0.49  fof(f136,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl5_5 | ~spl5_12)),
% 0.21/0.49    inference(backward_demodulation,[],[f83,f127])).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    k1_xboole_0 = sK1 | ~spl5_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f125])).
% 0.21/0.49  fof(f149,plain,(
% 0.21/0.49    spl5_15 | ~spl5_2 | ~spl5_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f134,f125,f66,f146])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    spl5_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl5_2 | ~spl5_12)),
% 0.21/0.49    inference(backward_demodulation,[],[f68,f127])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f66])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    spl5_11 | spl5_12 | ~spl5_2 | ~spl5_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f119,f71,f66,f125,f121])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    spl5_3 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | (~spl5_2 | ~spl5_3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f99,f73])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    v1_funct_2(sK3,sK0,sK1) | ~spl5_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f71])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl5_2),
% 0.21/0.49    inference(resolution,[],[f68,f42])).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    spl5_10 | ~spl5_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f98,f66,f114])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) | ~spl5_2),
% 0.21/0.49    inference(resolution,[],[f68,f48])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    spl5_9 | ~spl5_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f96,f66,f109])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    v1_relat_1(sK3) | ~spl5_2),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f68,f49])).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    spl5_8 | ~spl5_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f97,f66,f104])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    spl5_8 <=> r2_relset_1(sK0,sK1,sK3,sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    r2_relset_1(sK0,sK1,sK3,sK3) | ~spl5_2),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f68,f59])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(equality_resolution,[],[f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(nnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(flattening,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    spl5_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f30,f91])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    v1_funct_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    spl5_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f31,f86])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    spl5_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f32,f81])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    spl5_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f33,f76])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    v1_funct_1(sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    spl5_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f34,f71])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    spl5_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f35,f66])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ~spl5_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f37,f61])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    spl5_1 <=> r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (344)------------------------------
% 0.21/0.49  % (344)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (344)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (344)Memory used [KB]: 7036
% 0.21/0.49  % (344)Time elapsed: 0.062 s
% 0.21/0.49  % (344)------------------------------
% 0.21/0.49  % (344)------------------------------
% 0.21/0.49  % (330)Success in time 0.13 s
%------------------------------------------------------------------------------
