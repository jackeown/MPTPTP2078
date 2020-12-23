%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:50 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 285 expanded)
%              Number of leaves         :   37 (  96 expanded)
%              Depth                    :   10
%              Number of atoms          :  471 (1356 expanded)
%              Number of equality atoms :   81 ( 354 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1085,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f105,f114,f118,f122,f152,f154,f204,f209,f212,f227,f273,f275,f299,f306,f709,f790,f816,f848,f943,f980,f1076])).

fof(f1076,plain,(
    ~ spl4_79 ),
    inference(avatar_contradiction_clause,[],[f1054])).

fof(f1054,plain,
    ( $false
    | ~ spl4_79 ),
    inference(subsumption_resolution,[],[f57,f922])).

fof(f922,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ spl4_79 ),
    inference(avatar_component_clause,[],[f920])).

fof(f920,plain,
    ( spl4_79
  <=> sK3 = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_79])])).

fof(f57,plain,(
    sK3 != k2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( ( v2_funct_1(X2)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

fof(f980,plain,
    ( ~ spl4_1
    | spl4_80 ),
    inference(avatar_contradiction_clause,[],[f978])).

fof(f978,plain,
    ( $false
    | ~ spl4_1
    | spl4_80 ),
    inference(unit_resulting_resolution,[],[f100,f126,f927,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f927,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK1)
    | spl4_80 ),
    inference(avatar_component_clause,[],[f925])).

fof(f925,plain,
    ( spl4_80
  <=> r1_tarski(k1_relat_1(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_80])])).

fof(f126,plain,(
    v4_relat_1(sK3,sK1) ),
    inference(resolution,[],[f80,f51])).

fof(f51,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f100,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl4_1
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f943,plain,
    ( ~ spl4_1
    | ~ spl4_80
    | spl4_79
    | ~ spl4_68 ),
    inference(avatar_split_clause,[],[f903,f812,f920,f925,f98])).

fof(f812,plain,
    ( spl4_68
  <=> k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).

fof(f903,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ r1_tarski(k1_relat_1(sK3),sK1)
    | ~ v1_relat_1(sK3)
    | ~ spl4_68 ),
    inference(superposition,[],[f91,f814])).

fof(f814,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ spl4_68 ),
    inference(avatar_component_clause,[],[f812])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_partfun1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f75,f61])).

fof(f61,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k5_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(f848,plain,
    ( ~ spl4_3
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_53
    | spl4_67 ),
    inference(avatar_split_clause,[],[f847,f808,f687,f192,f188,f107])).

fof(f107,plain,
    ( spl4_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f188,plain,
    ( spl4_8
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f192,plain,
    ( spl4_9
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f687,plain,
    ( spl4_53
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f808,plain,
    ( spl4_67
  <=> r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).

fof(f847,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_67 ),
    inference(superposition,[],[f810,f70])).

fof(f70,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f810,plain,
    ( ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
    | spl4_67 ),
    inference(avatar_component_clause,[],[f808])).

fof(f816,plain,
    ( ~ spl4_10
    | ~ spl4_67
    | spl4_68
    | ~ spl4_64 ),
    inference(avatar_split_clause,[],[f803,f787,f812,f808,f196])).

fof(f196,plain,
    ( spl4_10
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f787,plain,
    ( spl4_64
  <=> k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).

fof(f803,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_64 ),
    inference(superposition,[],[f90,f789])).

fof(f789,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ spl4_64 ),
    inference(avatar_component_clause,[],[f787])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_partfun1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f74,f61])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f790,plain,
    ( ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_1
    | ~ spl4_3
    | spl4_64
    | ~ spl4_6
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f785,f284,f148,f787,f107,f98,f196,f192,f188])).

fof(f148,plain,
    ( spl4_6
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f284,plain,
    ( spl4_19
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f785,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ spl4_6
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f758,f150])).

fof(f150,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f148])).

fof(f758,plain,
    ( k5_relat_1(k6_partfun1(k2_relat_1(sK2)),sK3) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ spl4_19 ),
    inference(superposition,[],[f181,f286])).

fof(f286,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f284])).

fof(f181,plain,(
    ! [X10,X9] :
      ( k5_relat_1(k2_funct_1(X9),k5_relat_1(X9,X10)) = k5_relat_1(k6_partfun1(k2_relat_1(X9)),X10)
      | ~ v1_relat_1(X9)
      | ~ v1_relat_1(X10)
      | ~ v1_relat_1(k2_funct_1(X9))
      | ~ v1_funct_1(X9)
      | ~ v2_funct_1(X9) ) ),
    inference(duplicate_literal_removal,[],[f174])).

fof(f174,plain,(
    ! [X10,X9] :
      ( k5_relat_1(k2_funct_1(X9),k5_relat_1(X9,X10)) = k5_relat_1(k6_partfun1(k2_relat_1(X9)),X10)
      | ~ v1_relat_1(X9)
      | ~ v1_relat_1(X10)
      | ~ v1_relat_1(k2_funct_1(X9))
      | ~ v1_funct_1(X9)
      | ~ v2_funct_1(X9)
      | ~ v1_relat_1(X9) ) ),
    inference(superposition,[],[f65,f88])).

fof(f88,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f72,f61])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f709,plain,
    ( ~ spl4_3
    | spl4_53 ),
    inference(avatar_contradiction_clause,[],[f707])).

fof(f707,plain,
    ( $false
    | ~ spl4_3
    | spl4_53 ),
    inference(unit_resulting_resolution,[],[f109,f127,f689,f77])).

fof(f689,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | spl4_53 ),
    inference(avatar_component_clause,[],[f687])).

fof(f127,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f80,f60])).

fof(f60,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f109,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f107])).

fof(f306,plain,
    ( ~ spl4_9
    | ~ spl4_15
    | ~ spl4_16
    | ~ spl4_5
    | spl4_19
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f303,f224,f284,f144,f259,f255,f192])).

fof(f255,plain,
    ( spl4_15
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f259,plain,
    ( spl4_16
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f144,plain,
    ( spl4_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f224,plain,
    ( spl4_13
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f303,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_13 ),
    inference(superposition,[],[f84,f226])).

fof(f226,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f224])).

fof(f84,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f299,plain,(
    spl4_12 ),
    inference(avatar_contradiction_clause,[],[f288])).

fof(f288,plain,
    ( $false
    | spl4_12 ),
    inference(unit_resulting_resolution,[],[f58,f49,f51,f60,f222,f86])).

fof(f86,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f222,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_12 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl4_12
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f49,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f58,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f275,plain,(
    spl4_16 ),
    inference(avatar_contradiction_clause,[],[f274])).

fof(f274,plain,
    ( $false
    | spl4_16 ),
    inference(subsumption_resolution,[],[f49,f261])).

fof(f261,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_16 ),
    inference(avatar_component_clause,[],[f259])).

fof(f273,plain,(
    spl4_15 ),
    inference(avatar_contradiction_clause,[],[f272])).

fof(f272,plain,
    ( $false
    | spl4_15 ),
    inference(subsumption_resolution,[],[f51,f257])).

fof(f257,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_15 ),
    inference(avatar_component_clause,[],[f255])).

fof(f227,plain,
    ( ~ spl4_12
    | spl4_13 ),
    inference(avatar_split_clause,[],[f217,f224,f220])).

fof(f217,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f206,f53])).

fof(f53,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f206,plain,(
    ! [X2,X1] :
      ( ~ r2_relset_1(X2,X2,X1,k6_partfun1(X2))
      | k6_partfun1(X2) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f83,f87])).

fof(f87,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f62,f61])).

fof(f62,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f212,plain,
    ( ~ spl4_3
    | spl4_10 ),
    inference(avatar_contradiction_clause,[],[f210])).

fof(f210,plain,
    ( $false
    | ~ spl4_3
    | spl4_10 ),
    inference(unit_resulting_resolution,[],[f109,f58,f198,f67])).

fof(f67,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f198,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl4_10 ),
    inference(avatar_component_clause,[],[f196])).

fof(f209,plain,(
    spl4_9 ),
    inference(avatar_contradiction_clause,[],[f208])).

fof(f208,plain,
    ( $false
    | spl4_9 ),
    inference(subsumption_resolution,[],[f58,f194])).

fof(f194,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f192])).

fof(f204,plain,(
    spl4_8 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | spl4_8 ),
    inference(subsumption_resolution,[],[f54,f190])).

fof(f190,plain,
    ( ~ v2_funct_1(sK2)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f188])).

fof(f54,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f154,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f60,f146])).

fof(f146,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f144])).

fof(f152,plain,
    ( ~ spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f142,f148,f144])).

fof(f142,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f52,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f52,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f122,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | spl4_4 ),
    inference(unit_resulting_resolution,[],[f73,f113])).

fof(f113,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl4_4
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f73,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f118,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f73,f104])).

fof(f104,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl4_2
  <=> v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f114,plain,
    ( spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f95,f111,f107])).

fof(f95,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f66,f60])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f105,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f94,f102,f98])).

fof(f94,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f66,f51])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:58:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (2886)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.50  % (2897)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.51  % (2902)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.51  % (2893)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.51  % (2913)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.51  % (2902)Refutation not found, incomplete strategy% (2902)------------------------------
% 0.22/0.51  % (2902)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (2891)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (2890)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (2902)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (2902)Memory used [KB]: 10746
% 0.22/0.52  % (2902)Time elapsed: 0.096 s
% 0.22/0.52  % (2902)------------------------------
% 0.22/0.52  % (2902)------------------------------
% 0.22/0.52  % (2889)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.52  % (2894)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.52  % (2911)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.53  % (2895)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.53  % (2909)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (2900)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.54  % (2912)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.54  % (2887)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (2892)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (2888)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (2907)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (2901)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.55  % (2903)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.55  % (2904)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.55  % (2916)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (2910)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.55  % (2914)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.55  % (2899)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.55  % (2915)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.56  % (2896)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.56  % (2905)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.56  % (2906)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.56  % (2898)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.60/0.59  % (2899)Refutation found. Thanks to Tanya!
% 1.60/0.59  % SZS status Theorem for theBenchmark
% 1.60/0.59  % SZS output start Proof for theBenchmark
% 1.78/0.59  fof(f1085,plain,(
% 1.78/0.59    $false),
% 1.78/0.59    inference(avatar_sat_refutation,[],[f105,f114,f118,f122,f152,f154,f204,f209,f212,f227,f273,f275,f299,f306,f709,f790,f816,f848,f943,f980,f1076])).
% 1.78/0.59  fof(f1076,plain,(
% 1.78/0.59    ~spl4_79),
% 1.78/0.59    inference(avatar_contradiction_clause,[],[f1054])).
% 1.78/0.59  fof(f1054,plain,(
% 1.78/0.59    $false | ~spl4_79),
% 1.78/0.59    inference(subsumption_resolution,[],[f57,f922])).
% 1.78/0.59  fof(f922,plain,(
% 1.78/0.59    sK3 = k2_funct_1(sK2) | ~spl4_79),
% 1.78/0.59    inference(avatar_component_clause,[],[f920])).
% 1.78/0.59  fof(f920,plain,(
% 1.78/0.59    spl4_79 <=> sK3 = k2_funct_1(sK2)),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_79])])).
% 1.78/0.59  fof(f57,plain,(
% 1.78/0.59    sK3 != k2_funct_1(sK2)),
% 1.78/0.59    inference(cnf_transformation,[],[f23])).
% 1.78/0.59  fof(f23,plain,(
% 1.78/0.59    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.78/0.59    inference(flattening,[],[f22])).
% 1.78/0.59  fof(f22,plain,(
% 1.78/0.59    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.78/0.59    inference(ennf_transformation,[],[f21])).
% 1.78/0.59  fof(f21,negated_conjecture,(
% 1.78/0.59    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.78/0.59    inference(negated_conjecture,[],[f20])).
% 1.78/0.59  fof(f20,conjecture,(
% 1.78/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.78/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 1.78/0.59  fof(f980,plain,(
% 1.78/0.59    ~spl4_1 | spl4_80),
% 1.78/0.59    inference(avatar_contradiction_clause,[],[f978])).
% 1.78/0.59  fof(f978,plain,(
% 1.78/0.59    $false | (~spl4_1 | spl4_80)),
% 1.78/0.59    inference(unit_resulting_resolution,[],[f100,f126,f927,f77])).
% 1.78/0.59  fof(f77,plain,(
% 1.78/0.59    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v4_relat_1(X1,X0)) )),
% 1.78/0.59    inference(cnf_transformation,[],[f38])).
% 1.78/0.59  fof(f38,plain,(
% 1.78/0.59    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.78/0.59    inference(ennf_transformation,[],[f2])).
% 1.78/0.59  fof(f2,axiom,(
% 1.78/0.59    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.78/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 1.78/0.59  fof(f927,plain,(
% 1.78/0.59    ~r1_tarski(k1_relat_1(sK3),sK1) | spl4_80),
% 1.78/0.59    inference(avatar_component_clause,[],[f925])).
% 1.78/0.59  fof(f925,plain,(
% 1.78/0.59    spl4_80 <=> r1_tarski(k1_relat_1(sK3),sK1)),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_80])])).
% 1.78/0.59  fof(f126,plain,(
% 1.78/0.59    v4_relat_1(sK3,sK1)),
% 1.78/0.59    inference(resolution,[],[f80,f51])).
% 1.78/0.59  fof(f51,plain,(
% 1.78/0.59    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.78/0.59    inference(cnf_transformation,[],[f23])).
% 1.78/0.59  fof(f80,plain,(
% 1.78/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.78/0.59    inference(cnf_transformation,[],[f42])).
% 1.78/0.59  fof(f42,plain,(
% 1.78/0.59    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.78/0.59    inference(ennf_transformation,[],[f13])).
% 1.78/0.59  fof(f13,axiom,(
% 1.78/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.78/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.78/0.59  fof(f100,plain,(
% 1.78/0.59    v1_relat_1(sK3) | ~spl4_1),
% 1.78/0.59    inference(avatar_component_clause,[],[f98])).
% 1.78/0.59  fof(f98,plain,(
% 1.78/0.59    spl4_1 <=> v1_relat_1(sK3)),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.78/0.59  fof(f943,plain,(
% 1.78/0.59    ~spl4_1 | ~spl4_80 | spl4_79 | ~spl4_68),
% 1.78/0.59    inference(avatar_split_clause,[],[f903,f812,f920,f925,f98])).
% 1.78/0.59  fof(f812,plain,(
% 1.78/0.59    spl4_68 <=> k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),sK3)),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).
% 1.78/0.59  fof(f903,plain,(
% 1.78/0.59    sK3 = k2_funct_1(sK2) | ~r1_tarski(k1_relat_1(sK3),sK1) | ~v1_relat_1(sK3) | ~spl4_68),
% 1.78/0.59    inference(superposition,[],[f91,f814])).
% 1.78/0.59  fof(f814,plain,(
% 1.78/0.59    k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),sK3) | ~spl4_68),
% 1.78/0.59    inference(avatar_component_clause,[],[f812])).
% 1.78/0.59  fof(f91,plain,(
% 1.78/0.59    ( ! [X0,X1] : (k5_relat_1(k6_partfun1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.78/0.59    inference(definition_unfolding,[],[f75,f61])).
% 1.78/0.59  fof(f61,plain,(
% 1.78/0.59    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.78/0.59    inference(cnf_transformation,[],[f19])).
% 1.78/0.59  fof(f19,axiom,(
% 1.78/0.59    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.78/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.78/0.59  fof(f75,plain,(
% 1.78/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1) )),
% 1.78/0.59    inference(cnf_transformation,[],[f37])).
% 1.78/0.59  fof(f37,plain,(
% 1.78/0.59    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.78/0.59    inference(flattening,[],[f36])).
% 1.78/0.59  fof(f36,plain,(
% 1.78/0.59    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.78/0.59    inference(ennf_transformation,[],[f7])).
% 1.78/0.59  fof(f7,axiom,(
% 1.78/0.59    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 1.78/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).
% 1.78/0.59  fof(f848,plain,(
% 1.78/0.59    ~spl4_3 | ~spl4_8 | ~spl4_9 | ~spl4_53 | spl4_67),
% 1.78/0.59    inference(avatar_split_clause,[],[f847,f808,f687,f192,f188,f107])).
% 1.78/0.59  fof(f107,plain,(
% 1.78/0.59    spl4_3 <=> v1_relat_1(sK2)),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.78/0.59  fof(f188,plain,(
% 1.78/0.59    spl4_8 <=> v2_funct_1(sK2)),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.78/0.59  fof(f192,plain,(
% 1.78/0.59    spl4_9 <=> v1_funct_1(sK2)),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.78/0.59  fof(f687,plain,(
% 1.78/0.59    spl4_53 <=> r1_tarski(k1_relat_1(sK2),sK0)),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).
% 1.78/0.59  fof(f808,plain,(
% 1.78/0.59    spl4_67 <=> r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).
% 1.78/0.59  fof(f847,plain,(
% 1.78/0.59    ~r1_tarski(k1_relat_1(sK2),sK0) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_67),
% 1.78/0.59    inference(superposition,[],[f810,f70])).
% 1.78/0.59  fof(f70,plain,(
% 1.78/0.59    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.78/0.59    inference(cnf_transformation,[],[f31])).
% 1.78/0.59  fof(f31,plain,(
% 1.78/0.59    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.78/0.59    inference(flattening,[],[f30])).
% 1.78/0.59  fof(f30,plain,(
% 1.78/0.59    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.78/0.59    inference(ennf_transformation,[],[f11])).
% 1.78/0.59  fof(f11,axiom,(
% 1.78/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.78/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 1.78/0.59  fof(f810,plain,(
% 1.78/0.59    ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) | spl4_67),
% 1.78/0.59    inference(avatar_component_clause,[],[f808])).
% 1.78/0.59  fof(f816,plain,(
% 1.78/0.59    ~spl4_10 | ~spl4_67 | spl4_68 | ~spl4_64),
% 1.78/0.59    inference(avatar_split_clause,[],[f803,f787,f812,f808,f196])).
% 1.78/0.59  fof(f196,plain,(
% 1.78/0.59    spl4_10 <=> v1_relat_1(k2_funct_1(sK2))),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.78/0.59  fof(f787,plain,(
% 1.78/0.59    spl4_64 <=> k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3)),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).
% 1.78/0.59  fof(f803,plain,(
% 1.78/0.59    k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),sK3) | ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl4_64),
% 1.78/0.59    inference(superposition,[],[f90,f789])).
% 1.78/0.59  fof(f789,plain,(
% 1.78/0.59    k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3) | ~spl4_64),
% 1.78/0.59    inference(avatar_component_clause,[],[f787])).
% 1.78/0.59  fof(f90,plain,(
% 1.78/0.59    ( ! [X0,X1] : (k5_relat_1(X1,k6_partfun1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.78/0.59    inference(definition_unfolding,[],[f74,f61])).
% 1.78/0.59  fof(f74,plain,(
% 1.78/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1) )),
% 1.78/0.59    inference(cnf_transformation,[],[f35])).
% 1.78/0.59  fof(f35,plain,(
% 1.78/0.59    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.78/0.59    inference(flattening,[],[f34])).
% 1.78/0.59  fof(f34,plain,(
% 1.78/0.59    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.78/0.59    inference(ennf_transformation,[],[f8])).
% 1.78/0.59  fof(f8,axiom,(
% 1.78/0.59    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 1.78/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 1.78/0.59  fof(f790,plain,(
% 1.78/0.59    ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_1 | ~spl4_3 | spl4_64 | ~spl4_6 | ~spl4_19),
% 1.78/0.59    inference(avatar_split_clause,[],[f785,f284,f148,f787,f107,f98,f196,f192,f188])).
% 1.78/0.59  fof(f148,plain,(
% 1.78/0.59    spl4_6 <=> sK1 = k2_relat_1(sK2)),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.78/0.59  fof(f284,plain,(
% 1.78/0.59    spl4_19 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.78/0.59  fof(f785,plain,(
% 1.78/0.59    k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | (~spl4_6 | ~spl4_19)),
% 1.78/0.59    inference(forward_demodulation,[],[f758,f150])).
% 1.78/0.59  fof(f150,plain,(
% 1.78/0.59    sK1 = k2_relat_1(sK2) | ~spl4_6),
% 1.78/0.59    inference(avatar_component_clause,[],[f148])).
% 1.78/0.59  fof(f758,plain,(
% 1.78/0.59    k5_relat_1(k6_partfun1(k2_relat_1(sK2)),sK3) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~spl4_19),
% 1.78/0.59    inference(superposition,[],[f181,f286])).
% 1.78/0.59  fof(f286,plain,(
% 1.78/0.59    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_19),
% 1.78/0.59    inference(avatar_component_clause,[],[f284])).
% 1.78/0.59  fof(f181,plain,(
% 1.78/0.59    ( ! [X10,X9] : (k5_relat_1(k2_funct_1(X9),k5_relat_1(X9,X10)) = k5_relat_1(k6_partfun1(k2_relat_1(X9)),X10) | ~v1_relat_1(X9) | ~v1_relat_1(X10) | ~v1_relat_1(k2_funct_1(X9)) | ~v1_funct_1(X9) | ~v2_funct_1(X9)) )),
% 1.78/0.59    inference(duplicate_literal_removal,[],[f174])).
% 1.78/0.59  fof(f174,plain,(
% 1.78/0.59    ( ! [X10,X9] : (k5_relat_1(k2_funct_1(X9),k5_relat_1(X9,X10)) = k5_relat_1(k6_partfun1(k2_relat_1(X9)),X10) | ~v1_relat_1(X9) | ~v1_relat_1(X10) | ~v1_relat_1(k2_funct_1(X9)) | ~v1_funct_1(X9) | ~v2_funct_1(X9) | ~v1_relat_1(X9)) )),
% 1.78/0.59    inference(superposition,[],[f65,f88])).
% 1.78/0.59  fof(f88,plain,(
% 1.78/0.59    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.78/0.59    inference(definition_unfolding,[],[f72,f61])).
% 1.78/0.59  fof(f72,plain,(
% 1.78/0.59    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))) )),
% 1.78/0.59    inference(cnf_transformation,[],[f33])).
% 1.78/0.59  fof(f33,plain,(
% 1.78/0.59    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.78/0.59    inference(flattening,[],[f32])).
% 1.78/0.59  fof(f32,plain,(
% 1.78/0.59    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.78/0.59    inference(ennf_transformation,[],[f12])).
% 1.78/0.59  fof(f12,axiom,(
% 1.78/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 1.78/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 1.78/0.59  fof(f65,plain,(
% 1.78/0.59    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 1.78/0.59    inference(cnf_transformation,[],[f26])).
% 1.78/0.59  fof(f26,plain,(
% 1.78/0.59    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.78/0.59    inference(ennf_transformation,[],[f6])).
% 1.78/0.59  fof(f6,axiom,(
% 1.78/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 1.78/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 1.78/0.59  fof(f709,plain,(
% 1.78/0.59    ~spl4_3 | spl4_53),
% 1.78/0.59    inference(avatar_contradiction_clause,[],[f707])).
% 1.78/0.59  fof(f707,plain,(
% 1.78/0.59    $false | (~spl4_3 | spl4_53)),
% 1.78/0.59    inference(unit_resulting_resolution,[],[f109,f127,f689,f77])).
% 1.78/0.59  fof(f689,plain,(
% 1.78/0.59    ~r1_tarski(k1_relat_1(sK2),sK0) | spl4_53),
% 1.78/0.59    inference(avatar_component_clause,[],[f687])).
% 1.78/0.59  fof(f127,plain,(
% 1.78/0.59    v4_relat_1(sK2,sK0)),
% 1.78/0.59    inference(resolution,[],[f80,f60])).
% 1.78/0.59  fof(f60,plain,(
% 1.78/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.78/0.59    inference(cnf_transformation,[],[f23])).
% 1.78/0.59  fof(f109,plain,(
% 1.78/0.59    v1_relat_1(sK2) | ~spl4_3),
% 1.78/0.59    inference(avatar_component_clause,[],[f107])).
% 1.78/0.59  fof(f306,plain,(
% 1.78/0.59    ~spl4_9 | ~spl4_15 | ~spl4_16 | ~spl4_5 | spl4_19 | ~spl4_13),
% 1.78/0.59    inference(avatar_split_clause,[],[f303,f224,f284,f144,f259,f255,f192])).
% 1.78/0.59  fof(f255,plain,(
% 1.78/0.59    spl4_15 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.78/0.59  fof(f259,plain,(
% 1.78/0.59    spl4_16 <=> v1_funct_1(sK3)),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.78/0.59  fof(f144,plain,(
% 1.78/0.59    spl4_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.78/0.59  fof(f224,plain,(
% 1.78/0.59    spl4_13 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.78/0.59  fof(f303,plain,(
% 1.78/0.59    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~spl4_13),
% 1.78/0.59    inference(superposition,[],[f84,f226])).
% 1.78/0.59  fof(f226,plain,(
% 1.78/0.59    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~spl4_13),
% 1.78/0.59    inference(avatar_component_clause,[],[f224])).
% 1.78/0.59  fof(f84,plain,(
% 1.78/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 1.78/0.59    inference(cnf_transformation,[],[f46])).
% 1.78/0.59  fof(f46,plain,(
% 1.78/0.59    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.78/0.59    inference(flattening,[],[f45])).
% 1.78/0.59  fof(f45,plain,(
% 1.78/0.59    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.78/0.59    inference(ennf_transformation,[],[f18])).
% 1.78/0.59  fof(f18,axiom,(
% 1.78/0.59    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.78/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.78/0.59  fof(f299,plain,(
% 1.78/0.59    spl4_12),
% 1.78/0.59    inference(avatar_contradiction_clause,[],[f288])).
% 1.78/0.59  fof(f288,plain,(
% 1.78/0.59    $false | spl4_12),
% 1.78/0.59    inference(unit_resulting_resolution,[],[f58,f49,f51,f60,f222,f86])).
% 1.78/0.59  fof(f86,plain,(
% 1.78/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 1.78/0.59    inference(cnf_transformation,[],[f48])).
% 1.78/0.59  fof(f48,plain,(
% 1.78/0.59    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.78/0.59    inference(flattening,[],[f47])).
% 1.78/0.59  fof(f47,plain,(
% 1.78/0.59    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.78/0.59    inference(ennf_transformation,[],[f17])).
% 1.78/0.59  fof(f17,axiom,(
% 1.78/0.59    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.78/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.78/0.59  fof(f222,plain,(
% 1.78/0.59    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_12),
% 1.78/0.59    inference(avatar_component_clause,[],[f220])).
% 1.78/0.59  fof(f220,plain,(
% 1.78/0.59    spl4_12 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.78/0.59  fof(f49,plain,(
% 1.78/0.59    v1_funct_1(sK3)),
% 1.78/0.59    inference(cnf_transformation,[],[f23])).
% 1.78/0.59  fof(f58,plain,(
% 1.78/0.59    v1_funct_1(sK2)),
% 1.78/0.59    inference(cnf_transformation,[],[f23])).
% 1.78/0.59  fof(f275,plain,(
% 1.78/0.59    spl4_16),
% 1.78/0.59    inference(avatar_contradiction_clause,[],[f274])).
% 1.78/0.59  fof(f274,plain,(
% 1.78/0.59    $false | spl4_16),
% 1.78/0.59    inference(subsumption_resolution,[],[f49,f261])).
% 1.78/0.59  fof(f261,plain,(
% 1.78/0.59    ~v1_funct_1(sK3) | spl4_16),
% 1.78/0.59    inference(avatar_component_clause,[],[f259])).
% 1.78/0.59  fof(f273,plain,(
% 1.78/0.59    spl4_15),
% 1.78/0.59    inference(avatar_contradiction_clause,[],[f272])).
% 1.78/0.59  fof(f272,plain,(
% 1.78/0.59    $false | spl4_15),
% 1.78/0.59    inference(subsumption_resolution,[],[f51,f257])).
% 1.78/0.59  fof(f257,plain,(
% 1.78/0.59    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_15),
% 1.78/0.59    inference(avatar_component_clause,[],[f255])).
% 1.78/0.59  fof(f227,plain,(
% 1.78/0.59    ~spl4_12 | spl4_13),
% 1.78/0.59    inference(avatar_split_clause,[],[f217,f224,f220])).
% 1.78/0.59  fof(f217,plain,(
% 1.78/0.59    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.78/0.59    inference(resolution,[],[f206,f53])).
% 1.78/0.59  fof(f53,plain,(
% 1.78/0.59    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.78/0.59    inference(cnf_transformation,[],[f23])).
% 1.78/0.59  fof(f206,plain,(
% 1.78/0.59    ( ! [X2,X1] : (~r2_relset_1(X2,X2,X1,k6_partfun1(X2)) | k6_partfun1(X2) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 1.78/0.59    inference(resolution,[],[f83,f87])).
% 1.78/0.59  fof(f87,plain,(
% 1.78/0.59    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.78/0.59    inference(definition_unfolding,[],[f62,f61])).
% 1.78/0.59  fof(f62,plain,(
% 1.78/0.59    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.78/0.59    inference(cnf_transformation,[],[f16])).
% 1.78/0.59  fof(f16,axiom,(
% 1.78/0.59    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.78/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 1.78/0.59  fof(f83,plain,(
% 1.78/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 1.78/0.59    inference(cnf_transformation,[],[f44])).
% 1.78/0.59  fof(f44,plain,(
% 1.78/0.59    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.78/0.59    inference(flattening,[],[f43])).
% 1.78/0.59  fof(f43,plain,(
% 1.78/0.59    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.78/0.59    inference(ennf_transformation,[],[f15])).
% 1.78/0.59  fof(f15,axiom,(
% 1.78/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.78/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.78/0.59  fof(f212,plain,(
% 1.78/0.59    ~spl4_3 | spl4_10),
% 1.78/0.59    inference(avatar_contradiction_clause,[],[f210])).
% 1.78/0.59  fof(f210,plain,(
% 1.78/0.59    $false | (~spl4_3 | spl4_10)),
% 1.78/0.59    inference(unit_resulting_resolution,[],[f109,f58,f198,f67])).
% 1.78/0.59  fof(f67,plain,(
% 1.78/0.59    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.78/0.59    inference(cnf_transformation,[],[f29])).
% 1.78/0.59  fof(f29,plain,(
% 1.78/0.59    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.78/0.59    inference(flattening,[],[f28])).
% 1.78/0.59  fof(f28,plain,(
% 1.78/0.59    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.78/0.59    inference(ennf_transformation,[],[f9])).
% 1.78/0.59  fof(f9,axiom,(
% 1.78/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.78/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.78/0.59  fof(f198,plain,(
% 1.78/0.59    ~v1_relat_1(k2_funct_1(sK2)) | spl4_10),
% 1.78/0.59    inference(avatar_component_clause,[],[f196])).
% 1.78/0.59  fof(f209,plain,(
% 1.78/0.59    spl4_9),
% 1.78/0.59    inference(avatar_contradiction_clause,[],[f208])).
% 1.78/0.59  fof(f208,plain,(
% 1.78/0.59    $false | spl4_9),
% 1.78/0.59    inference(subsumption_resolution,[],[f58,f194])).
% 1.78/0.59  fof(f194,plain,(
% 1.78/0.59    ~v1_funct_1(sK2) | spl4_9),
% 1.78/0.59    inference(avatar_component_clause,[],[f192])).
% 1.78/0.59  fof(f204,plain,(
% 1.78/0.59    spl4_8),
% 1.78/0.59    inference(avatar_contradiction_clause,[],[f203])).
% 1.78/0.59  fof(f203,plain,(
% 1.78/0.59    $false | spl4_8),
% 1.78/0.59    inference(subsumption_resolution,[],[f54,f190])).
% 1.78/0.59  fof(f190,plain,(
% 1.78/0.59    ~v2_funct_1(sK2) | spl4_8),
% 1.78/0.59    inference(avatar_component_clause,[],[f188])).
% 1.78/0.59  fof(f54,plain,(
% 1.78/0.59    v2_funct_1(sK2)),
% 1.78/0.59    inference(cnf_transformation,[],[f23])).
% 1.78/0.59  fof(f154,plain,(
% 1.78/0.59    spl4_5),
% 1.78/0.59    inference(avatar_contradiction_clause,[],[f153])).
% 1.78/0.59  fof(f153,plain,(
% 1.78/0.59    $false | spl4_5),
% 1.78/0.59    inference(subsumption_resolution,[],[f60,f146])).
% 1.78/0.59  fof(f146,plain,(
% 1.78/0.59    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_5),
% 1.78/0.59    inference(avatar_component_clause,[],[f144])).
% 1.78/0.59  fof(f152,plain,(
% 1.78/0.59    ~spl4_5 | spl4_6),
% 1.78/0.59    inference(avatar_split_clause,[],[f142,f148,f144])).
% 1.78/0.59  fof(f142,plain,(
% 1.78/0.59    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.78/0.59    inference(superposition,[],[f52,f79])).
% 1.78/0.59  fof(f79,plain,(
% 1.78/0.59    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.78/0.59    inference(cnf_transformation,[],[f41])).
% 1.78/0.59  fof(f41,plain,(
% 1.78/0.59    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.78/0.59    inference(ennf_transformation,[],[f14])).
% 1.78/0.59  fof(f14,axiom,(
% 1.78/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.78/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.78/0.59  fof(f52,plain,(
% 1.78/0.59    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.78/0.59    inference(cnf_transformation,[],[f23])).
% 1.78/0.59  fof(f122,plain,(
% 1.78/0.59    spl4_4),
% 1.78/0.59    inference(avatar_contradiction_clause,[],[f119])).
% 1.78/0.59  fof(f119,plain,(
% 1.78/0.59    $false | spl4_4),
% 1.78/0.59    inference(unit_resulting_resolution,[],[f73,f113])).
% 1.78/0.59  fof(f113,plain,(
% 1.78/0.59    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl4_4),
% 1.78/0.59    inference(avatar_component_clause,[],[f111])).
% 1.78/0.59  fof(f111,plain,(
% 1.78/0.59    spl4_4 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.78/0.59  fof(f73,plain,(
% 1.78/0.59    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.78/0.59    inference(cnf_transformation,[],[f3])).
% 1.78/0.59  fof(f3,axiom,(
% 1.78/0.59    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.78/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.78/0.59  fof(f118,plain,(
% 1.78/0.59    spl4_2),
% 1.78/0.59    inference(avatar_contradiction_clause,[],[f115])).
% 1.78/0.59  fof(f115,plain,(
% 1.78/0.59    $false | spl4_2),
% 1.78/0.59    inference(unit_resulting_resolution,[],[f73,f104])).
% 1.78/0.59  fof(f104,plain,(
% 1.78/0.59    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | spl4_2),
% 1.78/0.59    inference(avatar_component_clause,[],[f102])).
% 1.78/0.59  fof(f102,plain,(
% 1.78/0.59    spl4_2 <=> v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.78/0.59  fof(f114,plain,(
% 1.78/0.59    spl4_3 | ~spl4_4),
% 1.78/0.59    inference(avatar_split_clause,[],[f95,f111,f107])).
% 1.78/0.59  fof(f95,plain,(
% 1.78/0.59    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2)),
% 1.78/0.59    inference(resolution,[],[f66,f60])).
% 1.78/0.59  fof(f66,plain,(
% 1.78/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 1.78/0.59    inference(cnf_transformation,[],[f27])).
% 1.78/0.59  fof(f27,plain,(
% 1.78/0.59    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.78/0.59    inference(ennf_transformation,[],[f1])).
% 1.78/0.59  fof(f1,axiom,(
% 1.78/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.78/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.78/0.59  fof(f105,plain,(
% 1.78/0.59    spl4_1 | ~spl4_2),
% 1.78/0.59    inference(avatar_split_clause,[],[f94,f102,f98])).
% 1.78/0.59  fof(f94,plain,(
% 1.78/0.59    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | v1_relat_1(sK3)),
% 1.78/0.59    inference(resolution,[],[f66,f51])).
% 1.78/0.59  % SZS output end Proof for theBenchmark
% 1.78/0.59  % (2899)------------------------------
% 1.78/0.59  % (2899)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.59  % (2899)Termination reason: Refutation
% 1.78/0.59  
% 1.78/0.59  % (2899)Memory used [KB]: 7291
% 1.78/0.59  % (2899)Time elapsed: 0.168 s
% 1.78/0.59  % (2899)------------------------------
% 1.78/0.59  % (2899)------------------------------
% 1.78/0.60  % (2885)Success in time 0.233 s
%------------------------------------------------------------------------------
