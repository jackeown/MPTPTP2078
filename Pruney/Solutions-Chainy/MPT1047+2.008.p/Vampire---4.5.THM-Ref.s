%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:01 EST 2020

% Result     : Theorem 1.70s
% Output     : Refutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 301 expanded)
%              Number of leaves         :   29 ( 108 expanded)
%              Depth                    :   19
%              Number of atoms          :  703 (1329 expanded)
%              Number of equality atoms :  149 ( 273 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f677,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f83,f88,f93,f98,f103,f162,f261,f273,f296,f405,f416,f675,f676])).

fof(f676,plain,
    ( k1_xboole_0 != k5_partfun1(sK0,k1_tarski(sK1),sK2)
    | r2_hidden(sK3,k1_xboole_0)
    | ~ r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f675,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | spl6_13 ),
    inference(avatar_contradiction_clause,[],[f674])).

fof(f674,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | spl6_13 ),
    inference(subsumption_resolution,[],[f673,f77])).

fof(f77,plain,
    ( k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl6_1
  <=> k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f673,plain,
    ( k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(sK3)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | spl6_13 ),
    inference(equality_resolution,[],[f671])).

fof(f671,plain,
    ( ! [X11] :
        ( sK3 != X11
        | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X11) )
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | spl6_13 ),
    inference(subsumption_resolution,[],[f660,f132])).

fof(f132,plain,
    ( k1_xboole_0 != k5_partfun1(sK0,k1_tarski(sK1),sK2)
    | spl6_9 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl6_9
  <=> k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f660,plain,
    ( ! [X11] :
        ( sK3 != X11
        | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
        | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X11) )
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | spl6_13 ),
    inference(duplicate_literal_removal,[],[f657])).

fof(f657,plain,
    ( ! [X11] :
        ( sK3 != X11
        | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
        | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X11)
        | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X11) )
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | spl6_13 ),
    inference(superposition,[],[f56,f641])).

fof(f641,plain,
    ( ! [X1] :
        ( sK3 = sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X1)
        | k1_tarski(X1) = k5_partfun1(sK0,k1_tarski(sK1),sK2) )
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | spl6_13 ),
    inference(subsumption_resolution,[],[f491,f502])).

fof(f502,plain,
    ( ! [X12] :
        ( v1_partfun1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X12),sK0)
        | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X12) )
    | ~ spl6_5
    | ~ spl6_6
    | spl6_9
    | ~ spl6_10
    | spl6_13 ),
    inference(subsumption_resolution,[],[f501,f315])).

fof(f315,plain,
    ( ! [X0] :
        ( v1_funct_2(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0),sK0,k1_tarski(sK1))
        | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2) )
    | ~ spl6_5
    | ~ spl6_6
    | spl6_9 ),
    inference(subsumption_resolution,[],[f313,f132])).

fof(f313,plain,
    ( ! [X0] :
        ( v1_funct_2(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0),sK0,k1_tarski(sK1))
        | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
        | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2) )
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(resolution,[],[f141,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( sK5(X0,X1) != X1
        & r2_hidden(sK5(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK5(X0,X1) != X1
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).

fof(f141,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k5_partfun1(sK0,k1_tarski(sK1),sK2))
        | v1_funct_2(X1,sK0,k1_tarski(sK1)) )
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f139,f102])).

fof(f102,plain,
    ( v1_funct_1(sK2)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl6_6
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f139,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k5_partfun1(sK0,k1_tarski(sK1),sK2))
        | v1_funct_2(X1,sK0,k1_tarski(sK1))
        | ~ v1_funct_1(sK2) )
    | ~ spl6_5 ),
    inference(resolution,[],[f59,f97])).

fof(f97,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl6_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
         => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_2)).

fof(f501,plain,
    ( ! [X12] :
        ( k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X12)
        | v1_partfun1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X12),sK0)
        | ~ v1_funct_2(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X12),sK0,k1_tarski(sK1)) )
    | ~ spl6_5
    | ~ spl6_6
    | spl6_9
    | ~ spl6_10
    | spl6_13 ),
    inference(subsumption_resolution,[],[f500,f136])).

fof(f136,plain,
    ( ! [X0] :
        ( v1_funct_1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0))
        | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2) )
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl6_10
  <=> ! [X0] :
        ( v1_funct_1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0))
        | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f500,plain,
    ( ! [X12] :
        ( k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X12)
        | v1_partfun1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X12),sK0)
        | ~ v1_funct_2(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X12),sK0,k1_tarski(sK1))
        | ~ v1_funct_1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X12)) )
    | ~ spl6_5
    | ~ spl6_6
    | spl6_9
    | spl6_13 ),
    inference(subsumption_resolution,[],[f487,f160])).

fof(f160,plain,
    ( k1_xboole_0 != k1_tarski(sK1)
    | spl6_13 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl6_13
  <=> k1_xboole_0 = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f487,plain,
    ( ! [X12] :
        ( k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X12)
        | k1_xboole_0 = k1_tarski(sK1)
        | v1_partfun1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X12),sK0)
        | ~ v1_funct_2(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X12),sK0,k1_tarski(sK1))
        | ~ v1_funct_1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X12)) )
    | ~ spl6_5
    | ~ spl6_6
    | spl6_9 ),
    inference(resolution,[],[f370,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

fof(f370,plain,
    ( ! [X0] :
        ( m1_subset_1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2) )
    | ~ spl6_5
    | ~ spl6_6
    | spl6_9 ),
    inference(subsumption_resolution,[],[f368,f132])).

fof(f368,plain,
    ( ! [X0] :
        ( m1_subset_1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
        | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2) )
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(resolution,[],[f176,f55])).

fof(f176,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k5_partfun1(sK0,k1_tarski(sK1),sK2))
        | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) )
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f174,f102])).

fof(f174,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k5_partfun1(sK0,k1_tarski(sK1),sK2))
        | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | ~ v1_funct_1(sK2) )
    | ~ spl6_5 ),
    inference(resolution,[],[f60,f97])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f491,plain,
    ( ! [X1] :
        ( k1_tarski(X1) = k5_partfun1(sK0,k1_tarski(sK1),sK2)
        | sK3 = sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X1)
        | ~ v1_partfun1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X1),sK0) )
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_9
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f480,f136])).

fof(f480,plain,
    ( ! [X1] :
        ( k1_tarski(X1) = k5_partfun1(sK0,k1_tarski(sK1),sK2)
        | sK3 = sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X1)
        | ~ v1_partfun1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X1),sK0)
        | ~ v1_funct_1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X1)) )
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_9
    | ~ spl6_12 ),
    inference(resolution,[],[f370,f376])).

fof(f376,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | sK3 = X0
        | ~ v1_partfun1(X0,sK0)
        | ~ v1_funct_1(X0) )
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f189,f180])).

fof(f180,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | r1_partfun1(X0,sK3)
        | ~ v1_funct_1(X0) )
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f178,f92])).

fof(f92,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl6_4
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f178,plain,
    ( ! [X0] :
        ( r1_partfun1(X0,sK3)
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | ~ v1_funct_1(X0) )
    | ~ spl6_2 ),
    inference(resolution,[],[f61,f82])).

fof(f82,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl6_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | r1_partfun1(X2,X3)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_1(X3) )
         => r1_partfun1(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_partfun1)).

fof(f189,plain,
    ( ! [X0] :
        ( ~ r1_partfun1(X0,sK3)
        | ~ v1_partfun1(X0,sK0)
        | sK3 = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | ~ v1_funct_1(X0) )
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f188,f92])).

fof(f188,plain,
    ( ! [X0] :
        ( ~ r1_partfun1(X0,sK3)
        | ~ v1_partfun1(X0,sK0)
        | sK3 = X0
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | ~ v1_funct_1(X0) )
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f186,f157])).

fof(f157,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl6_12
  <=> v1_partfun1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f186,plain,
    ( ! [X0] :
        ( ~ r1_partfun1(X0,sK3)
        | ~ v1_partfun1(sK3,sK0)
        | ~ v1_partfun1(X0,sK0)
        | sK3 = X0
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | ~ v1_funct_1(X0) )
    | ~ spl6_2 ),
    inference(resolution,[],[f50,f82])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_partfun1(X2,X3)
      | ~ v1_partfun1(X3,X0)
      | ~ v1_partfun1(X2,X0)
      | X2 = X3
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( ( r1_partfun1(X2,X3)
              & v1_partfun1(X3,X0)
              & v1_partfun1(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( sK5(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f416,plain,(
    ~ spl6_31 ),
    inference(avatar_contradiction_clause,[],[f415])).

fof(f415,plain,
    ( $false
    | ~ spl6_31 ),
    inference(subsumption_resolution,[],[f413,f64])).

fof(f64,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f413,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | ~ spl6_31 ),
    inference(resolution,[],[f398,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f398,plain,
    ( r2_hidden(sK3,k1_xboole_0)
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f396])).

fof(f396,plain,
    ( spl6_31
  <=> r2_hidden(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f405,plain,
    ( spl6_32
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f400,f217,f100,f95,f90,f80,f402])).

fof(f402,plain,
    ( spl6_32
  <=> r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f217,plain,
    ( spl6_18
  <=> ! [X0] :
        ( ~ r1_partfun1(X0,sK3)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f400,plain,
    ( r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK2))
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f391,f102])).

fof(f391,plain,
    ( ~ v1_funct_1(sK2)
    | r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK2))
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_18 ),
    inference(resolution,[],[f386,f97])).

fof(f386,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | ~ v1_funct_1(X0)
        | r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),X0)) )
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f218,f180])).

fof(f218,plain,
    ( ! [X0] :
        ( ~ r1_partfun1(X0,sK3)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),X0)) )
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f217])).

fof(f296,plain,
    ( spl6_10
    | ~ spl6_5
    | ~ spl6_6
    | spl6_9 ),
    inference(avatar_split_clause,[],[f295,f131,f100,f95,f135])).

fof(f295,plain,
    ( ! [X0] :
        ( v1_funct_1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0))
        | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2) )
    | ~ spl6_5
    | ~ spl6_6
    | spl6_9 ),
    inference(subsumption_resolution,[],[f293,f132])).

fof(f293,plain,
    ( ! [X0] :
        ( v1_funct_1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0))
        | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
        | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2) )
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(resolution,[],[f119,f55])).

fof(f119,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k5_partfun1(sK0,k1_tarski(sK1),sK2))
        | v1_funct_1(X1) )
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f117,f102])).

fof(f117,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k5_partfun1(sK0,k1_tarski(sK1),sK2))
        | v1_funct_1(X1)
        | ~ v1_funct_1(sK2) )
    | ~ spl6_5 ),
    inference(resolution,[],[f58,f97])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | v1_funct_1(X3)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f273,plain,
    ( spl6_18
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_13 ),
    inference(avatar_split_clause,[],[f272,f159,f90,f85,f80,f217])).

fof(f85,plain,
    ( spl6_3
  <=> v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f272,plain,
    ( ! [X1] :
        ( ~ r1_partfun1(X1,sK3)
        | r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | ~ v1_funct_1(X1) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_13 ),
    inference(subsumption_resolution,[],[f271,f92])).

fof(f271,plain,
    ( ! [X1] :
        ( ~ r1_partfun1(X1,sK3)
        | r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),X1))
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | ~ v1_funct_1(X1) )
    | ~ spl6_2
    | ~ spl6_3
    | spl6_13 ),
    inference(subsumption_resolution,[],[f270,f87])).

fof(f87,plain,
    ( v1_funct_2(sK3,sK0,k1_tarski(sK1))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f270,plain,
    ( ! [X1] :
        ( ~ r1_partfun1(X1,sK3)
        | r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),X1))
        | ~ v1_funct_2(sK3,sK0,k1_tarski(sK1))
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | ~ v1_funct_1(X1) )
    | ~ spl6_2
    | spl6_13 ),
    inference(subsumption_resolution,[],[f263,f160])).

fof(f263,plain,
    ( ! [X1] :
        ( k1_xboole_0 = k1_tarski(sK1)
        | ~ r1_partfun1(X1,sK3)
        | r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),X1))
        | ~ v1_funct_2(sK3,sK0,k1_tarski(sK1))
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | ~ v1_funct_1(X1) )
    | ~ spl6_2 ),
    inference(resolution,[],[f82,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r1_partfun1(X2,X3)
      | r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r1_partfun1(X2,X3)
           => ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
              | ( k1_xboole_0 != X0
                & k1_xboole_0 = X1 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_2)).

fof(f261,plain,(
    ~ spl6_13 ),
    inference(avatar_contradiction_clause,[],[f260])).

fof(f260,plain,
    ( $false
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f233,f64])).

fof(f233,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | ~ spl6_13 ),
    inference(superposition,[],[f108,f161])).

fof(f161,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f159])).

fof(f108,plain,(
    ! [X0] : ~ r1_tarski(k1_tarski(X0),X0) ),
    inference(resolution,[],[f104,f62])).

fof(f104,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(superposition,[],[f68,f57])).

fof(f57,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f68,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK4(X0,X1,X2) != X1
              & sK4(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sK4(X0,X1,X2) = X1
            | sK4(X0,X1,X2) = X0
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK4(X0,X1,X2) != X1
            & sK4(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sK4(X0,X1,X2) = X1
          | sK4(X0,X1,X2) = X0
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f162,plain,
    ( spl6_12
    | spl6_13
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f153,f90,f85,f80,f159,f155])).

fof(f153,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | v1_partfun1(sK3,sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f152,f92])).

fof(f152,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | v1_partfun1(sK3,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f150,f87])).

fof(f150,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | v1_partfun1(sK3,sK0)
    | ~ v1_funct_2(sK3,sK0,k1_tarski(sK1))
    | ~ v1_funct_1(sK3)
    | ~ spl6_2 ),
    inference(resolution,[],[f72,f82])).

fof(f103,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f38,f100])).

fof(f38,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    & v1_funct_2(sK3,sK0,k1_tarski(sK1))
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f29,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k1_tarski(X3) != k5_partfun1(sK0,k1_tarski(sK1),sK2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
          & v1_funct_2(X3,sK0,k1_tarski(sK1))
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X3] :
        ( k1_tarski(X3) != k5_partfun1(sK0,k1_tarski(sK1),sK2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        & v1_funct_2(X3,sK0,k1_tarski(sK1))
        & v1_funct_1(X3) )
   => ( k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      & v1_funct_2(sK3,sK0,k1_tarski(sK1))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
              & v1_funct_2(X3,X0,k1_tarski(X1))
              & v1_funct_1(X3) )
           => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
         => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_2)).

fof(f98,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f39,f95])).

fof(f39,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f30])).

fof(f93,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f40,f90])).

fof(f40,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f88,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f41,f85])).

fof(f41,plain,(
    v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f83,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f42,f80])).

fof(f42,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f30])).

fof(f78,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f43,f75])).

fof(f43,plain,(
    k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:26:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (23607)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.52  % (23626)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (23610)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.53  % (23609)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.53  % (23628)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.54  % (23602)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (23603)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (23624)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.54  % (23599)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (23601)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (23606)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.54  % (23629)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (23619)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.54  % (23616)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.54  % (23621)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.54  % (23605)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (23629)Refutation not found, incomplete strategy% (23629)------------------------------
% 0.22/0.54  % (23629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (23629)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (23629)Memory used [KB]: 1663
% 0.22/0.54  % (23629)Time elapsed: 0.003 s
% 0.22/0.54  % (23629)------------------------------
% 0.22/0.54  % (23629)------------------------------
% 0.22/0.54  % (23620)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.54  % (23612)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.54  % (23625)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.55  % (23623)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.55  % (23600)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.55  % (23627)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.55  % (23627)Refutation not found, incomplete strategy% (23627)------------------------------
% 0.22/0.55  % (23627)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (23627)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (23627)Memory used [KB]: 6140
% 0.22/0.55  % (23627)Time elapsed: 0.137 s
% 0.22/0.55  % (23627)------------------------------
% 0.22/0.55  % (23627)------------------------------
% 0.22/0.55  % (23604)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.55  % (23611)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.55  % (23617)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.55  % (23622)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.55  % (23618)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.56  % (23616)Refutation not found, incomplete strategy% (23616)------------------------------
% 0.22/0.56  % (23616)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (23616)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (23616)Memory used [KB]: 10746
% 0.22/0.56  % (23616)Time elapsed: 0.131 s
% 0.22/0.56  % (23616)------------------------------
% 0.22/0.56  % (23616)------------------------------
% 0.22/0.56  % (23614)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.56  % (23608)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.56  % (23615)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.70/0.59  % (23621)Refutation found. Thanks to Tanya!
% 1.70/0.59  % SZS status Theorem for theBenchmark
% 1.70/0.59  % SZS output start Proof for theBenchmark
% 1.70/0.59  fof(f677,plain,(
% 1.70/0.59    $false),
% 1.70/0.59    inference(avatar_sat_refutation,[],[f78,f83,f88,f93,f98,f103,f162,f261,f273,f296,f405,f416,f675,f676])).
% 1.70/0.59  fof(f676,plain,(
% 1.70/0.59    k1_xboole_0 != k5_partfun1(sK0,k1_tarski(sK1),sK2) | r2_hidden(sK3,k1_xboole_0) | ~r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK2))),
% 1.70/0.59    introduced(theory_tautology_sat_conflict,[])).
% 1.70/0.59  fof(f675,plain,(
% 1.70/0.59    spl6_1 | ~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_9 | ~spl6_10 | ~spl6_12 | spl6_13),
% 1.70/0.59    inference(avatar_contradiction_clause,[],[f674])).
% 1.70/0.59  fof(f674,plain,(
% 1.70/0.59    $false | (spl6_1 | ~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_9 | ~spl6_10 | ~spl6_12 | spl6_13)),
% 1.70/0.59    inference(subsumption_resolution,[],[f673,f77])).
% 1.70/0.59  fof(f77,plain,(
% 1.70/0.59    k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3) | spl6_1),
% 1.70/0.59    inference(avatar_component_clause,[],[f75])).
% 1.70/0.59  fof(f75,plain,(
% 1.70/0.59    spl6_1 <=> k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(sK3)),
% 1.70/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.70/0.59  fof(f673,plain,(
% 1.70/0.59    k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(sK3) | (~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_9 | ~spl6_10 | ~spl6_12 | spl6_13)),
% 1.70/0.59    inference(equality_resolution,[],[f671])).
% 1.70/0.59  fof(f671,plain,(
% 1.70/0.59    ( ! [X11] : (sK3 != X11 | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X11)) ) | (~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_9 | ~spl6_10 | ~spl6_12 | spl6_13)),
% 1.70/0.59    inference(subsumption_resolution,[],[f660,f132])).
% 1.70/0.59  fof(f132,plain,(
% 1.70/0.59    k1_xboole_0 != k5_partfun1(sK0,k1_tarski(sK1),sK2) | spl6_9),
% 1.70/0.59    inference(avatar_component_clause,[],[f131])).
% 1.70/0.59  fof(f131,plain,(
% 1.70/0.59    spl6_9 <=> k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)),
% 1.70/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.70/0.59  fof(f660,plain,(
% 1.70/0.59    ( ! [X11] : (sK3 != X11 | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X11)) ) | (~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_9 | ~spl6_10 | ~spl6_12 | spl6_13)),
% 1.70/0.59    inference(duplicate_literal_removal,[],[f657])).
% 1.70/0.59  fof(f657,plain,(
% 1.70/0.59    ( ! [X11] : (sK3 != X11 | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X11) | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X11)) ) | (~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_9 | ~spl6_10 | ~spl6_12 | spl6_13)),
% 1.70/0.59    inference(superposition,[],[f56,f641])).
% 1.70/0.59  fof(f641,plain,(
% 1.70/0.59    ( ! [X1] : (sK3 = sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X1) | k1_tarski(X1) = k5_partfun1(sK0,k1_tarski(sK1),sK2)) ) | (~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_9 | ~spl6_10 | ~spl6_12 | spl6_13)),
% 1.70/0.59    inference(subsumption_resolution,[],[f491,f502])).
% 1.70/0.59  fof(f502,plain,(
% 1.70/0.59    ( ! [X12] : (v1_partfun1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X12),sK0) | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X12)) ) | (~spl6_5 | ~spl6_6 | spl6_9 | ~spl6_10 | spl6_13)),
% 1.70/0.59    inference(subsumption_resolution,[],[f501,f315])).
% 1.70/0.59  fof(f315,plain,(
% 1.70/0.59    ( ! [X0] : (v1_funct_2(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0),sK0,k1_tarski(sK1)) | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2)) ) | (~spl6_5 | ~spl6_6 | spl6_9)),
% 1.70/0.59    inference(subsumption_resolution,[],[f313,f132])).
% 1.70/0.59  fof(f313,plain,(
% 1.70/0.59    ( ! [X0] : (v1_funct_2(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0),sK0,k1_tarski(sK1)) | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2)) ) | (~spl6_5 | ~spl6_6)),
% 1.70/0.59    inference(resolution,[],[f141,f55])).
% 1.70/0.59  fof(f55,plain,(
% 1.70/0.59    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 1.70/0.59    inference(cnf_transformation,[],[f37])).
% 1.70/0.59  fof(f37,plain,(
% 1.70/0.59    ! [X0,X1] : ((sK5(X0,X1) != X1 & r2_hidden(sK5(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 1.70/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f36])).
% 1.70/0.59  fof(f36,plain,(
% 1.70/0.59    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK5(X0,X1) != X1 & r2_hidden(sK5(X0,X1),X0)))),
% 1.70/0.59    introduced(choice_axiom,[])).
% 1.70/0.59  fof(f22,plain,(
% 1.70/0.59    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 1.70/0.59    inference(ennf_transformation,[],[f5])).
% 1.70/0.59  fof(f5,axiom,(
% 1.70/0.59    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 1.70/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).
% 1.70/0.59  fof(f141,plain,(
% 1.70/0.59    ( ! [X1] : (~r2_hidden(X1,k5_partfun1(sK0,k1_tarski(sK1),sK2)) | v1_funct_2(X1,sK0,k1_tarski(sK1))) ) | (~spl6_5 | ~spl6_6)),
% 1.70/0.59    inference(subsumption_resolution,[],[f139,f102])).
% 1.70/0.59  fof(f102,plain,(
% 1.70/0.59    v1_funct_1(sK2) | ~spl6_6),
% 1.70/0.59    inference(avatar_component_clause,[],[f100])).
% 1.70/0.59  fof(f100,plain,(
% 1.70/0.59    spl6_6 <=> v1_funct_1(sK2)),
% 1.70/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.70/0.59  fof(f139,plain,(
% 1.70/0.59    ( ! [X1] : (~r2_hidden(X1,k5_partfun1(sK0,k1_tarski(sK1),sK2)) | v1_funct_2(X1,sK0,k1_tarski(sK1)) | ~v1_funct_1(sK2)) ) | ~spl6_5),
% 1.70/0.59    inference(resolution,[],[f59,f97])).
% 1.70/0.59  fof(f97,plain,(
% 1.70/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~spl6_5),
% 1.70/0.59    inference(avatar_component_clause,[],[f95])).
% 1.70/0.59  fof(f95,plain,(
% 1.70/0.59    spl6_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 1.70/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.70/0.59  fof(f59,plain,(
% 1.70/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | v1_funct_2(X3,X0,X1) | ~v1_funct_1(X2)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f24])).
% 1.70/0.59  fof(f24,plain,(
% 1.70/0.59    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.70/0.59    inference(flattening,[],[f23])).
% 1.70/0.59  fof(f23,plain,(
% 1.70/0.59    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.70/0.59    inference(ennf_transformation,[],[f11])).
% 1.70/0.59  fof(f11,axiom,(
% 1.70/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (r2_hidden(X3,k5_partfun1(X0,X1,X2)) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))))),
% 1.70/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_2)).
% 1.70/0.59  fof(f501,plain,(
% 1.70/0.59    ( ! [X12] : (k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X12) | v1_partfun1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X12),sK0) | ~v1_funct_2(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X12),sK0,k1_tarski(sK1))) ) | (~spl6_5 | ~spl6_6 | spl6_9 | ~spl6_10 | spl6_13)),
% 1.70/0.59    inference(subsumption_resolution,[],[f500,f136])).
% 1.70/0.59  fof(f136,plain,(
% 1.70/0.59    ( ! [X0] : (v1_funct_1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0)) | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2)) ) | ~spl6_10),
% 1.70/0.59    inference(avatar_component_clause,[],[f135])).
% 1.70/0.59  fof(f135,plain,(
% 1.70/0.59    spl6_10 <=> ! [X0] : (v1_funct_1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0)) | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2))),
% 1.70/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.70/0.59  fof(f500,plain,(
% 1.70/0.59    ( ! [X12] : (k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X12) | v1_partfun1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X12),sK0) | ~v1_funct_2(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X12),sK0,k1_tarski(sK1)) | ~v1_funct_1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X12))) ) | (~spl6_5 | ~spl6_6 | spl6_9 | spl6_13)),
% 1.70/0.59    inference(subsumption_resolution,[],[f487,f160])).
% 1.70/0.59  fof(f160,plain,(
% 1.70/0.59    k1_xboole_0 != k1_tarski(sK1) | spl6_13),
% 1.70/0.59    inference(avatar_component_clause,[],[f159])).
% 1.70/0.59  fof(f159,plain,(
% 1.70/0.59    spl6_13 <=> k1_xboole_0 = k1_tarski(sK1)),
% 1.70/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 1.70/0.59  fof(f487,plain,(
% 1.70/0.59    ( ! [X12] : (k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X12) | k1_xboole_0 = k1_tarski(sK1) | v1_partfun1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X12),sK0) | ~v1_funct_2(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X12),sK0,k1_tarski(sK1)) | ~v1_funct_1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X12))) ) | (~spl6_5 | ~spl6_6 | spl6_9)),
% 1.70/0.59    inference(resolution,[],[f370,f72])).
% 1.70/0.59  fof(f72,plain,(
% 1.70/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.70/0.59    inference(duplicate_literal_removal,[],[f53])).
% 1.70/0.59  fof(f53,plain,(
% 1.70/0.59    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f21])).
% 1.70/0.59  fof(f21,plain,(
% 1.70/0.59    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.70/0.59    inference(flattening,[],[f20])).
% 1.70/0.59  fof(f20,plain,(
% 1.70/0.59    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.70/0.59    inference(ennf_transformation,[],[f7])).
% 1.70/0.59  fof(f7,axiom,(
% 1.70/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.70/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).
% 1.70/0.59  fof(f370,plain,(
% 1.70/0.59    ( ! [X0] : (m1_subset_1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2)) ) | (~spl6_5 | ~spl6_6 | spl6_9)),
% 1.70/0.59    inference(subsumption_resolution,[],[f368,f132])).
% 1.70/0.59  fof(f368,plain,(
% 1.70/0.59    ( ! [X0] : (m1_subset_1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2)) ) | (~spl6_5 | ~spl6_6)),
% 1.70/0.59    inference(resolution,[],[f176,f55])).
% 1.70/0.59  fof(f176,plain,(
% 1.70/0.59    ( ! [X1] : (~r2_hidden(X1,k5_partfun1(sK0,k1_tarski(sK1),sK2)) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))) ) | (~spl6_5 | ~spl6_6)),
% 1.70/0.59    inference(subsumption_resolution,[],[f174,f102])).
% 1.70/0.59  fof(f174,plain,(
% 1.70/0.59    ( ! [X1] : (~r2_hidden(X1,k5_partfun1(sK0,k1_tarski(sK1),sK2)) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~v1_funct_1(sK2)) ) | ~spl6_5),
% 1.70/0.59    inference(resolution,[],[f60,f97])).
% 1.70/0.59  fof(f60,plain,(
% 1.70/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f24])).
% 1.70/0.59  fof(f491,plain,(
% 1.70/0.59    ( ! [X1] : (k1_tarski(X1) = k5_partfun1(sK0,k1_tarski(sK1),sK2) | sK3 = sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X1) | ~v1_partfun1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X1),sK0)) ) | (~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_9 | ~spl6_10 | ~spl6_12)),
% 1.70/0.59    inference(subsumption_resolution,[],[f480,f136])).
% 1.70/0.59  fof(f480,plain,(
% 1.70/0.59    ( ! [X1] : (k1_tarski(X1) = k5_partfun1(sK0,k1_tarski(sK1),sK2) | sK3 = sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X1) | ~v1_partfun1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X1),sK0) | ~v1_funct_1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X1))) ) | (~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_9 | ~spl6_12)),
% 1.70/0.59    inference(resolution,[],[f370,f376])).
% 1.70/0.59  fof(f376,plain,(
% 1.70/0.59    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | sK3 = X0 | ~v1_partfun1(X0,sK0) | ~v1_funct_1(X0)) ) | (~spl6_2 | ~spl6_4 | ~spl6_12)),
% 1.70/0.59    inference(subsumption_resolution,[],[f189,f180])).
% 1.70/0.59  fof(f180,plain,(
% 1.70/0.59    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | r1_partfun1(X0,sK3) | ~v1_funct_1(X0)) ) | (~spl6_2 | ~spl6_4)),
% 1.70/0.59    inference(subsumption_resolution,[],[f178,f92])).
% 1.70/0.59  fof(f92,plain,(
% 1.70/0.59    v1_funct_1(sK3) | ~spl6_4),
% 1.70/0.59    inference(avatar_component_clause,[],[f90])).
% 1.70/0.59  fof(f90,plain,(
% 1.70/0.59    spl6_4 <=> v1_funct_1(sK3)),
% 1.70/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.70/0.59  fof(f178,plain,(
% 1.70/0.59    ( ! [X0] : (r1_partfun1(X0,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~v1_funct_1(X0)) ) | ~spl6_2),
% 1.70/0.59    inference(resolution,[],[f61,f82])).
% 1.70/0.59  fof(f82,plain,(
% 1.70/0.59    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~spl6_2),
% 1.70/0.59    inference(avatar_component_clause,[],[f80])).
% 1.70/0.59  fof(f80,plain,(
% 1.70/0.59    spl6_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 1.70/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.70/0.59  fof(f61,plain,(
% 1.70/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | r1_partfun1(X2,X3) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f26])).
% 1.70/0.59  fof(f26,plain,(
% 1.70/0.59    ! [X0,X1,X2] : (! [X3] : (r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2))),
% 1.70/0.59    inference(flattening,[],[f25])).
% 1.70/0.59  fof(f25,plain,(
% 1.70/0.59    ! [X0,X1,X2] : (! [X3] : (r1_partfun1(X2,X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2)))),
% 1.70/0.59    inference(ennf_transformation,[],[f8])).
% 1.70/0.59  fof(f8,axiom,(
% 1.70/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X3)) => r1_partfun1(X2,X3)))),
% 1.70/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_partfun1)).
% 1.70/0.59  fof(f189,plain,(
% 1.70/0.59    ( ! [X0] : (~r1_partfun1(X0,sK3) | ~v1_partfun1(X0,sK0) | sK3 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~v1_funct_1(X0)) ) | (~spl6_2 | ~spl6_4 | ~spl6_12)),
% 1.70/0.59    inference(subsumption_resolution,[],[f188,f92])).
% 1.70/0.59  fof(f188,plain,(
% 1.70/0.59    ( ! [X0] : (~r1_partfun1(X0,sK3) | ~v1_partfun1(X0,sK0) | sK3 = X0 | ~v1_funct_1(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~v1_funct_1(X0)) ) | (~spl6_2 | ~spl6_12)),
% 1.70/0.59    inference(subsumption_resolution,[],[f186,f157])).
% 1.70/0.59  fof(f157,plain,(
% 1.70/0.59    v1_partfun1(sK3,sK0) | ~spl6_12),
% 1.70/0.59    inference(avatar_component_clause,[],[f155])).
% 1.70/0.59  fof(f155,plain,(
% 1.70/0.59    spl6_12 <=> v1_partfun1(sK3,sK0)),
% 1.70/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 1.70/0.59  fof(f186,plain,(
% 1.70/0.59    ( ! [X0] : (~r1_partfun1(X0,sK3) | ~v1_partfun1(sK3,sK0) | ~v1_partfun1(X0,sK0) | sK3 = X0 | ~v1_funct_1(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~v1_funct_1(X0)) ) | ~spl6_2),
% 1.70/0.59    inference(resolution,[],[f50,f82])).
% 1.70/0.59  fof(f50,plain,(
% 1.70/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | X2 = X3 | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f17])).
% 1.70/0.59  fof(f17,plain,(
% 1.70/0.59    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.70/0.59    inference(flattening,[],[f16])).
% 1.70/0.59  fof(f16,plain,(
% 1.70/0.59    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.70/0.59    inference(ennf_transformation,[],[f9])).
% 1.70/0.59  fof(f9,axiom,(
% 1.70/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 1.70/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).
% 1.70/0.59  fof(f56,plain,(
% 1.70/0.59    ( ! [X0,X1] : (sK5(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 1.70/0.59    inference(cnf_transformation,[],[f37])).
% 1.70/0.59  fof(f416,plain,(
% 1.70/0.59    ~spl6_31),
% 1.70/0.59    inference(avatar_contradiction_clause,[],[f415])).
% 1.70/0.59  fof(f415,plain,(
% 1.70/0.59    $false | ~spl6_31),
% 1.70/0.59    inference(subsumption_resolution,[],[f413,f64])).
% 1.70/0.59  fof(f64,plain,(
% 1.70/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f1])).
% 1.70/0.59  fof(f1,axiom,(
% 1.70/0.59    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.70/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.70/0.59  fof(f413,plain,(
% 1.70/0.59    ~r1_tarski(k1_xboole_0,sK3) | ~spl6_31),
% 1.70/0.59    inference(resolution,[],[f398,f62])).
% 1.70/0.59  fof(f62,plain,(
% 1.70/0.59    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f27])).
% 1.70/0.59  fof(f27,plain,(
% 1.70/0.59    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.70/0.59    inference(ennf_transformation,[],[f6])).
% 1.70/0.59  fof(f6,axiom,(
% 1.70/0.59    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.70/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.70/0.59  fof(f398,plain,(
% 1.70/0.59    r2_hidden(sK3,k1_xboole_0) | ~spl6_31),
% 1.70/0.59    inference(avatar_component_clause,[],[f396])).
% 1.70/0.59  fof(f396,plain,(
% 1.70/0.59    spl6_31 <=> r2_hidden(sK3,k1_xboole_0)),
% 1.70/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 1.70/0.59  fof(f405,plain,(
% 1.70/0.59    spl6_32 | ~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_18),
% 1.70/0.59    inference(avatar_split_clause,[],[f400,f217,f100,f95,f90,f80,f402])).
% 1.70/0.59  fof(f402,plain,(
% 1.70/0.59    spl6_32 <=> r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK2))),
% 1.70/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 1.70/0.59  fof(f217,plain,(
% 1.70/0.59    spl6_18 <=> ! [X0] : (~r1_partfun1(X0,sK3) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),X0)))),
% 1.70/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 1.70/0.59  fof(f400,plain,(
% 1.70/0.59    r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK2)) | (~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_18)),
% 1.70/0.59    inference(subsumption_resolution,[],[f391,f102])).
% 1.70/0.59  fof(f391,plain,(
% 1.70/0.59    ~v1_funct_1(sK2) | r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK2)) | (~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_18)),
% 1.70/0.59    inference(resolution,[],[f386,f97])).
% 1.70/0.59  fof(f386,plain,(
% 1.70/0.59    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~v1_funct_1(X0) | r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),X0))) ) | (~spl6_2 | ~spl6_4 | ~spl6_18)),
% 1.70/0.59    inference(subsumption_resolution,[],[f218,f180])).
% 1.70/0.59  fof(f218,plain,(
% 1.70/0.59    ( ! [X0] : (~r1_partfun1(X0,sK3) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),X0))) ) | ~spl6_18),
% 1.70/0.59    inference(avatar_component_clause,[],[f217])).
% 1.70/0.59  fof(f296,plain,(
% 1.70/0.59    spl6_10 | ~spl6_5 | ~spl6_6 | spl6_9),
% 1.70/0.59    inference(avatar_split_clause,[],[f295,f131,f100,f95,f135])).
% 1.70/0.59  fof(f295,plain,(
% 1.70/0.59    ( ! [X0] : (v1_funct_1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0)) | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2)) ) | (~spl6_5 | ~spl6_6 | spl6_9)),
% 1.70/0.59    inference(subsumption_resolution,[],[f293,f132])).
% 1.70/0.59  fof(f293,plain,(
% 1.70/0.59    ( ! [X0] : (v1_funct_1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0)) | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2)) ) | (~spl6_5 | ~spl6_6)),
% 1.70/0.59    inference(resolution,[],[f119,f55])).
% 1.70/0.59  fof(f119,plain,(
% 1.70/0.59    ( ! [X1] : (~r2_hidden(X1,k5_partfun1(sK0,k1_tarski(sK1),sK2)) | v1_funct_1(X1)) ) | (~spl6_5 | ~spl6_6)),
% 1.70/0.59    inference(subsumption_resolution,[],[f117,f102])).
% 1.70/0.59  fof(f117,plain,(
% 1.70/0.59    ( ! [X1] : (~r2_hidden(X1,k5_partfun1(sK0,k1_tarski(sK1),sK2)) | v1_funct_1(X1) | ~v1_funct_1(sK2)) ) | ~spl6_5),
% 1.70/0.59    inference(resolution,[],[f58,f97])).
% 1.70/0.59  fof(f58,plain,(
% 1.70/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | v1_funct_1(X3) | ~v1_funct_1(X2)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f24])).
% 1.70/0.59  fof(f273,plain,(
% 1.70/0.59    spl6_18 | ~spl6_2 | ~spl6_3 | ~spl6_4 | spl6_13),
% 1.70/0.59    inference(avatar_split_clause,[],[f272,f159,f90,f85,f80,f217])).
% 1.70/0.59  fof(f85,plain,(
% 1.70/0.59    spl6_3 <=> v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 1.70/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.70/0.59  fof(f272,plain,(
% 1.70/0.59    ( ! [X1] : (~r1_partfun1(X1,sK3) | r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~v1_funct_1(X1)) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | spl6_13)),
% 1.70/0.59    inference(subsumption_resolution,[],[f271,f92])).
% 1.70/0.59  fof(f271,plain,(
% 1.70/0.59    ( ! [X1] : (~r1_partfun1(X1,sK3) | r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),X1)) | ~v1_funct_1(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~v1_funct_1(X1)) ) | (~spl6_2 | ~spl6_3 | spl6_13)),
% 1.70/0.59    inference(subsumption_resolution,[],[f270,f87])).
% 1.70/0.59  fof(f87,plain,(
% 1.70/0.59    v1_funct_2(sK3,sK0,k1_tarski(sK1)) | ~spl6_3),
% 1.70/0.59    inference(avatar_component_clause,[],[f85])).
% 1.70/0.59  fof(f270,plain,(
% 1.70/0.59    ( ! [X1] : (~r1_partfun1(X1,sK3) | r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),X1)) | ~v1_funct_2(sK3,sK0,k1_tarski(sK1)) | ~v1_funct_1(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~v1_funct_1(X1)) ) | (~spl6_2 | spl6_13)),
% 1.70/0.59    inference(subsumption_resolution,[],[f263,f160])).
% 1.70/0.59  fof(f263,plain,(
% 1.70/0.59    ( ! [X1] : (k1_xboole_0 = k1_tarski(sK1) | ~r1_partfun1(X1,sK3) | r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),X1)) | ~v1_funct_2(sK3,sK0,k1_tarski(sK1)) | ~v1_funct_1(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~v1_funct_1(X1)) ) | ~spl6_2),
% 1.70/0.59    inference(resolution,[],[f82,f51])).
% 1.70/0.59  fof(f51,plain,(
% 1.70/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r1_partfun1(X2,X3) | r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f19])).
% 1.70/0.59  fof(f19,plain,(
% 1.70/0.59    ! [X0,X1,X2] : (! [X3] : (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.70/0.59    inference(flattening,[],[f18])).
% 1.70/0.59  fof(f18,plain,(
% 1.70/0.59    ! [X0,X1,X2] : (! [X3] : (((r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_partfun1(X2,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.70/0.59    inference(ennf_transformation,[],[f10])).
% 1.70/0.59  fof(f10,axiom,(
% 1.70/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 1.70/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_2)).
% 1.70/0.59  fof(f261,plain,(
% 1.70/0.59    ~spl6_13),
% 1.70/0.59    inference(avatar_contradiction_clause,[],[f260])).
% 1.70/0.59  fof(f260,plain,(
% 1.70/0.59    $false | ~spl6_13),
% 1.70/0.59    inference(subsumption_resolution,[],[f233,f64])).
% 1.70/0.59  fof(f233,plain,(
% 1.70/0.59    ~r1_tarski(k1_xboole_0,sK1) | ~spl6_13),
% 1.70/0.59    inference(superposition,[],[f108,f161])).
% 1.70/0.59  fof(f161,plain,(
% 1.70/0.59    k1_xboole_0 = k1_tarski(sK1) | ~spl6_13),
% 1.70/0.59    inference(avatar_component_clause,[],[f159])).
% 1.70/0.59  fof(f108,plain,(
% 1.70/0.59    ( ! [X0] : (~r1_tarski(k1_tarski(X0),X0)) )),
% 1.70/0.59    inference(resolution,[],[f104,f62])).
% 1.70/0.59  fof(f104,plain,(
% 1.70/0.59    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 1.70/0.59    inference(superposition,[],[f68,f57])).
% 1.70/0.59  fof(f57,plain,(
% 1.70/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f3])).
% 1.70/0.59  fof(f3,axiom,(
% 1.70/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.70/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.70/0.59  fof(f68,plain,(
% 1.70/0.59    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 1.70/0.59    inference(equality_resolution,[],[f67])).
% 1.70/0.59  fof(f67,plain,(
% 1.70/0.59    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 1.70/0.59    inference(equality_resolution,[],[f45])).
% 1.70/0.59  fof(f45,plain,(
% 1.70/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 1.70/0.59    inference(cnf_transformation,[],[f35])).
% 1.70/0.59  fof(f35,plain,(
% 1.70/0.59    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.70/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).
% 1.70/0.59  fof(f34,plain,(
% 1.70/0.59    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.70/0.59    introduced(choice_axiom,[])).
% 1.70/0.59  fof(f33,plain,(
% 1.70/0.59    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.70/0.59    inference(rectify,[],[f32])).
% 1.70/0.59  fof(f32,plain,(
% 1.70/0.59    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.70/0.59    inference(flattening,[],[f31])).
% 1.70/0.59  fof(f31,plain,(
% 1.70/0.59    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.70/0.59    inference(nnf_transformation,[],[f2])).
% 1.70/0.59  fof(f2,axiom,(
% 1.70/0.59    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.70/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 1.70/0.59  fof(f162,plain,(
% 1.70/0.59    spl6_12 | spl6_13 | ~spl6_2 | ~spl6_3 | ~spl6_4),
% 1.70/0.59    inference(avatar_split_clause,[],[f153,f90,f85,f80,f159,f155])).
% 1.70/0.59  fof(f153,plain,(
% 1.70/0.59    k1_xboole_0 = k1_tarski(sK1) | v1_partfun1(sK3,sK0) | (~spl6_2 | ~spl6_3 | ~spl6_4)),
% 1.70/0.59    inference(subsumption_resolution,[],[f152,f92])).
% 1.70/0.59  fof(f152,plain,(
% 1.70/0.59    k1_xboole_0 = k1_tarski(sK1) | v1_partfun1(sK3,sK0) | ~v1_funct_1(sK3) | (~spl6_2 | ~spl6_3)),
% 1.70/0.59    inference(subsumption_resolution,[],[f150,f87])).
% 1.70/0.59  fof(f150,plain,(
% 1.70/0.59    k1_xboole_0 = k1_tarski(sK1) | v1_partfun1(sK3,sK0) | ~v1_funct_2(sK3,sK0,k1_tarski(sK1)) | ~v1_funct_1(sK3) | ~spl6_2),
% 1.70/0.59    inference(resolution,[],[f72,f82])).
% 1.70/0.59  fof(f103,plain,(
% 1.70/0.59    spl6_6),
% 1.70/0.59    inference(avatar_split_clause,[],[f38,f100])).
% 1.70/0.59  fof(f38,plain,(
% 1.70/0.59    v1_funct_1(sK2)),
% 1.70/0.59    inference(cnf_transformation,[],[f30])).
% 1.70/0.59  fof(f30,plain,(
% 1.70/0.59    (k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_1(sK2)),
% 1.70/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f29,f28])).
% 1.70/0.59  fof(f28,plain,(
% 1.70/0.59    ? [X0,X1,X2] : (? [X3] : (k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => (? [X3] : (k1_tarski(X3) != k5_partfun1(sK0,k1_tarski(sK1),sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(X3,sK0,k1_tarski(sK1)) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_1(sK2))),
% 1.70/0.59    introduced(choice_axiom,[])).
% 1.70/0.59  fof(f29,plain,(
% 1.70/0.59    ? [X3] : (k1_tarski(X3) != k5_partfun1(sK0,k1_tarski(sK1),sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(X3,sK0,k1_tarski(sK1)) & v1_funct_1(X3)) => (k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3))),
% 1.70/0.59    introduced(choice_axiom,[])).
% 1.70/0.59  fof(f15,plain,(
% 1.70/0.59    ? [X0,X1,X2] : (? [X3] : (k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2))),
% 1.70/0.59    inference(flattening,[],[f14])).
% 1.70/0.59  fof(f14,plain,(
% 1.70/0.59    ? [X0,X1,X2] : (? [X3] : (k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)))),
% 1.70/0.59    inference(ennf_transformation,[],[f13])).
% 1.70/0.59  fof(f13,negated_conjecture,(
% 1.70/0.59    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3)))),
% 1.70/0.59    inference(negated_conjecture,[],[f12])).
% 1.70/0.59  fof(f12,conjecture,(
% 1.70/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3)))),
% 1.70/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_2)).
% 1.70/0.59  fof(f98,plain,(
% 1.70/0.59    spl6_5),
% 1.70/0.59    inference(avatar_split_clause,[],[f39,f95])).
% 1.70/0.59  fof(f39,plain,(
% 1.70/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 1.70/0.59    inference(cnf_transformation,[],[f30])).
% 1.70/0.59  fof(f93,plain,(
% 1.70/0.59    spl6_4),
% 1.70/0.59    inference(avatar_split_clause,[],[f40,f90])).
% 1.70/0.59  fof(f40,plain,(
% 1.70/0.59    v1_funct_1(sK3)),
% 1.70/0.59    inference(cnf_transformation,[],[f30])).
% 1.70/0.59  fof(f88,plain,(
% 1.70/0.59    spl6_3),
% 1.70/0.59    inference(avatar_split_clause,[],[f41,f85])).
% 1.70/0.59  fof(f41,plain,(
% 1.70/0.59    v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 1.70/0.59    inference(cnf_transformation,[],[f30])).
% 1.70/0.59  fof(f83,plain,(
% 1.70/0.59    spl6_2),
% 1.70/0.59    inference(avatar_split_clause,[],[f42,f80])).
% 1.70/0.59  fof(f42,plain,(
% 1.70/0.59    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 1.70/0.59    inference(cnf_transformation,[],[f30])).
% 1.70/0.59  fof(f78,plain,(
% 1.70/0.59    ~spl6_1),
% 1.70/0.59    inference(avatar_split_clause,[],[f43,f75])).
% 1.70/0.59  fof(f43,plain,(
% 1.70/0.59    k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3)),
% 1.70/0.59    inference(cnf_transformation,[],[f30])).
% 1.70/0.59  % SZS output end Proof for theBenchmark
% 1.70/0.59  % (23621)------------------------------
% 1.70/0.59  % (23621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.59  % (23621)Termination reason: Refutation
% 1.70/0.59  
% 1.70/0.59  % (23621)Memory used [KB]: 6652
% 1.70/0.59  % (23621)Time elapsed: 0.153 s
% 1.70/0.59  % (23621)------------------------------
% 1.70/0.59  % (23621)------------------------------
% 1.70/0.60  % (23598)Success in time 0.233 s
%------------------------------------------------------------------------------
