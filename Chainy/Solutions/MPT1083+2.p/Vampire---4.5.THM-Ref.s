%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1083+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:05 EST 2020

% Result     : Theorem 18.22s
% Output     : Refutation 18.49s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 147 expanded)
%              Number of leaves         :   24 (  68 expanded)
%              Depth                    :    7
%              Number of atoms          :  264 ( 776 expanded)
%              Number of equality atoms :   28 (  96 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (7368)Time limit reached!
% (7368)------------------------------
% (7368)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (7368)Termination reason: Time limit

% (7368)Memory used [KB]: 18933
% (7368)Time elapsed: 0.619 s
% (7368)------------------------------
% (7368)------------------------------
fof(f36927,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f4630,f4638,f4642,f4646,f4650,f4654,f4658,f12123,f12653,f12663,f12776,f13214,f36895,f36926])).

fof(f36926,plain,
    ( sK2 != k1_relat_1(sK3)
    | ~ r1_tarski(k2_relat_1(sK4),sK2)
    | r1_tarski(k2_relat_1(sK4),k1_relat_1(sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f36895,plain,
    ( ~ spl247_815
    | ~ spl247_1371
    | spl247_5294
    | ~ spl247_1328 ),
    inference(avatar_split_clause,[],[f36882,f12236,f36893,f12651,f9836])).

fof(f9836,plain,
    ( spl247_815
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl247_815])])).

fof(f12651,plain,
    ( spl247_1371
  <=> v4_relat_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl247_1371])])).

fof(f36893,plain,
    ( spl247_5294
  <=> sK2 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl247_5294])])).

fof(f12236,plain,
    ( spl247_1328
  <=> v1_partfun1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl247_1328])])).

fof(f36882,plain,
    ( sK2 = k1_relat_1(sK3)
    | ~ v4_relat_1(sK3,sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl247_1328 ),
    inference(resolution,[],[f12237,f4023])).

fof(f4023,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2946])).

fof(f2946,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f2334])).

fof(f2334,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f2333])).

fof(f2333,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1487])).

fof(f1487,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f12237,plain,
    ( v1_partfun1(sK3,sK2)
    | ~ spl247_1328 ),
    inference(avatar_component_clause,[],[f12236])).

fof(f13214,plain,
    ( ~ spl247_4
    | ~ spl247_815
    | ~ spl247_1493
    | spl247_1 ),
    inference(avatar_split_clause,[],[f13169,f4628,f13212,f9836,f4640])).

fof(f4640,plain,
    ( spl247_4
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl247_4])])).

fof(f13212,plain,
    ( spl247_1493
  <=> r1_tarski(k2_relat_1(sK4),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl247_1493])])).

fof(f4628,plain,
    ( spl247_1
  <=> k1_relat_1(sK4) = k1_relat_1(k5_relat_1(sK4,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl247_1])])).

fof(f13169,plain,
    ( ~ r1_tarski(k2_relat_1(sK4),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK4)
    | spl247_1 ),
    inference(trivial_inequality_removal,[],[f13162])).

fof(f13162,plain,
    ( k1_relat_1(sK4) != k1_relat_1(sK4)
    | ~ r1_tarski(k2_relat_1(sK4),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK4)
    | spl247_1 ),
    inference(superposition,[],[f4629,f3133])).

fof(f3133,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1791])).

fof(f1791,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1790])).

fof(f1790,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f845])).

fof(f845,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

fof(f4629,plain,
    ( k1_relat_1(sK4) != k1_relat_1(k5_relat_1(sK4,sK3))
    | spl247_1 ),
    inference(avatar_component_clause,[],[f4628])).

fof(f12776,plain,
    ( spl247_8
    | ~ spl247_7
    | ~ spl247_6
    | spl247_1328
    | ~ spl247_5 ),
    inference(avatar_split_clause,[],[f12483,f4644,f12236,f4648,f4652,f4656])).

fof(f4656,plain,
    ( spl247_8
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl247_8])])).

fof(f4652,plain,
    ( spl247_7
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl247_7])])).

fof(f4648,plain,
    ( spl247_6
  <=> v1_funct_2(sK3,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl247_6])])).

fof(f4644,plain,
    ( spl247_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl247_5])])).

fof(f12483,plain,
    ( v1_partfun1(sK3,sK2)
    | ~ v1_funct_2(sK3,sK2,sK2)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK2)
    | ~ spl247_5 ),
    inference(resolution,[],[f4645,f4265])).

fof(f4265,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f2500])).

fof(f2500,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f2499])).

fof(f2499,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f1475])).

fof(f1475,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f4645,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ spl247_5 ),
    inference(avatar_component_clause,[],[f4644])).

fof(f12663,plain,
    ( spl247_815
    | ~ spl247_5 ),
    inference(avatar_split_clause,[],[f12441,f4644,f9836])).

fof(f12441,plain,
    ( v1_relat_1(sK3)
    | ~ spl247_5 ),
    inference(resolution,[],[f4645,f3215])).

fof(f3215,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1845])).

fof(f1845,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1210])).

fof(f1210,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f12653,plain,
    ( spl247_1371
    | ~ spl247_5 ),
    inference(avatar_split_clause,[],[f12438,f4644,f12651])).

fof(f12438,plain,
    ( v4_relat_1(sK3,sK2)
    | ~ spl247_5 ),
    inference(resolution,[],[f4645,f3164])).

fof(f3164,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1824])).

fof(f1824,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1211])).

fof(f1211,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f12123,plain,
    ( ~ spl247_4
    | spl247_1315
    | ~ spl247_3 ),
    inference(avatar_split_clause,[],[f12072,f4636,f12121,f4640])).

fof(f12121,plain,
    ( spl247_1315
  <=> r1_tarski(k2_relat_1(sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl247_1315])])).

fof(f4636,plain,
    ( spl247_3
  <=> v5_relat_1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl247_3])])).

fof(f12072,plain,
    ( r1_tarski(k2_relat_1(sK4),sK2)
    | ~ v1_relat_1(sK4)
    | ~ spl247_3 ),
    inference(resolution,[],[f4637,f3199])).

fof(f3199,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2623])).

fof(f2623,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f1835])).

fof(f1835,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f652])).

fof(f652,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f4637,plain,
    ( v5_relat_1(sK4,sK2)
    | ~ spl247_3 ),
    inference(avatar_component_clause,[],[f4636])).

fof(f4658,plain,(
    ~ spl247_8 ),
    inference(avatar_split_clause,[],[f3048,f4656])).

fof(f3048,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f2584])).

fof(f2584,plain,
    ( k1_relat_1(sK4) != k1_relat_1(k5_relat_1(sK4,sK3))
    & v1_funct_1(sK4)
    & v5_relat_1(sK4,sK2)
    & v1_relat_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v1_funct_2(sK3,sK2,sK2)
    & v1_funct_1(sK3)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f1719,f2583,f2582,f2581])).

fof(f2581,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1))
                & v1_funct_1(X2)
                & v5_relat_1(X2,X0)
                & v1_relat_1(X2) )
            & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X1,X0,X0)
            & v1_funct_1(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1))
              & v1_funct_1(X2)
              & v5_relat_1(X2,sK2)
              & v1_relat_1(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
          & v1_funct_2(X1,sK2,sK2)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f2582,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1))
            & v1_funct_1(X2)
            & v5_relat_1(X2,sK2)
            & v1_relat_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
        & v1_funct_2(X1,sK2,sK2)
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,sK3))
          & v1_funct_1(X2)
          & v5_relat_1(X2,sK2)
          & v1_relat_1(X2) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      & v1_funct_2(sK3,sK2,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f2583,plain,
    ( ? [X2] :
        ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,sK3))
        & v1_funct_1(X2)
        & v5_relat_1(X2,sK2)
        & v1_relat_1(X2) )
   => ( k1_relat_1(sK4) != k1_relat_1(k5_relat_1(sK4,sK3))
      & v1_funct_1(sK4)
      & v5_relat_1(sK4,sK2)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f1719,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1))
              & v1_funct_1(X2)
              & v5_relat_1(X2,X0)
              & v1_relat_1(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f1718])).

fof(f1718,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1))
              & v1_funct_1(X2)
              & v5_relat_1(X2,X0)
              & v1_relat_1(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1646])).

fof(f1646,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X1,X0,X0)
              & v1_funct_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v5_relat_1(X2,X0)
                  & v1_relat_1(X2) )
               => k1_relat_1(X2) = k1_relat_1(k5_relat_1(X2,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f1645])).

fof(f1645,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X1,X0,X0)
            & v1_funct_1(X1) )
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v5_relat_1(X2,X0)
                & v1_relat_1(X2) )
             => k1_relat_1(X2) = k1_relat_1(k5_relat_1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t200_funct_2)).

fof(f4654,plain,(
    spl247_7 ),
    inference(avatar_split_clause,[],[f3049,f4652])).

fof(f3049,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f2584])).

fof(f4650,plain,(
    spl247_6 ),
    inference(avatar_split_clause,[],[f3050,f4648])).

fof(f3050,plain,(
    v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f2584])).

fof(f4646,plain,(
    spl247_5 ),
    inference(avatar_split_clause,[],[f3051,f4644])).

fof(f3051,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f2584])).

fof(f4642,plain,(
    spl247_4 ),
    inference(avatar_split_clause,[],[f3052,f4640])).

fof(f3052,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f2584])).

fof(f4638,plain,(
    spl247_3 ),
    inference(avatar_split_clause,[],[f3053,f4636])).

fof(f3053,plain,(
    v5_relat_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f2584])).

fof(f4630,plain,(
    ~ spl247_1 ),
    inference(avatar_split_clause,[],[f3055,f4628])).

fof(f3055,plain,(
    k1_relat_1(sK4) != k1_relat_1(k5_relat_1(sK4,sK3)) ),
    inference(cnf_transformation,[],[f2584])).
%------------------------------------------------------------------------------
