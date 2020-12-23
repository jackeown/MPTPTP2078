%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1034+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:04 EST 2020

% Result     : Theorem 1.68s
% Output     : Refutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 134 expanded)
%              Number of leaves         :   16 (  52 expanded)
%              Depth                    :    9
%              Number of atoms          :  266 ( 772 expanded)
%              Number of equality atoms :   32 (  32 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3429,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3140,f3145,f3150,f3155,f3160,f3170,f3190,f3195,f3428])).

fof(f3428,plain,
    ( ~ spl183_1
    | ~ spl183_2
    | ~ spl183_3
    | ~ spl183_4
    | ~ spl183_5
    | spl183_7
    | ~ spl183_11
    | ~ spl183_12 ),
    inference(avatar_contradiction_clause,[],[f3427])).

fof(f3427,plain,
    ( $false
    | ~ spl183_1
    | ~ spl183_2
    | ~ spl183_3
    | ~ spl183_4
    | ~ spl183_5
    | spl183_7
    | ~ spl183_11
    | ~ spl183_12 ),
    inference(subsumption_resolution,[],[f3413,f3211])).

fof(f3211,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f2343,f2923])).

fof(f2923,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f2337])).

fof(f2337,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f2038])).

fof(f2038,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f2037])).

fof(f2037,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f329])).

fof(f329,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f2343,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f369])).

fof(f369,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f3413,plain,
    ( r2_hidden(sK5(k1_xboole_0,sK3,sK4),k1_xboole_0)
    | ~ spl183_1
    | ~ spl183_2
    | ~ spl183_3
    | ~ spl183_4
    | ~ spl183_5
    | spl183_7
    | ~ spl183_11
    | ~ spl183_12 ),
    inference(backward_demodulation,[],[f3383,f3385])).

fof(f3385,plain,
    ( k1_xboole_0 = sK2
    | ~ spl183_1
    | ~ spl183_2
    | ~ spl183_3
    | ~ spl183_4
    | ~ spl183_5
    | spl183_7
    | ~ spl183_11
    | ~ spl183_12 ),
    inference(unit_resulting_resolution,[],[f3139,f3144,f3149,f3154,f3159,f3169,f3189,f3194,f2294])).

fof(f2294,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_partfun1(X2,X3)
      | k1_xboole_0 = X1
      | r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f1626])).

fof(f1626,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f1625])).

fof(f1625,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1532])).

fof(f1532,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r1_partfun1(X2,X3)
           => ( r2_relset_1(X0,X1,X2,X3)
              | ( k1_xboole_0 != X0
                & k1_xboole_0 = X1 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_2)).

fof(f3194,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ spl183_12 ),
    inference(avatar_component_clause,[],[f3192])).

fof(f3192,plain,
    ( spl183_12
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl183_12])])).

fof(f3189,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ spl183_11 ),
    inference(avatar_component_clause,[],[f3187])).

fof(f3187,plain,
    ( spl183_11
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl183_11])])).

fof(f3169,plain,
    ( ~ r2_relset_1(sK2,sK2,sK3,sK4)
    | spl183_7 ),
    inference(avatar_component_clause,[],[f3167])).

fof(f3167,plain,
    ( spl183_7
  <=> r2_relset_1(sK2,sK2,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl183_7])])).

fof(f3159,plain,
    ( v1_funct_2(sK4,sK2,sK2)
    | ~ spl183_5 ),
    inference(avatar_component_clause,[],[f3157])).

fof(f3157,plain,
    ( spl183_5
  <=> v1_funct_2(sK4,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl183_5])])).

fof(f3154,plain,
    ( v1_funct_2(sK3,sK2,sK2)
    | ~ spl183_4 ),
    inference(avatar_component_clause,[],[f3152])).

fof(f3152,plain,
    ( spl183_4
  <=> v1_funct_2(sK3,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl183_4])])).

fof(f3149,plain,
    ( r1_partfun1(sK3,sK4)
    | ~ spl183_3 ),
    inference(avatar_component_clause,[],[f3147])).

fof(f3147,plain,
    ( spl183_3
  <=> r1_partfun1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl183_3])])).

fof(f3144,plain,
    ( v1_funct_1(sK4)
    | ~ spl183_2 ),
    inference(avatar_component_clause,[],[f3142])).

fof(f3142,plain,
    ( spl183_2
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl183_2])])).

fof(f3139,plain,
    ( v1_funct_1(sK3)
    | ~ spl183_1 ),
    inference(avatar_component_clause,[],[f3137])).

fof(f3137,plain,
    ( spl183_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl183_1])])).

fof(f3383,plain,
    ( r2_hidden(sK5(sK2,sK3,sK4),sK2)
    | ~ spl183_1
    | ~ spl183_2
    | ~ spl183_4
    | ~ spl183_5
    | spl183_7
    | ~ spl183_11
    | ~ spl183_12 ),
    inference(unit_resulting_resolution,[],[f3139,f3144,f3159,f3154,f3169,f3189,f3194,f2283])).

fof(f2283,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | r2_hidden(sK5(X0,X2,X3),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f2007])).

fof(f2007,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ( k1_funct_1(X2,sK5(X0,X2,X3)) != k1_funct_1(X3,sK5(X0,X2,X3))
            & r2_hidden(sK5(X0,X2,X3),X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f1619,f2006])).

fof(f2006,plain,(
    ! [X3,X2,X0] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X2,sK5(X0,X2,X3)) != k1_funct_1(X3,sK5(X0,X2,X3))
        & r2_hidden(sK5(X0,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1619,plain,(
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
    inference(flattening,[],[f1618])).

fof(f1618,plain,(
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
    inference(ennf_transformation,[],[f1538])).

fof(f1538,axiom,(
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

fof(f3195,plain,(
    spl183_12 ),
    inference(avatar_split_clause,[],[f2275,f3192])).

fof(f2275,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f2004])).

fof(f2004,plain,
    ( ~ r2_relset_1(sK2,sK2,sK3,sK4)
    & r1_partfun1(sK3,sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v1_funct_2(sK4,sK2,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v1_funct_2(sK3,sK2,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f1609,f2003,f2002])).

fof(f2002,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X1,X2)
            & r1_partfun1(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK2,sK2,sK3,X2)
          & r1_partfun1(sK3,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
          & v1_funct_2(X2,sK2,sK2)
          & v1_funct_1(X2) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      & v1_funct_2(sK3,sK2,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f2003,plain,
    ( ? [X2] :
        ( ~ r2_relset_1(sK2,sK2,sK3,X2)
        & r1_partfun1(sK3,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
        & v1_funct_2(X2,sK2,sK2)
        & v1_funct_1(X2) )
   => ( ~ r2_relset_1(sK2,sK2,sK3,sK4)
      & r1_partfun1(sK3,sK4)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      & v1_funct_2(sK4,sK2,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f1609,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X1,X2)
          & r1_partfun1(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f1608])).

fof(f1608,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X1,X2)
          & r1_partfun1(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f1534])).

fof(f1534,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( r1_partfun1(X1,X2)
             => r2_relset_1(X0,X0,X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f1533])).

fof(f1533,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( r1_partfun1(X1,X2)
           => r2_relset_1(X0,X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_funct_2)).

fof(f3190,plain,(
    spl183_11 ),
    inference(avatar_split_clause,[],[f2272,f3187])).

fof(f2272,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f2004])).

fof(f3170,plain,(
    ~ spl183_7 ),
    inference(avatar_split_clause,[],[f2277,f3167])).

fof(f2277,plain,(
    ~ r2_relset_1(sK2,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f2004])).

fof(f3160,plain,(
    spl183_5 ),
    inference(avatar_split_clause,[],[f2274,f3157])).

fof(f2274,plain,(
    v1_funct_2(sK4,sK2,sK2) ),
    inference(cnf_transformation,[],[f2004])).

fof(f3155,plain,(
    spl183_4 ),
    inference(avatar_split_clause,[],[f2271,f3152])).

fof(f2271,plain,(
    v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f2004])).

fof(f3150,plain,(
    spl183_3 ),
    inference(avatar_split_clause,[],[f2276,f3147])).

fof(f2276,plain,(
    r1_partfun1(sK3,sK4) ),
    inference(cnf_transformation,[],[f2004])).

fof(f3145,plain,(
    spl183_2 ),
    inference(avatar_split_clause,[],[f2273,f3142])).

fof(f2273,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f2004])).

fof(f3140,plain,(
    spl183_1 ),
    inference(avatar_split_clause,[],[f2270,f3137])).

fof(f2270,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f2004])).
%------------------------------------------------------------------------------
