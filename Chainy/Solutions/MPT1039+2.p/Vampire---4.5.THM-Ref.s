%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1039+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:04 EST 2020

% Result     : Theorem 27.45s
% Output     : Refutation 27.45s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 405 expanded)
%              Number of leaves         :   43 ( 181 expanded)
%              Depth                    :   13
%              Number of atoms          :  659 (1961 expanded)
%              Number of equality atoms :   74 ( 301 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f40687,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3525,f3530,f3535,f3540,f3545,f3550,f3555,f3569,f3596,f4083,f4088,f4156,f4318,f4506,f4558,f6423,f6428,f6473,f10281,f40470,f40551,f40556,f40557,f40636,f40646,f40686])).

fof(f40686,plain,
    ( ~ spl210_96
    | ~ spl210_99
    | ~ spl210_100
    | ~ spl210_101
    | ~ spl210_103 ),
    inference(avatar_contradiction_clause,[],[f40685])).

fof(f40685,plain,
    ( $false
    | ~ spl210_96
    | ~ spl210_99
    | ~ spl210_100
    | ~ spl210_101
    | ~ spl210_103 ),
    inference(subsumption_resolution,[],[f40647,f40674])).

fof(f40674,plain,
    ( v1_funct_2(sK6(sK2,sK3,sK4,sK5),sK2,sK3)
    | ~ spl210_96
    | ~ spl210_99
    | ~ spl210_103 ),
    inference(unit_resulting_resolution,[],[f40469,f40550,f40645,f2640])).

fof(f2640,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_partfun1(X2,X0)
      | v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f1771])).

fof(f1771,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f1770])).

fof(f1770,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1527])).

fof(f1527,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( v1_partfun1(X2,X0)
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_funct_2)).

fof(f40645,plain,
    ( m1_subset_1(sK6(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ spl210_103 ),
    inference(avatar_component_clause,[],[f40643])).

fof(f40643,plain,
    ( spl210_103
  <=> m1_subset_1(sK6(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl210_103])])).

fof(f40550,plain,
    ( v1_partfun1(sK6(sK2,sK3,sK4,sK5),sK2)
    | ~ spl210_99 ),
    inference(avatar_component_clause,[],[f40548])).

fof(f40548,plain,
    ( spl210_99
  <=> v1_partfun1(sK6(sK2,sK3,sK4,sK5),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl210_99])])).

fof(f40469,plain,
    ( v1_funct_1(sK6(sK2,sK3,sK4,sK5))
    | ~ spl210_96 ),
    inference(avatar_component_clause,[],[f40467])).

fof(f40467,plain,
    ( spl210_96
  <=> v1_funct_1(sK6(sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl210_96])])).

fof(f40647,plain,
    ( ~ v1_funct_2(sK6(sK2,sK3,sK4,sK5),sK2,sK3)
    | ~ spl210_96
    | ~ spl210_100
    | ~ spl210_101
    | ~ spl210_103 ),
    inference(unit_resulting_resolution,[],[f40469,f40555,f40635,f40645,f2433])).

fof(f2433,plain,(
    ! [X4] :
      ( ~ r1_partfun1(sK5,X4)
      | ~ r1_partfun1(sK4,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      | ~ v1_funct_2(X4,sK2,sK3)
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f2098])).

fof(f2098,plain,
    ( ! [X4] :
        ( ~ r1_partfun1(sK5,X4)
        | ~ r1_partfun1(sK4,X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
        | ~ v1_funct_2(X4,sK2,sK3)
        | ~ v1_funct_1(X4) )
    & r1_partfun1(sK4,sK5)
    & ( k1_xboole_0 = sK2
      | k1_xboole_0 != sK3 )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f1617,f2097,f2096])).

% (32628)Termination reason: Time limit

% (32628)Memory used [KB]: 22259
% (32628)Time elapsed: 2.528 s
% (32628)------------------------------
% (32628)------------------------------
fof(f2096,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ! [X4] :
                ( ~ r1_partfun1(X3,X4)
                | ~ r1_partfun1(X2,X4)
                | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                | ~ v1_funct_2(X4,X0,X1)
                | ~ v1_funct_1(X4) )
            & r1_partfun1(X2,X3)
            & ( k1_xboole_0 = X0
              | k1_xboole_0 != X1 )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ! [X4] :
              ( ~ r1_partfun1(X3,X4)
              | ~ r1_partfun1(sK4,X4)
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
              | ~ v1_funct_2(X4,sK2,sK3)
              | ~ v1_funct_1(X4) )
          & r1_partfun1(sK4,X3)
          & ( k1_xboole_0 = sK2
            | k1_xboole_0 != sK3 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
          & v1_funct_1(X3) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f2097,plain,
    ( ? [X3] :
        ( ! [X4] :
            ( ~ r1_partfun1(X3,X4)
            | ~ r1_partfun1(sK4,X4)
            | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
            | ~ v1_funct_2(X4,sK2,sK3)
            | ~ v1_funct_1(X4) )
        & r1_partfun1(sK4,X3)
        & ( k1_xboole_0 = sK2
          | k1_xboole_0 != sK3 )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
        & v1_funct_1(X3) )
   => ( ! [X4] :
          ( ~ r1_partfun1(sK5,X4)
          | ~ r1_partfun1(sK4,X4)
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
          | ~ v1_funct_2(X4,sK2,sK3)
          | ~ v1_funct_1(X4) )
      & r1_partfun1(sK4,sK5)
      & ( k1_xboole_0 = sK2
        | k1_xboole_0 != sK3 )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f1617,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r1_partfun1(X3,X4)
              | ~ r1_partfun1(X2,X4)
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X4,X0,X1)
              | ~ v1_funct_1(X4) )
          & r1_partfun1(X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f1616])).

fof(f1616,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r1_partfun1(X3,X4)
              | ~ r1_partfun1(X2,X4)
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X4,X0,X1)
              | ~ v1_funct_1(X4) )
          & r1_partfun1(X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1541])).

fof(f1541,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X3) )
           => ~ ( ! [X4] :
                    ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      & v1_funct_2(X4,X0,X1)
                      & v1_funct_1(X4) )
                   => ~ ( r1_partfun1(X3,X4)
                        & r1_partfun1(X2,X4) ) )
                & r1_partfun1(X2,X3)
                & ( k1_xboole_0 = X1
                 => k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f1540])).

fof(f1540,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ~ ( ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    & v1_funct_2(X4,X0,X1)
                    & v1_funct_1(X4) )
                 => ~ ( r1_partfun1(X3,X4)
                      & r1_partfun1(X2,X4) ) )
              & r1_partfun1(X2,X3)
              & ( k1_xboole_0 = X1
               => k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_2)).

fof(f40635,plain,
    ( r1_partfun1(sK5,sK6(sK2,sK3,sK4,sK5))
    | ~ spl210_101 ),
    inference(avatar_component_clause,[],[f40633])).

fof(f40633,plain,
    ( spl210_101
  <=> r1_partfun1(sK5,sK6(sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl210_101])])).

fof(f40555,plain,
    ( r1_partfun1(sK4,sK6(sK2,sK3,sK4,sK5))
    | ~ spl210_100 ),
    inference(avatar_component_clause,[],[f40553])).

fof(f40553,plain,
    ( spl210_100
  <=> r1_partfun1(sK4,sK6(sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl210_100])])).

fof(f40646,plain,
    ( spl210_103
    | ~ spl210_1
    | ~ spl210_2
    | ~ spl210_3
    | ~ spl210_5
    | ~ spl210_7
    | spl210_9 ),
    inference(avatar_split_clause,[],[f35357,f3562,f3552,f3542,f3532,f3527,f3522,f40643])).

fof(f3522,plain,
    ( spl210_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl210_1])])).

fof(f3527,plain,
    ( spl210_2
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl210_2])])).

fof(f3532,plain,
    ( spl210_3
  <=> r1_partfun1(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl210_3])])).

fof(f3542,plain,
    ( spl210_5
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl210_5])])).

fof(f3552,plain,
    ( spl210_7
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl210_7])])).

fof(f3562,plain,
    ( spl210_9
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl210_9])])).

fof(f35357,plain,
    ( m1_subset_1(sK6(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ spl210_1
    | ~ spl210_2
    | ~ spl210_3
    | ~ spl210_5
    | ~ spl210_7
    | spl210_9 ),
    inference(unit_resulting_resolution,[],[f3524,f3529,f3564,f3534,f3544,f3554,f2453])).

fof(f2453,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK6(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_partfun1(X2,X3)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f2100])).

fof(f2100,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r1_partfun1(X3,sK6(X0,X1,X2,X3))
            & r1_partfun1(X2,sK6(X0,X1,X2,X3))
            & v1_partfun1(sK6(X0,X1,X2,X3),X0)
            & m1_subset_1(sK6(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(sK6(X0,X1,X2,X3)) )
          | ~ r1_partfun1(X2,X3)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f1631,f2099])).

fof(f2099,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( r1_partfun1(X3,X4)
          & r1_partfun1(X2,X4)
          & v1_partfun1(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X4) )
     => ( r1_partfun1(X3,sK6(X0,X1,X2,X3))
        & r1_partfun1(X2,sK6(X0,X1,X2,X3))
        & v1_partfun1(sK6(X0,X1,X2,X3),X0)
        & m1_subset_1(sK6(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(sK6(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1631,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ? [X4] :
              ( r1_partfun1(X3,X4)
              & r1_partfun1(X2,X4)
              & v1_partfun1(X4,X0)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X4) )
          | ~ r1_partfun1(X2,X3)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f1630])).

fof(f1630,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ? [X4] :
              ( r1_partfun1(X3,X4)
              & r1_partfun1(X2,X4)
              & v1_partfun1(X4,X0)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X4) )
          | ~ r1_partfun1(X2,X3)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1543])).

fof(f1543,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ~ ( ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    & v1_funct_1(X4) )
                 => ~ ( r1_partfun1(X3,X4)
                      & r1_partfun1(X2,X4)
                      & v1_partfun1(X4,X0) ) )
              & r1_partfun1(X2,X3)
              & ( k1_xboole_0 = X1
               => k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_partfun1)).

fof(f3554,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ spl210_7 ),
    inference(avatar_component_clause,[],[f3552])).

fof(f3544,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ spl210_5 ),
    inference(avatar_component_clause,[],[f3542])).

fof(f3534,plain,
    ( r1_partfun1(sK4,sK5)
    | ~ spl210_3 ),
    inference(avatar_component_clause,[],[f3532])).

fof(f3564,plain,
    ( k1_xboole_0 != sK3
    | spl210_9 ),
    inference(avatar_component_clause,[],[f3562])).

fof(f3529,plain,
    ( v1_funct_1(sK5)
    | ~ spl210_2 ),
    inference(avatar_component_clause,[],[f3527])).

fof(f3524,plain,
    ( v1_funct_1(sK4)
    | ~ spl210_1 ),
    inference(avatar_component_clause,[],[f3522])).

fof(f40636,plain,
    ( spl210_101
    | ~ spl210_1
    | ~ spl210_2
    | ~ spl210_3
    | ~ spl210_5
    | ~ spl210_7
    | spl210_9 ),
    inference(avatar_split_clause,[],[f35360,f3562,f3552,f3542,f3532,f3527,f3522,f40633])).

fof(f35360,plain,
    ( r1_partfun1(sK5,sK6(sK2,sK3,sK4,sK5))
    | ~ spl210_1
    | ~ spl210_2
    | ~ spl210_3
    | ~ spl210_5
    | ~ spl210_7
    | spl210_9 ),
    inference(unit_resulting_resolution,[],[f3524,f3529,f3564,f3534,f3544,f3554,f2459])).

fof(f2459,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X3,sK6(X0,X1,X2,X3))
      | ~ r1_partfun1(X2,X3)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f2100])).

fof(f40557,plain,
    ( ~ spl210_34
    | spl210_43 ),
    inference(avatar_split_clause,[],[f4801,f4352,f4043])).

fof(f4043,plain,
    ( spl210_34
  <=> r1_tarski(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl210_34])])).

fof(f4352,plain,
    ( spl210_43
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl210_43])])).

fof(f4801,plain,
    ( ~ r1_tarski(sK4,k1_xboole_0)
    | spl210_43 ),
    inference(unit_resulting_resolution,[],[f4353,f2505])).

fof(f2505,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1664])).

fof(f1664,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f101])).

fof(f101,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f4353,plain,
    ( k1_xboole_0 != sK4
    | spl210_43 ),
    inference(avatar_component_clause,[],[f4352])).

fof(f40556,plain,
    ( spl210_100
    | ~ spl210_1
    | ~ spl210_2
    | ~ spl210_3
    | ~ spl210_5
    | ~ spl210_7
    | spl210_9 ),
    inference(avatar_split_clause,[],[f35359,f3562,f3552,f3542,f3532,f3527,f3522,f40553])).

fof(f35359,plain,
    ( r1_partfun1(sK4,sK6(sK2,sK3,sK4,sK5))
    | ~ spl210_1
    | ~ spl210_2
    | ~ spl210_3
    | ~ spl210_5
    | ~ spl210_7
    | spl210_9 ),
    inference(unit_resulting_resolution,[],[f3524,f3529,f3564,f3534,f3544,f3554,f2457])).

fof(f2457,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X2,sK6(X0,X1,X2,X3))
      | ~ r1_partfun1(X2,X3)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f2100])).

fof(f40551,plain,
    ( spl210_99
    | ~ spl210_1
    | ~ spl210_2
    | ~ spl210_3
    | ~ spl210_5
    | ~ spl210_7
    | spl210_9 ),
    inference(avatar_split_clause,[],[f35358,f3562,f3552,f3542,f3532,f3527,f3522,f40548])).

fof(f35358,plain,
    ( v1_partfun1(sK6(sK2,sK3,sK4,sK5),sK2)
    | ~ spl210_1
    | ~ spl210_2
    | ~ spl210_3
    | ~ spl210_5
    | ~ spl210_7
    | spl210_9 ),
    inference(unit_resulting_resolution,[],[f3524,f3529,f3564,f3534,f3544,f3554,f2455])).

fof(f2455,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_partfun1(sK6(X0,X1,X2,X3),X0)
      | ~ r1_partfun1(X2,X3)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f2100])).

fof(f40470,plain,
    ( spl210_96
    | ~ spl210_1
    | ~ spl210_2
    | ~ spl210_3
    | ~ spl210_5
    | ~ spl210_7
    | spl210_9 ),
    inference(avatar_split_clause,[],[f3836,f3562,f3552,f3542,f3532,f3527,f3522,f40467])).

fof(f3836,plain,
    ( v1_funct_1(sK6(sK2,sK3,sK4,sK5))
    | ~ spl210_1
    | ~ spl210_2
    | ~ spl210_3
    | ~ spl210_5
    | ~ spl210_7
    | spl210_9 ),
    inference(unit_resulting_resolution,[],[f3524,f3529,f3564,f3534,f3544,f3554,f2451])).

fof(f2451,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(sK6(X0,X1,X2,X3))
      | ~ r1_partfun1(X2,X3)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f2100])).

fof(f10281,plain,
    ( ~ spl210_10
    | ~ spl210_15
    | ~ spl210_41
    | ~ spl210_43
    | ~ spl210_46
    | ~ spl210_61
    | ~ spl210_62
    | ~ spl210_63 ),
    inference(avatar_contradiction_clause,[],[f10280])).

fof(f10280,plain,
    ( $false
    | ~ spl210_10
    | ~ spl210_15
    | ~ spl210_41
    | ~ spl210_43
    | ~ spl210_46
    | ~ spl210_61
    | ~ spl210_62
    | ~ spl210_63 ),
    inference(subsumption_resolution,[],[f10040,f6925])).

fof(f6925,plain,
    ( ! [X1] : v1_funct_2(k1_xboole_0,k1_xboole_0,X1)
    | ~ spl210_15
    | ~ spl210_61
    | ~ spl210_62
    | ~ spl210_63 ),
    inference(forward_demodulation,[],[f6924,f6422])).

fof(f6422,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl210_61 ),
    inference(avatar_component_clause,[],[f6420])).

fof(f6420,plain,
    ( spl210_61
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl210_61])])).

fof(f6924,plain,
    ( ! [X1] : v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X1)
    | ~ spl210_15
    | ~ spl210_62
    | ~ spl210_63 ),
    inference(subsumption_resolution,[],[f6923,f3595])).

fof(f3595,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl210_15 ),
    inference(avatar_component_clause,[],[f3593])).

fof(f3593,plain,
    ( spl210_15
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl210_15])])).

fof(f6923,plain,
    ( ! [X1] :
        ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X1)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl210_62
    | ~ spl210_63 ),
    inference(subsumption_resolution,[],[f6922,f6472])).

fof(f6472,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl210_63 ),
    inference(avatar_component_clause,[],[f6470])).

fof(f6470,plain,
    ( spl210_63
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl210_63])])).

fof(f6922,plain,
    ( ! [X1] :
        ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X1)
        | ~ v1_funct_1(k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl210_62 ),
    inference(subsumption_resolution,[],[f6919,f2507])).

fof(f2507,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f6919,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_xboole_0,X1)
        | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X1)
        | ~ v1_funct_1(k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl210_62 ),
    inference(superposition,[],[f2445,f6427])).

fof(f6427,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl210_62 ),
    inference(avatar_component_clause,[],[f6425])).

fof(f6425,plain,
    ( spl210_62
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl210_62])])).

fof(f2445,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1625])).

fof(f1625,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1624])).

fof(f1624,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1578])).

fof(f1578,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f10040,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl210_10
    | ~ spl210_41
    | ~ spl210_43
    | ~ spl210_46
    | ~ spl210_63 ),
    inference(backward_demodulation,[],[f6784,f3568])).

fof(f3568,plain,
    ( k1_xboole_0 = sK2
    | ~ spl210_10 ),
    inference(avatar_component_clause,[],[f3566])).

fof(f3566,plain,
    ( spl210_10
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl210_10])])).

fof(f6784,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK2,sK3)
    | ~ spl210_41
    | ~ spl210_43
    | ~ spl210_46
    | ~ spl210_63 ),
    inference(unit_resulting_resolution,[],[f4557,f2502,f6472,f5641])).

fof(f5641,plain,
    ( ! [X4] :
        ( ~ v1_funct_2(X4,sK2,sK3)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
        | ~ r1_partfun1(k1_xboole_0,X4)
        | ~ v1_funct_1(X4) )
    | ~ spl210_41
    | ~ spl210_43 ),
    inference(duplicate_literal_removal,[],[f5640])).

fof(f5640,plain,
    ( ! [X4] :
        ( ~ r1_partfun1(k1_xboole_0,X4)
        | ~ r1_partfun1(k1_xboole_0,X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
        | ~ v1_funct_2(X4,sK2,sK3)
        | ~ v1_funct_1(X4) )
    | ~ spl210_41
    | ~ spl210_43 ),
    inference(backward_demodulation,[],[f5583,f4507])).

fof(f4507,plain,
    ( k1_xboole_0 = sK5
    | ~ spl210_41 ),
    inference(unit_resulting_resolution,[],[f4321,f2505])).

fof(f4321,plain,
    ( r1_tarski(sK5,k1_xboole_0)
    | ~ spl210_41 ),
    inference(avatar_component_clause,[],[f4320])).

fof(f4320,plain,
    ( spl210_41
  <=> r1_tarski(sK5,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl210_41])])).

fof(f5583,plain,
    ( ! [X4] :
        ( ~ r1_partfun1(k1_xboole_0,X4)
        | ~ r1_partfun1(sK5,X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
        | ~ v1_funct_2(X4,sK2,sK3)
        | ~ v1_funct_1(X4) )
    | ~ spl210_43 ),
    inference(backward_demodulation,[],[f2433,f4354])).

fof(f4354,plain,
    ( k1_xboole_0 = sK4
    | ~ spl210_43 ),
    inference(avatar_component_clause,[],[f4352])).

fof(f2502,plain,(
    ! [X0,X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f1248])).

fof(f1248,axiom,(
    ! [X0,X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relset_1)).

fof(f4557,plain,
    ( r1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ spl210_46 ),
    inference(avatar_component_clause,[],[f4555])).

fof(f4555,plain,
    ( spl210_46
  <=> r1_partfun1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl210_46])])).

fof(f6473,plain,
    ( spl210_63
    | ~ spl210_4
    | ~ spl210_6 ),
    inference(avatar_split_clause,[],[f3689,f3547,f3537,f6470])).

fof(f3537,plain,
    ( spl210_4
  <=> v1_relat_1(sK20) ),
    introduced(avatar_definition,[new_symbols(naming,[spl210_4])])).

fof(f3547,plain,
    ( spl210_6
  <=> v1_funct_1(sK20) ),
    introduced(avatar_definition,[new_symbols(naming,[spl210_6])])).

fof(f3689,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl210_4
    | ~ spl210_6 ),
    inference(unit_resulting_resolution,[],[f3539,f3549,f2506,f2544])).

fof(f2544,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_funct_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1691])).

fof(f1691,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_funct_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1690])).

fof(f1690,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_funct_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f892])).

fof(f892,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_funct_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_funct_1)).

fof(f2506,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f522])).

fof(f522,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f3549,plain,
    ( v1_funct_1(sK20)
    | ~ spl210_6 ),
    inference(avatar_component_clause,[],[f3547])).

fof(f3539,plain,
    ( v1_relat_1(sK20)
    | ~ spl210_4 ),
    inference(avatar_component_clause,[],[f3537])).

fof(f6428,plain,(
    spl210_62 ),
    inference(avatar_split_clause,[],[f2636,f6425])).

fof(f2636,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f856])).

fof(f856,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f6423,plain,(
    spl210_61 ),
    inference(avatar_split_clause,[],[f2635,f6420])).

fof(f2635,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f856])).

fof(f4558,plain,
    ( spl210_46
    | ~ spl210_40
    | ~ spl210_41 ),
    inference(avatar_split_clause,[],[f4532,f4320,f4315,f4555])).

fof(f4315,plain,
    ( spl210_40
  <=> r1_partfun1(k1_xboole_0,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl210_40])])).

fof(f4532,plain,
    ( r1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ spl210_40
    | ~ spl210_41 ),
    inference(backward_demodulation,[],[f4317,f4507])).

fof(f4317,plain,
    ( r1_partfun1(k1_xboole_0,sK5)
    | ~ spl210_40 ),
    inference(avatar_component_clause,[],[f4315])).

fof(f4506,plain,
    ( spl210_41
    | ~ spl210_10
    | ~ spl210_37 ),
    inference(avatar_split_clause,[],[f4465,f4085,f3566,f4320])).

fof(f4085,plain,
    ( spl210_37
  <=> r1_tarski(sK5,k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl210_37])])).

fof(f4465,plain,
    ( r1_tarski(sK5,k1_xboole_0)
    | ~ spl210_10
    | ~ spl210_37 ),
    inference(forward_demodulation,[],[f4453,f3232])).

fof(f3232,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f2495])).

fof(f2495,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f2116])).

fof(f2116,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f2115])).

fof(f2115,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f4453,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(k1_xboole_0,sK3))
    | ~ spl210_10
    | ~ spl210_37 ),
    inference(backward_demodulation,[],[f4087,f3568])).

fof(f4087,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(sK2,sK3))
    | ~ spl210_37 ),
    inference(avatar_component_clause,[],[f4085])).

fof(f4318,plain,
    ( spl210_40
    | ~ spl210_3
    | ~ spl210_34 ),
    inference(avatar_split_clause,[],[f4279,f4043,f3532,f4315])).

fof(f4279,plain,
    ( r1_partfun1(k1_xboole_0,sK5)
    | ~ spl210_3
    | ~ spl210_34 ),
    inference(backward_demodulation,[],[f3534,f4259])).

fof(f4259,plain,
    ( k1_xboole_0 = sK4
    | ~ spl210_34 ),
    inference(unit_resulting_resolution,[],[f4044,f2505])).

fof(f4044,plain,
    ( r1_tarski(sK4,k1_xboole_0)
    | ~ spl210_34 ),
    inference(avatar_component_clause,[],[f4043])).

fof(f4156,plain,
    ( ~ spl210_10
    | spl210_34
    | ~ spl210_36 ),
    inference(avatar_contradiction_clause,[],[f4155])).

fof(f4155,plain,
    ( $false
    | ~ spl210_10
    | spl210_34
    | ~ spl210_36 ),
    inference(subsumption_resolution,[],[f4154,f4045])).

fof(f4045,plain,
    ( ~ r1_tarski(sK4,k1_xboole_0)
    | spl210_34 ),
    inference(avatar_component_clause,[],[f4043])).

fof(f4154,plain,
    ( r1_tarski(sK4,k1_xboole_0)
    | ~ spl210_10
    | ~ spl210_36 ),
    inference(forward_demodulation,[],[f4140,f3232])).

fof(f4140,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(k1_xboole_0,sK3))
    | ~ spl210_10
    | ~ spl210_36 ),
    inference(backward_demodulation,[],[f4082,f3568])).

fof(f4082,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK2,sK3))
    | ~ spl210_36 ),
    inference(avatar_component_clause,[],[f4080])).

fof(f4080,plain,
    ( spl210_36
  <=> r1_tarski(sK4,k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl210_36])])).

fof(f4088,plain,
    ( spl210_37
    | ~ spl210_7 ),
    inference(avatar_split_clause,[],[f3620,f3552,f4085])).

fof(f3620,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(sK2,sK3))
    | ~ spl210_7 ),
    inference(unit_resulting_resolution,[],[f3554,f2511])).

fof(f2511,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2123])).

fof(f2123,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f609])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f4083,plain,
    ( spl210_36
    | ~ spl210_5 ),
    inference(avatar_split_clause,[],[f3619,f3542,f4080])).

fof(f3619,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK2,sK3))
    | ~ spl210_5 ),
    inference(unit_resulting_resolution,[],[f3544,f2511])).

fof(f3596,plain,(
    spl210_15 ),
    inference(avatar_split_clause,[],[f3591,f3593])).

fof(f3591,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f2541,f3231])).

fof(f3231,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f2496])).

fof(f2496,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f2116])).

fof(f2541,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f696])).

fof(f696,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f3569,plain,
    ( ~ spl210_9
    | spl210_10 ),
    inference(avatar_split_clause,[],[f2431,f3566,f3562])).

fof(f2431,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f2098])).

fof(f3555,plain,(
    spl210_7 ),
    inference(avatar_split_clause,[],[f2430,f3552])).

fof(f2430,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f2098])).

fof(f3550,plain,(
    spl210_6 ),
    inference(avatar_split_clause,[],[f2543,f3547])).

fof(f2543,plain,(
    v1_funct_1(sK20) ),
    inference(cnf_transformation,[],[f2143])).

fof(f2143,plain,
    ( v1_funct_1(sK20)
    & v1_relat_1(sK20) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK20])],[f930,f2142])).

fof(f2142,plain,
    ( ? [X0] :
        ( v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( v1_funct_1(sK20)
      & v1_relat_1(sK20) ) ),
    introduced(choice_axiom,[])).

fof(f930,axiom,(
    ? [X0] :
      ( v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_1)).

fof(f3545,plain,(
    spl210_5 ),
    inference(avatar_split_clause,[],[f2428,f3542])).

fof(f2428,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f2098])).

fof(f3540,plain,(
    spl210_4 ),
    inference(avatar_split_clause,[],[f2542,f3537])).

fof(f2542,plain,(
    v1_relat_1(sK20) ),
    inference(cnf_transformation,[],[f2143])).

fof(f3535,plain,(
    spl210_3 ),
    inference(avatar_split_clause,[],[f2432,f3532])).

fof(f2432,plain,(
    r1_partfun1(sK4,sK5) ),
    inference(cnf_transformation,[],[f2098])).

fof(f3530,plain,(
    spl210_2 ),
    inference(avatar_split_clause,[],[f2429,f3527])).

fof(f2429,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f2098])).

fof(f3525,plain,(
    spl210_1 ),
    inference(avatar_split_clause,[],[f2427,f3522])).

fof(f2427,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f2098])).
%------------------------------------------------------------------------------
