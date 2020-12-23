%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:54 EST 2020

% Result     : Theorem 1.27s
% Output     : Refutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 445 expanded)
%              Number of leaves         :   13 ( 129 expanded)
%              Depth                    :   26
%              Number of atoms          :  649 (3169 expanded)
%              Number of equality atoms :   88 ( 366 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f997,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f665,f996])).

fof(f996,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f995])).

fof(f995,plain,
    ( $false
    | spl8_1 ),
    inference(subsumption_resolution,[],[f993,f801])).

fof(f801,plain,
    ( sP1(sK5,sK4,sK2,sK3)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f800,f32])).

fof(f32,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f8,f22,f21])).

fof(f21,plain,
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

fof(f22,plain,
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

fof(f8,plain,(
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
    inference(flattening,[],[f7])).

fof(f7,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
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
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
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

fof(f800,plain,
    ( sP1(sK5,sK4,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f796,f37])).

fof(f37,plain,(
    r1_partfun1(sK4,sK5) ),
    inference(cnf_transformation,[],[f23])).

fof(f796,plain,
    ( sP1(sK5,sK4,sK2,sK3)
    | ~ r1_partfun1(sK4,sK5)
    | ~ v1_funct_1(sK4)
    | spl8_1 ),
    inference(resolution,[],[f743,f33])).

fof(f33,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f23])).

fof(f743,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
        | sP1(sK5,X1,sK2,sK3)
        | ~ r1_partfun1(X1,sK5)
        | ~ v1_funct_1(X1) )
    | spl8_1 ),
    inference(subsumption_resolution,[],[f742,f34])).

fof(f34,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f23])).

fof(f742,plain,
    ( ! [X1] :
        ( ~ r1_partfun1(X1,sK5)
        | sP1(sK5,X1,sK2,sK3)
        | ~ v1_funct_1(sK5)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
        | ~ v1_funct_1(X1) )
    | spl8_1 ),
    inference(subsumption_resolution,[],[f725,f63])).

fof(f63,plain,
    ( k1_xboole_0 != sK3
    | spl8_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl8_1
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f725,plain,(
    ! [X1] :
      ( ~ r1_partfun1(X1,sK5)
      | k1_xboole_0 = sK3
      | sP1(sK5,X1,sK2,sK3)
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      | ~ v1_funct_1(X1) ) ),
    inference(resolution,[],[f35,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_partfun1(X2,X3)
      | k1_xboole_0 = X1
      | sP1(X3,X2,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( sP1(X3,X2,X0,X1)
          | ~ r1_partfun1(X2,X3)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f16,f19])).

fof(f19,plain,(
    ! [X3,X2,X0,X1] :
      ( ? [X4] :
          ( r1_partfun1(X3,X4)
          & r1_partfun1(X2,X4)
          & v1_partfun1(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X4) )
      | ~ sP1(X3,X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f35,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f23])).

fof(f993,plain,
    ( ~ sP1(sK5,sK4,sK2,sK3)
    | spl8_1 ),
    inference(duplicate_literal_removal,[],[f988])).

fof(f988,plain,
    ( ~ sP1(sK5,sK4,sK2,sK3)
    | ~ sP1(sK5,sK4,sK2,sK3)
    | spl8_1 ),
    inference(resolution,[],[f984,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X1,sK7(X0,X1,X2,X3))
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_partfun1(X0,sK7(X0,X1,X2,X3))
        & r1_partfun1(X1,sK7(X0,X1,X2,X3))
        & v1_partfun1(sK7(X0,X1,X2,X3),X2)
        & m1_subset_1(sK7(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(sK7(X0,X1,X2,X3)) )
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f29,f30])).

fof(f30,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( r1_partfun1(X0,X4)
          & r1_partfun1(X1,X4)
          & v1_partfun1(X4,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
          & v1_funct_1(X4) )
     => ( r1_partfun1(X0,sK7(X0,X1,X2,X3))
        & r1_partfun1(X1,sK7(X0,X1,X2,X3))
        & v1_partfun1(sK7(X0,X1,X2,X3),X2)
        & m1_subset_1(sK7(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(sK7(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4] :
          ( r1_partfun1(X0,X4)
          & r1_partfun1(X1,X4)
          & v1_partfun1(X4,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
          & v1_funct_1(X4) )
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X3,X2,X0,X1] :
      ( ? [X4] :
          ( r1_partfun1(X3,X4)
          & r1_partfun1(X2,X4)
          & v1_partfun1(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X4) )
      | ~ sP1(X3,X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f984,plain,
    ( ! [X3] :
        ( ~ r1_partfun1(sK4,sK7(sK5,X3,sK2,sK3))
        | ~ sP1(sK5,X3,sK2,sK3) )
    | spl8_1 ),
    inference(duplicate_literal_removal,[],[f979])).

fof(f979,plain,
    ( ! [X3] :
        ( ~ r1_partfun1(sK4,sK7(sK5,X3,sK2,sK3))
        | ~ sP1(sK5,X3,sK2,sK3)
        | ~ sP1(sK5,X3,sK2,sK3) )
    | spl8_1 ),
    inference(resolution,[],[f976,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X0,sK7(X0,X1,X2,X3))
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f976,plain,
    ( ! [X0,X1] :
        ( ~ r1_partfun1(sK5,sK7(X0,X1,sK2,sK3))
        | ~ r1_partfun1(sK4,sK7(X0,X1,sK2,sK3))
        | ~ sP1(X0,X1,sK2,sK3) )
    | spl8_1 ),
    inference(subsumption_resolution,[],[f975,f63])).

fof(f975,plain,
    ( ! [X0,X1] :
        ( ~ r1_partfun1(sK4,sK7(X0,X1,sK2,sK3))
        | ~ r1_partfun1(sK5,sK7(X0,X1,sK2,sK3))
        | ~ sP1(X0,X1,sK2,sK3)
        | k1_xboole_0 = sK3 )
    | spl8_1 ),
    inference(duplicate_literal_removal,[],[f970])).

fof(f970,plain,
    ( ! [X0,X1] :
        ( ~ r1_partfun1(sK4,sK7(X0,X1,sK2,sK3))
        | ~ r1_partfun1(sK5,sK7(X0,X1,sK2,sK3))
        | ~ sP1(X0,X1,sK2,sK3)
        | k1_xboole_0 = sK3
        | ~ sP1(X0,X1,sK2,sK3) )
    | spl8_1 ),
    inference(resolution,[],[f967,f170])).

fof(f170,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(sK7(X0,X1,X2,X3),X3,X2)
      | k1_xboole_0 = X3
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(subsumption_resolution,[],[f167,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(sK7(X0,X1,X2,X3))
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f167,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3)
      | k1_xboole_0 = X3
      | sP0(sK7(X0,X1,X2,X3),X3,X2)
      | ~ v1_funct_1(sK7(X0,X1,X2,X3)) ) ),
    inference(resolution,[],[f49,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | sP0(X2,X1,X0)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( sP0(X2,X1,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f12,f17])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      | ~ sP0(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ~ ( ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X3,X0,X1)
                & v1_funct_1(X3) )
             => ~ r1_partfun1(X2,X3) )
          & ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_2)).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK7(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f967,plain,
    ( ! [X61,X62] :
        ( ~ sP0(sK7(X61,X62,sK2,sK3),sK3,sK2)
        | ~ r1_partfun1(sK4,sK7(X61,X62,sK2,sK3))
        | ~ r1_partfun1(sK5,sK7(X61,X62,sK2,sK3))
        | ~ sP1(X61,X62,sK2,sK3) )
    | spl8_1 ),
    inference(subsumption_resolution,[],[f948,f63])).

fof(f948,plain,(
    ! [X61,X62] :
      ( ~ r1_partfun1(sK5,sK7(X61,X62,sK2,sK3))
      | ~ r1_partfun1(sK4,sK7(X61,X62,sK2,sK3))
      | ~ sP0(sK7(X61,X62,sK2,sK3),sK3,sK2)
      | k1_xboole_0 = sK3
      | ~ sP1(X61,X62,sK2,sK3) ) ),
    inference(superposition,[],[f99,f473])).

fof(f473,plain,(
    ! [X6,X4,X5,X3] :
      ( sK7(X3,X4,X5,X6) = sK6(sK7(X3,X4,X5,X6),X6,X5)
      | k1_xboole_0 = X6
      | ~ sP1(X3,X4,X5,X6) ) ),
    inference(subsumption_resolution,[],[f472,f48])).

fof(f472,plain,(
    ! [X6,X4,X5,X3] :
      ( sK7(X3,X4,X5,X6) = sK6(sK7(X3,X4,X5,X6),X6,X5)
      | ~ v1_funct_1(sK7(X3,X4,X5,X6))
      | k1_xboole_0 = X6
      | ~ sP1(X3,X4,X5,X6) ) ),
    inference(subsumption_resolution,[],[f469,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_partfun1(sK7(X0,X1,X2,X3),X2)
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f469,plain,(
    ! [X6,X4,X5,X3] :
      ( sK7(X3,X4,X5,X6) = sK6(sK7(X3,X4,X5,X6),X6,X5)
      | ~ v1_partfun1(sK7(X3,X4,X5,X6),X5)
      | ~ v1_funct_1(sK7(X3,X4,X5,X6))
      | k1_xboole_0 = X6
      | ~ sP1(X3,X4,X5,X6) ) ),
    inference(resolution,[],[f421,f49])).

fof(f421,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | sK6(X2,X4,X3) = X2
      | ~ v1_partfun1(X2,X3)
      | ~ v1_funct_1(X2)
      | k1_xboole_0 = X4 ) ),
    inference(subsumption_resolution,[],[f418,f45])).

fof(f418,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_partfun1(X2,X3)
      | sK6(X2,X4,X3) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X2)
      | ~ sP0(X2,X4,X3)
      | k1_xboole_0 = X4 ) ),
    inference(duplicate_literal_removal,[],[f417])).

fof(f417,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_partfun1(X2,X3)
      | sK6(X2,X4,X3) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X2)
      | ~ sP0(X2,X4,X3)
      | k1_xboole_0 = X4
      | ~ sP0(X2,X4,X3) ) ),
    inference(resolution,[],[f381,f194])).

fof(f194,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(sK6(X1,X0,X2),X2)
      | k1_xboole_0 = X0
      | ~ sP0(X1,X0,X2) ) ),
    inference(subsumption_resolution,[],[f193,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(sK6(X0,X1,X2))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r1_partfun1(X0,sK6(X0,X1,X2))
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(sK6(X0,X1,X2),X2,X1)
        & v1_funct_1(sK6(X0,X1,X2)) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f25,f26])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r1_partfun1(X0,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
          & v1_funct_2(X3,X2,X1)
          & v1_funct_1(X3) )
     => ( r1_partfun1(X0,sK6(X0,X1,X2))
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(sK6(X0,X1,X2),X2,X1)
        & v1_funct_1(sK6(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( r1_partfun1(X0,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
          & v1_funct_2(X3,X2,X1)
          & v1_funct_1(X3) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      | ~ sP0(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f193,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | v1_partfun1(sK6(X1,X0,X2),X2)
      | ~ v1_funct_1(sK6(X1,X0,X2))
      | ~ sP0(X1,X0,X2) ) ),
    inference(subsumption_resolution,[],[f191,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(sK6(X0,X1,X2),X2,X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f191,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | v1_partfun1(sK6(X1,X0,X2),X2)
      | ~ v1_funct_2(sK6(X1,X0,X2),X2,X0)
      | ~ v1_funct_1(sK6(X1,X0,X2))
      | ~ sP0(X1,X0,X2) ) ),
    inference(resolution,[],[f58,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

% (5474)Termination reason: Refutation not found, incomplete strategy

% (5474)Memory used [KB]: 11001
% (5474)Time elapsed: 0.154 s
% (5474)------------------------------
% (5474)------------------------------
fof(f381,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_partfun1(sK6(X0,X1,X2),X2)
      | ~ v1_partfun1(X0,X2)
      | sK6(X0,X1,X2) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f380])).

fof(f380,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_partfun1(sK6(X0,X1,X2),X2)
      | ~ v1_partfun1(X0,X2)
      | sK6(X0,X1,X2) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X0)
      | ~ sP0(X0,X1,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(resolution,[],[f253,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_partfun1(X0,sK6(X0,X1,X2))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f253,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ r1_partfun1(X2,sK6(X3,X4,X5))
      | ~ v1_partfun1(sK6(X3,X4,X5),X5)
      | ~ v1_partfun1(X2,X5)
      | sK6(X3,X4,X5) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X4)))
      | ~ v1_funct_1(X2)
      | ~ sP0(X3,X4,X5) ) ),
    inference(subsumption_resolution,[],[f237,f41])).

fof(f237,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ r1_partfun1(X2,sK6(X3,X4,X5))
      | ~ v1_partfun1(sK6(X3,X4,X5),X5)
      | ~ v1_partfun1(X2,X5)
      | sK6(X3,X4,X5) = X2
      | ~ v1_funct_1(sK6(X3,X4,X5))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X4)))
      | ~ v1_funct_1(X2)
      | ~ sP0(X3,X4,X5) ) ),
    inference(resolution,[],[f47,f43])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_partfun1(X2,X3)
      | ~ v1_partfun1(X3,X0)
      | ~ v1_partfun1(X2,X0)
      | X2 = X3
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f99,plain,(
    ! [X0] :
      ( ~ r1_partfun1(sK5,sK6(X0,sK3,sK2))
      | ~ r1_partfun1(sK4,sK6(X0,sK3,sK2))
      | ~ sP0(X0,sK3,sK2) ) ),
    inference(subsumption_resolution,[],[f98,f41])).

fof(f98,plain,(
    ! [X0] :
      ( ~ sP0(X0,sK3,sK2)
      | ~ r1_partfun1(sK4,sK6(X0,sK3,sK2))
      | ~ r1_partfun1(sK5,sK6(X0,sK3,sK2))
      | ~ v1_funct_1(sK6(X0,sK3,sK2)) ) ),
    inference(subsumption_resolution,[],[f96,f42])).

fof(f96,plain,(
    ! [X0] :
      ( ~ sP0(X0,sK3,sK2)
      | ~ r1_partfun1(sK4,sK6(X0,sK3,sK2))
      | ~ r1_partfun1(sK5,sK6(X0,sK3,sK2))
      | ~ v1_funct_2(sK6(X0,sK3,sK2),sK2,sK3)
      | ~ v1_funct_1(sK6(X0,sK3,sK2)) ) ),
    inference(resolution,[],[f43,f38])).

fof(f38,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      | ~ r1_partfun1(sK4,X4)
      | ~ r1_partfun1(sK5,X4)
      | ~ v1_funct_2(X4,sK2,sK3)
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f665,plain,(
    ~ spl8_2 ),
    inference(avatar_contradiction_clause,[],[f664])).

fof(f664,plain,
    ( $false
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f663,f631])).

fof(f631,plain,
    ( sP1(sK5,sK4,k1_xboole_0,sK3)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f630,f32])).

fof(f630,plain,
    ( sP1(sK5,sK4,k1_xboole_0,sK3)
    | ~ v1_funct_1(sK4)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f626,f37])).

fof(f626,plain,
    ( sP1(sK5,sK4,k1_xboole_0,sK3)
    | ~ r1_partfun1(sK4,sK5)
    | ~ v1_funct_1(sK4)
    | ~ spl8_2 ),
    inference(resolution,[],[f591,f575])).

fof(f575,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f33,f67])).

fof(f67,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl8_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f591,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
        | sP1(sK5,X0,k1_xboole_0,sK3)
        | ~ r1_partfun1(X0,sK5)
        | ~ v1_funct_1(X0) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f578,f34])).

fof(f578,plain,
    ( ! [X0] :
        ( ~ r1_partfun1(X0,sK5)
        | sP1(sK5,X0,k1_xboole_0,sK3)
        | ~ v1_funct_1(sK5)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
        | ~ v1_funct_1(X0) )
    | ~ spl8_2 ),
    inference(resolution,[],[f574,f57])).

fof(f57,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ r1_partfun1(X2,X3)
      | sP1(X3,X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X3,X2,X0,X1)
      | ~ r1_partfun1(X2,X3)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f574,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f35,f67])).

fof(f663,plain,
    ( ~ sP1(sK5,sK4,k1_xboole_0,sK3)
    | ~ spl8_2 ),
    inference(duplicate_literal_removal,[],[f658])).

fof(f658,plain,
    ( ~ sP1(sK5,sK4,k1_xboole_0,sK3)
    | ~ sP1(sK5,sK4,k1_xboole_0,sK3)
    | ~ spl8_2 ),
    inference(resolution,[],[f656,f51])).

fof(f656,plain,
    ( ! [X1] :
        ( ~ r1_partfun1(sK4,sK7(sK5,X1,k1_xboole_0,sK3))
        | ~ sP1(sK5,X1,k1_xboole_0,sK3) )
    | ~ spl8_2 ),
    inference(duplicate_literal_removal,[],[f651])).

fof(f651,plain,
    ( ! [X1] :
        ( ~ r1_partfun1(sK4,sK7(sK5,X1,k1_xboole_0,sK3))
        | ~ sP1(sK5,X1,k1_xboole_0,sK3)
        | ~ sP1(sK5,X1,k1_xboole_0,sK3) )
    | ~ spl8_2 ),
    inference(resolution,[],[f620,f52])).

fof(f620,plain,
    ( ! [X2,X1] :
        ( ~ r1_partfun1(sK5,sK7(X1,X2,k1_xboole_0,sK3))
        | ~ r1_partfun1(sK4,sK7(X1,X2,k1_xboole_0,sK3))
        | ~ sP1(X1,X2,k1_xboole_0,sK3) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f618,f171])).

fof(f171,plain,(
    ! [X6,X4,X5] :
      ( sP0(sK7(X4,X5,k1_xboole_0,X6),X6,k1_xboole_0)
      | ~ sP1(X4,X5,k1_xboole_0,X6) ) ),
    inference(subsumption_resolution,[],[f168,f48])).

fof(f168,plain,(
    ! [X6,X4,X5] :
      ( ~ sP1(X4,X5,k1_xboole_0,X6)
      | sP0(sK7(X4,X5,k1_xboole_0,X6),X6,k1_xboole_0)
      | ~ v1_funct_1(sK7(X4,X5,k1_xboole_0,X6)) ) ),
    inference(resolution,[],[f49,f56])).

fof(f56,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | sP0(X2,X1,k1_xboole_0)
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f618,plain,
    ( ! [X2,X1] :
        ( ~ r1_partfun1(sK5,sK7(X1,X2,k1_xboole_0,sK3))
        | ~ r1_partfun1(sK4,sK7(X1,X2,k1_xboole_0,sK3))
        | ~ sP0(sK7(X1,X2,k1_xboole_0,sK3),sK3,k1_xboole_0)
        | ~ sP1(X1,X2,k1_xboole_0,sK3) )
    | ~ spl8_2 ),
    inference(superposition,[],[f570,f461])).

fof(f461,plain,(
    ! [X4,X2,X3] :
      ( sK7(X2,X3,k1_xboole_0,X4) = sK6(sK7(X2,X3,k1_xboole_0,X4),X4,k1_xboole_0)
      | ~ sP1(X2,X3,k1_xboole_0,X4) ) ),
    inference(subsumption_resolution,[],[f460,f48])).

fof(f460,plain,(
    ! [X4,X2,X3] :
      ( sK7(X2,X3,k1_xboole_0,X4) = sK6(sK7(X2,X3,k1_xboole_0,X4),X4,k1_xboole_0)
      | ~ v1_funct_1(sK7(X2,X3,k1_xboole_0,X4))
      | ~ sP1(X2,X3,k1_xboole_0,X4) ) ),
    inference(subsumption_resolution,[],[f457,f50])).

fof(f457,plain,(
    ! [X4,X2,X3] :
      ( sK7(X2,X3,k1_xboole_0,X4) = sK6(sK7(X2,X3,k1_xboole_0,X4),X4,k1_xboole_0)
      | ~ v1_partfun1(sK7(X2,X3,k1_xboole_0,X4),k1_xboole_0)
      | ~ v1_funct_1(sK7(X2,X3,k1_xboole_0,X4))
      | ~ sP1(X2,X3,k1_xboole_0,X4) ) ),
    inference(resolution,[],[f420,f49])).

fof(f420,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | sK6(X0,X1,k1_xboole_0) = X0
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f419,f56])).

fof(f419,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X0,k1_xboole_0)
      | sK6(X0,X1,k1_xboole_0) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X0)
      | ~ sP0(X0,X1,k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f416])).

fof(f416,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X0,k1_xboole_0)
      | sK6(X0,X1,k1_xboole_0) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X0)
      | ~ sP0(X0,X1,k1_xboole_0)
      | ~ sP0(X0,X1,k1_xboole_0) ) ),
    inference(resolution,[],[f381,f188])).

fof(f188,plain,(
    ! [X0,X1] :
      ( v1_partfun1(sK6(X0,X1,k1_xboole_0),k1_xboole_0)
      | ~ sP0(X0,X1,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f187,f41])).

fof(f187,plain,(
    ! [X0,X1] :
      ( v1_partfun1(sK6(X0,X1,k1_xboole_0),k1_xboole_0)
      | ~ v1_funct_1(sK6(X0,X1,k1_xboole_0))
      | ~ sP0(X0,X1,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f175,f42])).

fof(f175,plain,(
    ! [X0,X1] :
      ( v1_partfun1(sK6(X0,X1,k1_xboole_0),k1_xboole_0)
      | ~ v1_funct_2(sK6(X0,X1,k1_xboole_0),k1_xboole_0,X1)
      | ~ v1_funct_1(sK6(X0,X1,k1_xboole_0))
      | ~ sP0(X0,X1,k1_xboole_0) ) ),
    inference(resolution,[],[f59,f43])).

fof(f59,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | v1_partfun1(X2,k1_xboole_0)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f55])).

fof(f55,plain,(
    ! [X2,X1] :
      ( v1_partfun1(X2,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f570,plain,
    ( ! [X0] :
        ( ~ r1_partfun1(sK5,sK6(X0,sK3,k1_xboole_0))
        | ~ r1_partfun1(sK4,sK6(X0,sK3,k1_xboole_0))
        | ~ sP0(X0,sK3,k1_xboole_0) )
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f569,f67])).

fof(f569,plain,
    ( ! [X0] :
        ( ~ r1_partfun1(sK4,sK6(X0,sK3,k1_xboole_0))
        | ~ r1_partfun1(sK5,sK6(X0,sK3,k1_xboole_0))
        | ~ sP0(X0,sK3,sK2) )
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f568,f67])).

fof(f568,plain,
    ( ! [X0] :
        ( ~ r1_partfun1(sK5,sK6(X0,sK3,k1_xboole_0))
        | ~ r1_partfun1(sK4,sK6(X0,sK3,sK2))
        | ~ sP0(X0,sK3,sK2) )
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f99,f67])).

fof(f68,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f36,f65,f61])).

fof(f36,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:05:03 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (5483)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.49  % (5476)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.49  % (5479)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.50  % (5480)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.50  % (5497)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.50  % (5496)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.50  % (5474)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.50  % (5481)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.50  % (5479)Refutation not found, incomplete strategy% (5479)------------------------------
% 0.22/0.50  % (5479)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (5479)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (5479)Memory used [KB]: 10618
% 0.22/0.50  % (5479)Time elapsed: 0.095 s
% 0.22/0.50  % (5479)------------------------------
% 0.22/0.50  % (5479)------------------------------
% 0.22/0.50  % (5480)Refutation not found, incomplete strategy% (5480)------------------------------
% 0.22/0.50  % (5480)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (5489)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.50  % (5486)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (5477)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (5485)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.51  % (5478)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (5487)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (5494)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.51  % (5488)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.12/0.51  % (5492)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.12/0.51  % (5495)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.12/0.51  % (5491)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.12/0.51  % (5480)Termination reason: Refutation not found, incomplete strategy
% 1.12/0.51  
% 1.12/0.51  % (5480)Memory used [KB]: 1663
% 1.12/0.51  % (5480)Time elapsed: 0.107 s
% 1.12/0.51  % (5480)------------------------------
% 1.12/0.51  % (5480)------------------------------
% 1.12/0.52  % (5493)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.12/0.52  % (5498)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.27/0.53  % (5490)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.27/0.53  % (5473)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.27/0.53  % (5482)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.27/0.53  % (5484)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.27/0.54  % (5475)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.27/0.54  % (5477)Refutation found. Thanks to Tanya!
% 1.27/0.54  % SZS status Theorem for theBenchmark
% 1.27/0.56  % (5474)Refutation not found, incomplete strategy% (5474)------------------------------
% 1.27/0.56  % (5474)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.56  % SZS output start Proof for theBenchmark
% 1.27/0.56  fof(f997,plain,(
% 1.27/0.56    $false),
% 1.27/0.56    inference(avatar_sat_refutation,[],[f68,f665,f996])).
% 1.27/0.56  fof(f996,plain,(
% 1.27/0.56    spl8_1),
% 1.27/0.56    inference(avatar_contradiction_clause,[],[f995])).
% 1.27/0.56  fof(f995,plain,(
% 1.27/0.56    $false | spl8_1),
% 1.27/0.56    inference(subsumption_resolution,[],[f993,f801])).
% 1.27/0.56  fof(f801,plain,(
% 1.27/0.56    sP1(sK5,sK4,sK2,sK3) | spl8_1),
% 1.27/0.56    inference(subsumption_resolution,[],[f800,f32])).
% 1.27/0.56  fof(f32,plain,(
% 1.27/0.56    v1_funct_1(sK4)),
% 1.27/0.56    inference(cnf_transformation,[],[f23])).
% 1.27/0.56  fof(f23,plain,(
% 1.27/0.56    (! [X4] : (~r1_partfun1(sK5,X4) | ~r1_partfun1(sK4,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~v1_funct_2(X4,sK2,sK3) | ~v1_funct_1(X4)) & r1_partfun1(sK4,sK5) & (k1_xboole_0 = sK2 | k1_xboole_0 != sK3) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_1(sK4)),
% 1.27/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f8,f22,f21])).
% 1.27/0.56  fof(f21,plain,(
% 1.27/0.56    ? [X0,X1,X2] : (? [X3] : (! [X4] : (~r1_partfun1(X3,X4) | ~r1_partfun1(X2,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4)) & r1_partfun1(X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : (! [X4] : (~r1_partfun1(X3,X4) | ~r1_partfun1(sK4,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~v1_funct_2(X4,sK2,sK3) | ~v1_funct_1(X4)) & r1_partfun1(sK4,X3) & (k1_xboole_0 = sK2 | k1_xboole_0 != sK3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_1(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_1(sK4))),
% 1.27/0.56    introduced(choice_axiom,[])).
% 1.27/0.56  fof(f22,plain,(
% 1.27/0.56    ? [X3] : (! [X4] : (~r1_partfun1(X3,X4) | ~r1_partfun1(sK4,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~v1_funct_2(X4,sK2,sK3) | ~v1_funct_1(X4)) & r1_partfun1(sK4,X3) & (k1_xboole_0 = sK2 | k1_xboole_0 != sK3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_1(X3)) => (! [X4] : (~r1_partfun1(sK5,X4) | ~r1_partfun1(sK4,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~v1_funct_2(X4,sK2,sK3) | ~v1_funct_1(X4)) & r1_partfun1(sK4,sK5) & (k1_xboole_0 = sK2 | k1_xboole_0 != sK3) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_1(sK5))),
% 1.27/0.56    introduced(choice_axiom,[])).
% 1.27/0.56  fof(f8,plain,(
% 1.27/0.56    ? [X0,X1,X2] : (? [X3] : (! [X4] : (~r1_partfun1(X3,X4) | ~r1_partfun1(X2,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4)) & r1_partfun1(X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 1.27/0.56    inference(flattening,[],[f7])).
% 1.27/0.56  fof(f7,plain,(
% 1.27/0.56    ? [X0,X1,X2] : (? [X3] : ((! [X4] : ((~r1_partfun1(X3,X4) | ~r1_partfun1(X2,X4)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4))) & r1_partfun1(X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 1.27/0.56    inference(ennf_transformation,[],[f6])).
% 1.27/0.56  fof(f6,negated_conjecture,(
% 1.27/0.56    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4)) => ~(r1_partfun1(X3,X4) & r1_partfun1(X2,X4))) & r1_partfun1(X2,X3) & (k1_xboole_0 = X1 => k1_xboole_0 = X0))))),
% 1.27/0.56    inference(negated_conjecture,[],[f5])).
% 1.27/0.56  fof(f5,conjecture,(
% 1.27/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4)) => ~(r1_partfun1(X3,X4) & r1_partfun1(X2,X4))) & r1_partfun1(X2,X3) & (k1_xboole_0 = X1 => k1_xboole_0 = X0))))),
% 1.27/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_2)).
% 1.27/0.56  fof(f800,plain,(
% 1.27/0.56    sP1(sK5,sK4,sK2,sK3) | ~v1_funct_1(sK4) | spl8_1),
% 1.27/0.56    inference(subsumption_resolution,[],[f796,f37])).
% 1.27/0.56  fof(f37,plain,(
% 1.27/0.56    r1_partfun1(sK4,sK5)),
% 1.27/0.56    inference(cnf_transformation,[],[f23])).
% 1.27/0.56  fof(f796,plain,(
% 1.27/0.56    sP1(sK5,sK4,sK2,sK3) | ~r1_partfun1(sK4,sK5) | ~v1_funct_1(sK4) | spl8_1),
% 1.27/0.56    inference(resolution,[],[f743,f33])).
% 1.27/0.56  fof(f33,plain,(
% 1.27/0.56    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 1.27/0.56    inference(cnf_transformation,[],[f23])).
% 1.27/0.56  fof(f743,plain,(
% 1.27/0.56    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | sP1(sK5,X1,sK2,sK3) | ~r1_partfun1(X1,sK5) | ~v1_funct_1(X1)) ) | spl8_1),
% 1.27/0.56    inference(subsumption_resolution,[],[f742,f34])).
% 1.27/0.56  fof(f34,plain,(
% 1.27/0.56    v1_funct_1(sK5)),
% 1.27/0.56    inference(cnf_transformation,[],[f23])).
% 1.27/0.56  fof(f742,plain,(
% 1.27/0.56    ( ! [X1] : (~r1_partfun1(X1,sK5) | sP1(sK5,X1,sK2,sK3) | ~v1_funct_1(sK5) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~v1_funct_1(X1)) ) | spl8_1),
% 1.27/0.56    inference(subsumption_resolution,[],[f725,f63])).
% 1.27/0.56  fof(f63,plain,(
% 1.27/0.56    k1_xboole_0 != sK3 | spl8_1),
% 1.27/0.56    inference(avatar_component_clause,[],[f61])).
% 1.27/0.56  fof(f61,plain,(
% 1.27/0.56    spl8_1 <=> k1_xboole_0 = sK3),
% 1.27/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.27/0.56  fof(f725,plain,(
% 1.27/0.56    ( ! [X1] : (~r1_partfun1(X1,sK5) | k1_xboole_0 = sK3 | sP1(sK5,X1,sK2,sK3) | ~v1_funct_1(sK5) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~v1_funct_1(X1)) )),
% 1.27/0.56    inference(resolution,[],[f35,f53])).
% 1.27/0.56  fof(f53,plain,(
% 1.27/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_partfun1(X2,X3) | k1_xboole_0 = X1 | sP1(X3,X2,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.27/0.56    inference(cnf_transformation,[],[f20])).
% 1.27/0.56  fof(f20,plain,(
% 1.27/0.56    ! [X0,X1,X2] : (! [X3] : (sP1(X3,X2,X0,X1) | ~r1_partfun1(X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.27/0.56    inference(definition_folding,[],[f16,f19])).
% 1.27/0.56  fof(f19,plain,(
% 1.27/0.56    ! [X3,X2,X0,X1] : (? [X4] : (r1_partfun1(X3,X4) & r1_partfun1(X2,X4) & v1_partfun1(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) | ~sP1(X3,X2,X0,X1))),
% 1.27/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.27/0.56  fof(f16,plain,(
% 1.27/0.56    ! [X0,X1,X2] : (! [X3] : (? [X4] : (r1_partfun1(X3,X4) & r1_partfun1(X2,X4) & v1_partfun1(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) | ~r1_partfun1(X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.27/0.56    inference(flattening,[],[f15])).
% 1.27/0.56  fof(f15,plain,(
% 1.27/0.56    ! [X0,X1,X2] : (! [X3] : ((? [X4] : ((r1_partfun1(X3,X4) & r1_partfun1(X2,X4) & v1_partfun1(X4,X0)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4))) | ~r1_partfun1(X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.27/0.56    inference(ennf_transformation,[],[f4])).
% 1.27/0.56  fof(f4,axiom,(
% 1.27/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => ~(r1_partfun1(X3,X4) & r1_partfun1(X2,X4) & v1_partfun1(X4,X0))) & r1_partfun1(X2,X3) & (k1_xboole_0 = X1 => k1_xboole_0 = X0))))),
% 1.27/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_partfun1)).
% 1.27/0.56  fof(f35,plain,(
% 1.27/0.56    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 1.27/0.56    inference(cnf_transformation,[],[f23])).
% 1.27/0.56  fof(f993,plain,(
% 1.27/0.56    ~sP1(sK5,sK4,sK2,sK3) | spl8_1),
% 1.27/0.56    inference(duplicate_literal_removal,[],[f988])).
% 1.27/0.56  fof(f988,plain,(
% 1.27/0.56    ~sP1(sK5,sK4,sK2,sK3) | ~sP1(sK5,sK4,sK2,sK3) | spl8_1),
% 1.27/0.56    inference(resolution,[],[f984,f51])).
% 1.27/0.56  fof(f51,plain,(
% 1.27/0.56    ( ! [X2,X0,X3,X1] : (r1_partfun1(X1,sK7(X0,X1,X2,X3)) | ~sP1(X0,X1,X2,X3)) )),
% 1.27/0.56    inference(cnf_transformation,[],[f31])).
% 1.27/0.56  fof(f31,plain,(
% 1.27/0.56    ! [X0,X1,X2,X3] : ((r1_partfun1(X0,sK7(X0,X1,X2,X3)) & r1_partfun1(X1,sK7(X0,X1,X2,X3)) & v1_partfun1(sK7(X0,X1,X2,X3),X2) & m1_subset_1(sK7(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(sK7(X0,X1,X2,X3))) | ~sP1(X0,X1,X2,X3))),
% 1.27/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f29,f30])).
% 1.27/0.56  fof(f30,plain,(
% 1.27/0.56    ! [X3,X2,X1,X0] : (? [X4] : (r1_partfun1(X0,X4) & r1_partfun1(X1,X4) & v1_partfun1(X4,X2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X4)) => (r1_partfun1(X0,sK7(X0,X1,X2,X3)) & r1_partfun1(X1,sK7(X0,X1,X2,X3)) & v1_partfun1(sK7(X0,X1,X2,X3),X2) & m1_subset_1(sK7(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(sK7(X0,X1,X2,X3))))),
% 1.27/0.56    introduced(choice_axiom,[])).
% 1.27/0.56  fof(f29,plain,(
% 1.27/0.56    ! [X0,X1,X2,X3] : (? [X4] : (r1_partfun1(X0,X4) & r1_partfun1(X1,X4) & v1_partfun1(X4,X2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X4)) | ~sP1(X0,X1,X2,X3))),
% 1.27/0.56    inference(rectify,[],[f28])).
% 1.27/0.56  fof(f28,plain,(
% 1.27/0.56    ! [X3,X2,X0,X1] : (? [X4] : (r1_partfun1(X3,X4) & r1_partfun1(X2,X4) & v1_partfun1(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) | ~sP1(X3,X2,X0,X1))),
% 1.27/0.56    inference(nnf_transformation,[],[f19])).
% 1.27/0.56  fof(f984,plain,(
% 1.27/0.56    ( ! [X3] : (~r1_partfun1(sK4,sK7(sK5,X3,sK2,sK3)) | ~sP1(sK5,X3,sK2,sK3)) ) | spl8_1),
% 1.27/0.56    inference(duplicate_literal_removal,[],[f979])).
% 1.27/0.56  fof(f979,plain,(
% 1.27/0.56    ( ! [X3] : (~r1_partfun1(sK4,sK7(sK5,X3,sK2,sK3)) | ~sP1(sK5,X3,sK2,sK3) | ~sP1(sK5,X3,sK2,sK3)) ) | spl8_1),
% 1.27/0.56    inference(resolution,[],[f976,f52])).
% 1.27/0.56  fof(f52,plain,(
% 1.27/0.56    ( ! [X2,X0,X3,X1] : (r1_partfun1(X0,sK7(X0,X1,X2,X3)) | ~sP1(X0,X1,X2,X3)) )),
% 1.27/0.56    inference(cnf_transformation,[],[f31])).
% 1.27/0.56  fof(f976,plain,(
% 1.27/0.56    ( ! [X0,X1] : (~r1_partfun1(sK5,sK7(X0,X1,sK2,sK3)) | ~r1_partfun1(sK4,sK7(X0,X1,sK2,sK3)) | ~sP1(X0,X1,sK2,sK3)) ) | spl8_1),
% 1.27/0.56    inference(subsumption_resolution,[],[f975,f63])).
% 1.27/0.56  fof(f975,plain,(
% 1.27/0.56    ( ! [X0,X1] : (~r1_partfun1(sK4,sK7(X0,X1,sK2,sK3)) | ~r1_partfun1(sK5,sK7(X0,X1,sK2,sK3)) | ~sP1(X0,X1,sK2,sK3) | k1_xboole_0 = sK3) ) | spl8_1),
% 1.27/0.56    inference(duplicate_literal_removal,[],[f970])).
% 1.27/0.56  fof(f970,plain,(
% 1.27/0.56    ( ! [X0,X1] : (~r1_partfun1(sK4,sK7(X0,X1,sK2,sK3)) | ~r1_partfun1(sK5,sK7(X0,X1,sK2,sK3)) | ~sP1(X0,X1,sK2,sK3) | k1_xboole_0 = sK3 | ~sP1(X0,X1,sK2,sK3)) ) | spl8_1),
% 1.27/0.56    inference(resolution,[],[f967,f170])).
% 1.27/0.56  fof(f170,plain,(
% 1.27/0.56    ( ! [X2,X0,X3,X1] : (sP0(sK7(X0,X1,X2,X3),X3,X2) | k1_xboole_0 = X3 | ~sP1(X0,X1,X2,X3)) )),
% 1.27/0.56    inference(subsumption_resolution,[],[f167,f48])).
% 1.27/0.56  fof(f48,plain,(
% 1.27/0.56    ( ! [X2,X0,X3,X1] : (v1_funct_1(sK7(X0,X1,X2,X3)) | ~sP1(X0,X1,X2,X3)) )),
% 1.27/0.56    inference(cnf_transformation,[],[f31])).
% 1.27/0.56  fof(f167,plain,(
% 1.27/0.56    ( ! [X2,X0,X3,X1] : (~sP1(X0,X1,X2,X3) | k1_xboole_0 = X3 | sP0(sK7(X0,X1,X2,X3),X3,X2) | ~v1_funct_1(sK7(X0,X1,X2,X3))) )),
% 1.27/0.56    inference(resolution,[],[f49,f45])).
% 1.27/0.56  fof(f45,plain,(
% 1.27/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | sP0(X2,X1,X0) | ~v1_funct_1(X2)) )),
% 1.27/0.56    inference(cnf_transformation,[],[f18])).
% 1.27/0.56  fof(f18,plain,(
% 1.27/0.56    ! [X0,X1,X2] : (sP0(X2,X1,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.27/0.56    inference(definition_folding,[],[f12,f17])).
% 1.27/0.56  fof(f17,plain,(
% 1.27/0.56    ! [X2,X1,X0] : (? [X3] : (r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~sP0(X2,X1,X0))),
% 1.27/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.27/0.56  fof(f12,plain,(
% 1.27/0.56    ! [X0,X1,X2] : (? [X3] : (r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.27/0.56    inference(flattening,[],[f11])).
% 1.27/0.56  fof(f11,plain,(
% 1.27/0.56    ! [X0,X1,X2] : ((? [X3] : (r1_partfun1(X2,X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.27/0.56    inference(ennf_transformation,[],[f2])).
% 1.27/0.56  fof(f2,axiom,(
% 1.27/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ~r1_partfun1(X2,X3)) & (k1_xboole_0 = X1 => k1_xboole_0 = X0)))),
% 1.27/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_2)).
% 1.27/0.56  fof(f49,plain,(
% 1.27/0.56    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK7(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~sP1(X0,X1,X2,X3)) )),
% 1.27/0.56    inference(cnf_transformation,[],[f31])).
% 1.27/0.56  fof(f967,plain,(
% 1.27/0.56    ( ! [X61,X62] : (~sP0(sK7(X61,X62,sK2,sK3),sK3,sK2) | ~r1_partfun1(sK4,sK7(X61,X62,sK2,sK3)) | ~r1_partfun1(sK5,sK7(X61,X62,sK2,sK3)) | ~sP1(X61,X62,sK2,sK3)) ) | spl8_1),
% 1.27/0.56    inference(subsumption_resolution,[],[f948,f63])).
% 1.27/0.56  fof(f948,plain,(
% 1.27/0.56    ( ! [X61,X62] : (~r1_partfun1(sK5,sK7(X61,X62,sK2,sK3)) | ~r1_partfun1(sK4,sK7(X61,X62,sK2,sK3)) | ~sP0(sK7(X61,X62,sK2,sK3),sK3,sK2) | k1_xboole_0 = sK3 | ~sP1(X61,X62,sK2,sK3)) )),
% 1.27/0.56    inference(superposition,[],[f99,f473])).
% 1.27/0.56  fof(f473,plain,(
% 1.27/0.56    ( ! [X6,X4,X5,X3] : (sK7(X3,X4,X5,X6) = sK6(sK7(X3,X4,X5,X6),X6,X5) | k1_xboole_0 = X6 | ~sP1(X3,X4,X5,X6)) )),
% 1.27/0.56    inference(subsumption_resolution,[],[f472,f48])).
% 1.27/0.56  fof(f472,plain,(
% 1.27/0.56    ( ! [X6,X4,X5,X3] : (sK7(X3,X4,X5,X6) = sK6(sK7(X3,X4,X5,X6),X6,X5) | ~v1_funct_1(sK7(X3,X4,X5,X6)) | k1_xboole_0 = X6 | ~sP1(X3,X4,X5,X6)) )),
% 1.27/0.56    inference(subsumption_resolution,[],[f469,f50])).
% 1.27/0.56  fof(f50,plain,(
% 1.27/0.56    ( ! [X2,X0,X3,X1] : (v1_partfun1(sK7(X0,X1,X2,X3),X2) | ~sP1(X0,X1,X2,X3)) )),
% 1.27/0.56    inference(cnf_transformation,[],[f31])).
% 1.27/0.56  fof(f469,plain,(
% 1.27/0.56    ( ! [X6,X4,X5,X3] : (sK7(X3,X4,X5,X6) = sK6(sK7(X3,X4,X5,X6),X6,X5) | ~v1_partfun1(sK7(X3,X4,X5,X6),X5) | ~v1_funct_1(sK7(X3,X4,X5,X6)) | k1_xboole_0 = X6 | ~sP1(X3,X4,X5,X6)) )),
% 1.27/0.56    inference(resolution,[],[f421,f49])).
% 1.27/0.56  fof(f421,plain,(
% 1.27/0.56    ( ! [X4,X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | sK6(X2,X4,X3) = X2 | ~v1_partfun1(X2,X3) | ~v1_funct_1(X2) | k1_xboole_0 = X4) )),
% 1.27/0.56    inference(subsumption_resolution,[],[f418,f45])).
% 1.27/0.56  fof(f418,plain,(
% 1.27/0.56    ( ! [X4,X2,X3] : (~v1_partfun1(X2,X3) | sK6(X2,X4,X3) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X2) | ~sP0(X2,X4,X3) | k1_xboole_0 = X4) )),
% 1.27/0.56    inference(duplicate_literal_removal,[],[f417])).
% 1.27/0.56  fof(f417,plain,(
% 1.27/0.56    ( ! [X4,X2,X3] : (~v1_partfun1(X2,X3) | sK6(X2,X4,X3) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X2) | ~sP0(X2,X4,X3) | k1_xboole_0 = X4 | ~sP0(X2,X4,X3)) )),
% 1.27/0.56    inference(resolution,[],[f381,f194])).
% 1.27/0.56  fof(f194,plain,(
% 1.27/0.56    ( ! [X2,X0,X1] : (v1_partfun1(sK6(X1,X0,X2),X2) | k1_xboole_0 = X0 | ~sP0(X1,X0,X2)) )),
% 1.27/0.56    inference(subsumption_resolution,[],[f193,f41])).
% 1.27/0.56  fof(f41,plain,(
% 1.27/0.56    ( ! [X2,X0,X1] : (v1_funct_1(sK6(X0,X1,X2)) | ~sP0(X0,X1,X2)) )),
% 1.27/0.56    inference(cnf_transformation,[],[f27])).
% 1.27/0.56  fof(f27,plain,(
% 1.27/0.56    ! [X0,X1,X2] : ((r1_partfun1(X0,sK6(X0,X1,X2)) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK6(X0,X1,X2),X2,X1) & v1_funct_1(sK6(X0,X1,X2))) | ~sP0(X0,X1,X2))),
% 1.27/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f25,f26])).
% 1.27/0.56  fof(f26,plain,(
% 1.27/0.56    ! [X2,X1,X0] : (? [X3] : (r1_partfun1(X0,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X3,X2,X1) & v1_funct_1(X3)) => (r1_partfun1(X0,sK6(X0,X1,X2)) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK6(X0,X1,X2),X2,X1) & v1_funct_1(sK6(X0,X1,X2))))),
% 1.27/0.56    introduced(choice_axiom,[])).
% 1.27/0.56  fof(f25,plain,(
% 1.27/0.56    ! [X0,X1,X2] : (? [X3] : (r1_partfun1(X0,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X3,X2,X1) & v1_funct_1(X3)) | ~sP0(X0,X1,X2))),
% 1.27/0.56    inference(rectify,[],[f24])).
% 1.27/0.56  fof(f24,plain,(
% 1.27/0.56    ! [X2,X1,X0] : (? [X3] : (r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~sP0(X2,X1,X0))),
% 1.27/0.56    inference(nnf_transformation,[],[f17])).
% 1.27/0.56  fof(f193,plain,(
% 1.27/0.56    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | v1_partfun1(sK6(X1,X0,X2),X2) | ~v1_funct_1(sK6(X1,X0,X2)) | ~sP0(X1,X0,X2)) )),
% 1.27/0.56    inference(subsumption_resolution,[],[f191,f42])).
% 1.27/0.56  fof(f42,plain,(
% 1.27/0.56    ( ! [X2,X0,X1] : (v1_funct_2(sK6(X0,X1,X2),X2,X1) | ~sP0(X0,X1,X2)) )),
% 1.27/0.56    inference(cnf_transformation,[],[f27])).
% 1.27/0.56  fof(f191,plain,(
% 1.27/0.56    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | v1_partfun1(sK6(X1,X0,X2),X2) | ~v1_funct_2(sK6(X1,X0,X2),X2,X0) | ~v1_funct_1(sK6(X1,X0,X2)) | ~sP0(X1,X0,X2)) )),
% 1.27/0.56    inference(resolution,[],[f58,f43])).
% 1.27/0.56  fof(f43,plain,(
% 1.27/0.56    ( ! [X2,X0,X1] : (m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~sP0(X0,X1,X2)) )),
% 1.27/0.56    inference(cnf_transformation,[],[f27])).
% 1.27/0.56  fof(f58,plain,(
% 1.27/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.27/0.56    inference(duplicate_literal_removal,[],[f39])).
% 1.27/0.56  fof(f39,plain,(
% 1.27/0.56    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.27/0.56    inference(cnf_transformation,[],[f10])).
% 1.27/0.56  fof(f10,plain,(
% 1.27/0.56    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.27/0.56    inference(flattening,[],[f9])).
% 1.27/0.56  fof(f9,plain,(
% 1.27/0.56    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.27/0.56    inference(ennf_transformation,[],[f1])).
% 1.27/0.56  fof(f1,axiom,(
% 1.27/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.27/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).
% 1.27/0.57  % (5474)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.57  
% 1.27/0.57  % (5474)Memory used [KB]: 11001
% 1.27/0.57  % (5474)Time elapsed: 0.154 s
% 1.27/0.57  % (5474)------------------------------
% 1.27/0.57  % (5474)------------------------------
% 1.27/0.57  fof(f381,plain,(
% 1.27/0.57    ( ! [X2,X0,X1] : (~v1_partfun1(sK6(X0,X1,X2),X2) | ~v1_partfun1(X0,X2) | sK6(X0,X1,X2) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X0) | ~sP0(X0,X1,X2)) )),
% 1.27/0.57    inference(duplicate_literal_removal,[],[f380])).
% 1.27/0.57  fof(f380,plain,(
% 1.27/0.57    ( ! [X2,X0,X1] : (~v1_partfun1(sK6(X0,X1,X2),X2) | ~v1_partfun1(X0,X2) | sK6(X0,X1,X2) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X0) | ~sP0(X0,X1,X2) | ~sP0(X0,X1,X2)) )),
% 1.27/0.57    inference(resolution,[],[f253,f44])).
% 1.27/0.57  fof(f44,plain,(
% 1.27/0.57    ( ! [X2,X0,X1] : (r1_partfun1(X0,sK6(X0,X1,X2)) | ~sP0(X0,X1,X2)) )),
% 1.27/0.57    inference(cnf_transformation,[],[f27])).
% 1.27/0.57  fof(f253,plain,(
% 1.27/0.57    ( ! [X4,X2,X5,X3] : (~r1_partfun1(X2,sK6(X3,X4,X5)) | ~v1_partfun1(sK6(X3,X4,X5),X5) | ~v1_partfun1(X2,X5) | sK6(X3,X4,X5) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X4))) | ~v1_funct_1(X2) | ~sP0(X3,X4,X5)) )),
% 1.27/0.57    inference(subsumption_resolution,[],[f237,f41])).
% 1.27/0.57  fof(f237,plain,(
% 1.27/0.57    ( ! [X4,X2,X5,X3] : (~r1_partfun1(X2,sK6(X3,X4,X5)) | ~v1_partfun1(sK6(X3,X4,X5),X5) | ~v1_partfun1(X2,X5) | sK6(X3,X4,X5) = X2 | ~v1_funct_1(sK6(X3,X4,X5)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X4))) | ~v1_funct_1(X2) | ~sP0(X3,X4,X5)) )),
% 1.27/0.57    inference(resolution,[],[f47,f43])).
% 1.27/0.57  fof(f47,plain,(
% 1.27/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | X2 = X3 | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.27/0.57    inference(cnf_transformation,[],[f14])).
% 1.27/0.57  fof(f14,plain,(
% 1.27/0.57    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.27/0.57    inference(flattening,[],[f13])).
% 1.27/0.57  fof(f13,plain,(
% 1.27/0.57    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.27/0.57    inference(ennf_transformation,[],[f3])).
% 1.27/0.57  fof(f3,axiom,(
% 1.27/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 1.27/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).
% 1.27/0.57  fof(f99,plain,(
% 1.27/0.57    ( ! [X0] : (~r1_partfun1(sK5,sK6(X0,sK3,sK2)) | ~r1_partfun1(sK4,sK6(X0,sK3,sK2)) | ~sP0(X0,sK3,sK2)) )),
% 1.27/0.57    inference(subsumption_resolution,[],[f98,f41])).
% 1.27/0.57  fof(f98,plain,(
% 1.27/0.57    ( ! [X0] : (~sP0(X0,sK3,sK2) | ~r1_partfun1(sK4,sK6(X0,sK3,sK2)) | ~r1_partfun1(sK5,sK6(X0,sK3,sK2)) | ~v1_funct_1(sK6(X0,sK3,sK2))) )),
% 1.27/0.57    inference(subsumption_resolution,[],[f96,f42])).
% 1.27/0.57  fof(f96,plain,(
% 1.27/0.57    ( ! [X0] : (~sP0(X0,sK3,sK2) | ~r1_partfun1(sK4,sK6(X0,sK3,sK2)) | ~r1_partfun1(sK5,sK6(X0,sK3,sK2)) | ~v1_funct_2(sK6(X0,sK3,sK2),sK2,sK3) | ~v1_funct_1(sK6(X0,sK3,sK2))) )),
% 1.27/0.57    inference(resolution,[],[f43,f38])).
% 1.27/0.57  fof(f38,plain,(
% 1.27/0.57    ( ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~r1_partfun1(sK4,X4) | ~r1_partfun1(sK5,X4) | ~v1_funct_2(X4,sK2,sK3) | ~v1_funct_1(X4)) )),
% 1.27/0.57    inference(cnf_transformation,[],[f23])).
% 1.27/0.57  fof(f665,plain,(
% 1.27/0.57    ~spl8_2),
% 1.27/0.57    inference(avatar_contradiction_clause,[],[f664])).
% 1.27/0.57  fof(f664,plain,(
% 1.27/0.57    $false | ~spl8_2),
% 1.27/0.57    inference(subsumption_resolution,[],[f663,f631])).
% 1.27/0.57  fof(f631,plain,(
% 1.27/0.57    sP1(sK5,sK4,k1_xboole_0,sK3) | ~spl8_2),
% 1.27/0.57    inference(subsumption_resolution,[],[f630,f32])).
% 1.27/0.57  fof(f630,plain,(
% 1.27/0.57    sP1(sK5,sK4,k1_xboole_0,sK3) | ~v1_funct_1(sK4) | ~spl8_2),
% 1.27/0.57    inference(subsumption_resolution,[],[f626,f37])).
% 1.27/0.57  fof(f626,plain,(
% 1.27/0.57    sP1(sK5,sK4,k1_xboole_0,sK3) | ~r1_partfun1(sK4,sK5) | ~v1_funct_1(sK4) | ~spl8_2),
% 1.27/0.57    inference(resolution,[],[f591,f575])).
% 1.27/0.57  fof(f575,plain,(
% 1.27/0.57    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) | ~spl8_2),
% 1.27/0.57    inference(forward_demodulation,[],[f33,f67])).
% 1.27/0.57  fof(f67,plain,(
% 1.27/0.57    k1_xboole_0 = sK2 | ~spl8_2),
% 1.27/0.57    inference(avatar_component_clause,[],[f65])).
% 1.27/0.57  fof(f65,plain,(
% 1.27/0.57    spl8_2 <=> k1_xboole_0 = sK2),
% 1.27/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.27/0.57  fof(f591,plain,(
% 1.27/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) | sP1(sK5,X0,k1_xboole_0,sK3) | ~r1_partfun1(X0,sK5) | ~v1_funct_1(X0)) ) | ~spl8_2),
% 1.27/0.57    inference(subsumption_resolution,[],[f578,f34])).
% 1.27/0.57  fof(f578,plain,(
% 1.27/0.57    ( ! [X0] : (~r1_partfun1(X0,sK5) | sP1(sK5,X0,k1_xboole_0,sK3) | ~v1_funct_1(sK5) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) | ~v1_funct_1(X0)) ) | ~spl8_2),
% 1.27/0.57    inference(resolution,[],[f574,f57])).
% 1.27/0.57  fof(f57,plain,(
% 1.27/0.57    ( ! [X2,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~r1_partfun1(X2,X3) | sP1(X3,X2,k1_xboole_0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X2)) )),
% 1.27/0.57    inference(equality_resolution,[],[f54])).
% 1.27/0.57  fof(f54,plain,(
% 1.27/0.57    ( ! [X2,X0,X3,X1] : (sP1(X3,X2,X0,X1) | ~r1_partfun1(X2,X3) | k1_xboole_0 != X0 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.27/0.57    inference(cnf_transformation,[],[f20])).
% 1.27/0.57  fof(f574,plain,(
% 1.27/0.57    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) | ~spl8_2),
% 1.27/0.57    inference(forward_demodulation,[],[f35,f67])).
% 1.27/0.57  fof(f663,plain,(
% 1.27/0.57    ~sP1(sK5,sK4,k1_xboole_0,sK3) | ~spl8_2),
% 1.27/0.57    inference(duplicate_literal_removal,[],[f658])).
% 1.27/0.57  fof(f658,plain,(
% 1.27/0.57    ~sP1(sK5,sK4,k1_xboole_0,sK3) | ~sP1(sK5,sK4,k1_xboole_0,sK3) | ~spl8_2),
% 1.27/0.57    inference(resolution,[],[f656,f51])).
% 1.27/0.57  fof(f656,plain,(
% 1.27/0.57    ( ! [X1] : (~r1_partfun1(sK4,sK7(sK5,X1,k1_xboole_0,sK3)) | ~sP1(sK5,X1,k1_xboole_0,sK3)) ) | ~spl8_2),
% 1.27/0.57    inference(duplicate_literal_removal,[],[f651])).
% 1.27/0.57  fof(f651,plain,(
% 1.27/0.57    ( ! [X1] : (~r1_partfun1(sK4,sK7(sK5,X1,k1_xboole_0,sK3)) | ~sP1(sK5,X1,k1_xboole_0,sK3) | ~sP1(sK5,X1,k1_xboole_0,sK3)) ) | ~spl8_2),
% 1.27/0.57    inference(resolution,[],[f620,f52])).
% 1.27/0.57  fof(f620,plain,(
% 1.27/0.57    ( ! [X2,X1] : (~r1_partfun1(sK5,sK7(X1,X2,k1_xboole_0,sK3)) | ~r1_partfun1(sK4,sK7(X1,X2,k1_xboole_0,sK3)) | ~sP1(X1,X2,k1_xboole_0,sK3)) ) | ~spl8_2),
% 1.27/0.57    inference(subsumption_resolution,[],[f618,f171])).
% 1.27/0.57  fof(f171,plain,(
% 1.27/0.57    ( ! [X6,X4,X5] : (sP0(sK7(X4,X5,k1_xboole_0,X6),X6,k1_xboole_0) | ~sP1(X4,X5,k1_xboole_0,X6)) )),
% 1.27/0.57    inference(subsumption_resolution,[],[f168,f48])).
% 1.27/0.57  fof(f168,plain,(
% 1.27/0.57    ( ! [X6,X4,X5] : (~sP1(X4,X5,k1_xboole_0,X6) | sP0(sK7(X4,X5,k1_xboole_0,X6),X6,k1_xboole_0) | ~v1_funct_1(sK7(X4,X5,k1_xboole_0,X6))) )),
% 1.27/0.57    inference(resolution,[],[f49,f56])).
% 1.27/0.57  fof(f56,plain,(
% 1.27/0.57    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | sP0(X2,X1,k1_xboole_0) | ~v1_funct_1(X2)) )),
% 1.27/0.57    inference(equality_resolution,[],[f46])).
% 1.27/0.57  fof(f46,plain,(
% 1.27/0.57    ( ! [X2,X0,X1] : (sP0(X2,X1,X0) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.27/0.57    inference(cnf_transformation,[],[f18])).
% 1.27/0.57  fof(f618,plain,(
% 1.27/0.57    ( ! [X2,X1] : (~r1_partfun1(sK5,sK7(X1,X2,k1_xboole_0,sK3)) | ~r1_partfun1(sK4,sK7(X1,X2,k1_xboole_0,sK3)) | ~sP0(sK7(X1,X2,k1_xboole_0,sK3),sK3,k1_xboole_0) | ~sP1(X1,X2,k1_xboole_0,sK3)) ) | ~spl8_2),
% 1.27/0.57    inference(superposition,[],[f570,f461])).
% 1.27/0.57  fof(f461,plain,(
% 1.27/0.57    ( ! [X4,X2,X3] : (sK7(X2,X3,k1_xboole_0,X4) = sK6(sK7(X2,X3,k1_xboole_0,X4),X4,k1_xboole_0) | ~sP1(X2,X3,k1_xboole_0,X4)) )),
% 1.27/0.57    inference(subsumption_resolution,[],[f460,f48])).
% 1.27/0.57  fof(f460,plain,(
% 1.27/0.57    ( ! [X4,X2,X3] : (sK7(X2,X3,k1_xboole_0,X4) = sK6(sK7(X2,X3,k1_xboole_0,X4),X4,k1_xboole_0) | ~v1_funct_1(sK7(X2,X3,k1_xboole_0,X4)) | ~sP1(X2,X3,k1_xboole_0,X4)) )),
% 1.27/0.57    inference(subsumption_resolution,[],[f457,f50])).
% 1.27/0.57  fof(f457,plain,(
% 1.27/0.57    ( ! [X4,X2,X3] : (sK7(X2,X3,k1_xboole_0,X4) = sK6(sK7(X2,X3,k1_xboole_0,X4),X4,k1_xboole_0) | ~v1_partfun1(sK7(X2,X3,k1_xboole_0,X4),k1_xboole_0) | ~v1_funct_1(sK7(X2,X3,k1_xboole_0,X4)) | ~sP1(X2,X3,k1_xboole_0,X4)) )),
% 1.27/0.57    inference(resolution,[],[f420,f49])).
% 1.27/0.57  fof(f420,plain,(
% 1.27/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | sK6(X0,X1,k1_xboole_0) = X0 | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0)) )),
% 1.27/0.57    inference(subsumption_resolution,[],[f419,f56])).
% 1.27/0.57  fof(f419,plain,(
% 1.27/0.57    ( ! [X0,X1] : (~v1_partfun1(X0,k1_xboole_0) | sK6(X0,X1,k1_xboole_0) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X0) | ~sP0(X0,X1,k1_xboole_0)) )),
% 1.27/0.57    inference(duplicate_literal_removal,[],[f416])).
% 1.27/0.57  fof(f416,plain,(
% 1.27/0.57    ( ! [X0,X1] : (~v1_partfun1(X0,k1_xboole_0) | sK6(X0,X1,k1_xboole_0) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X0) | ~sP0(X0,X1,k1_xboole_0) | ~sP0(X0,X1,k1_xboole_0)) )),
% 1.27/0.57    inference(resolution,[],[f381,f188])).
% 1.27/0.57  fof(f188,plain,(
% 1.27/0.57    ( ! [X0,X1] : (v1_partfun1(sK6(X0,X1,k1_xboole_0),k1_xboole_0) | ~sP0(X0,X1,k1_xboole_0)) )),
% 1.27/0.57    inference(subsumption_resolution,[],[f187,f41])).
% 1.27/0.57  fof(f187,plain,(
% 1.27/0.57    ( ! [X0,X1] : (v1_partfun1(sK6(X0,X1,k1_xboole_0),k1_xboole_0) | ~v1_funct_1(sK6(X0,X1,k1_xboole_0)) | ~sP0(X0,X1,k1_xboole_0)) )),
% 1.27/0.57    inference(subsumption_resolution,[],[f175,f42])).
% 1.27/0.57  fof(f175,plain,(
% 1.27/0.57    ( ! [X0,X1] : (v1_partfun1(sK6(X0,X1,k1_xboole_0),k1_xboole_0) | ~v1_funct_2(sK6(X0,X1,k1_xboole_0),k1_xboole_0,X1) | ~v1_funct_1(sK6(X0,X1,k1_xboole_0)) | ~sP0(X0,X1,k1_xboole_0)) )),
% 1.27/0.57    inference(resolution,[],[f59,f43])).
% 1.27/0.57  fof(f59,plain,(
% 1.27/0.57    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_partfun1(X2,k1_xboole_0) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2)) )),
% 1.27/0.57    inference(duplicate_literal_removal,[],[f55])).
% 1.27/0.57  fof(f55,plain,(
% 1.27/0.57    ( ! [X2,X1] : (v1_partfun1(X2,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X2)) )),
% 1.27/0.57    inference(equality_resolution,[],[f40])).
% 1.27/0.57  fof(f40,plain,(
% 1.27/0.57    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.27/0.57    inference(cnf_transformation,[],[f10])).
% 1.27/0.57  fof(f570,plain,(
% 1.27/0.57    ( ! [X0] : (~r1_partfun1(sK5,sK6(X0,sK3,k1_xboole_0)) | ~r1_partfun1(sK4,sK6(X0,sK3,k1_xboole_0)) | ~sP0(X0,sK3,k1_xboole_0)) ) | ~spl8_2),
% 1.27/0.57    inference(forward_demodulation,[],[f569,f67])).
% 1.27/0.57  fof(f569,plain,(
% 1.27/0.57    ( ! [X0] : (~r1_partfun1(sK4,sK6(X0,sK3,k1_xboole_0)) | ~r1_partfun1(sK5,sK6(X0,sK3,k1_xboole_0)) | ~sP0(X0,sK3,sK2)) ) | ~spl8_2),
% 1.27/0.57    inference(forward_demodulation,[],[f568,f67])).
% 1.27/0.57  fof(f568,plain,(
% 1.27/0.57    ( ! [X0] : (~r1_partfun1(sK5,sK6(X0,sK3,k1_xboole_0)) | ~r1_partfun1(sK4,sK6(X0,sK3,sK2)) | ~sP0(X0,sK3,sK2)) ) | ~spl8_2),
% 1.27/0.57    inference(forward_demodulation,[],[f99,f67])).
% 1.27/0.57  fof(f68,plain,(
% 1.27/0.57    ~spl8_1 | spl8_2),
% 1.27/0.57    inference(avatar_split_clause,[],[f36,f65,f61])).
% 1.27/0.57  fof(f36,plain,(
% 1.27/0.57    k1_xboole_0 = sK2 | k1_xboole_0 != sK3),
% 1.27/0.57    inference(cnf_transformation,[],[f23])).
% 1.27/0.57  % SZS output end Proof for theBenchmark
% 1.27/0.57  % (5477)------------------------------
% 1.27/0.57  % (5477)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.57  % (5477)Termination reason: Refutation
% 1.27/0.57  
% 1.27/0.57  % (5477)Memory used [KB]: 6524
% 1.27/0.57  % (5477)Time elapsed: 0.137 s
% 1.27/0.57  % (5477)------------------------------
% 1.27/0.57  % (5477)------------------------------
% 1.27/0.57  % (5472)Success in time 0.202 s
%------------------------------------------------------------------------------
