%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:02 EST 2020

% Result     : Theorem 3.06s
% Output     : Refutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 693 expanded)
%              Number of leaves         :   25 ( 225 expanded)
%              Depth                    :   22
%              Number of atoms          :  580 (2396 expanded)
%              Number of equality atoms :  148 ( 765 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3371,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f191,f359,f369,f403,f437,f541,f578,f665,f3370])).

fof(f3370,plain,
    ( spl5_6
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | spl5_11 ),
    inference(avatar_contradiction_clause,[],[f3369])).

fof(f3369,plain,
    ( $false
    | spl5_6
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | spl5_11 ),
    inference(subsumption_resolution,[],[f3360,f71])).

fof(f71,plain,(
    k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2) != k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f45,f70,f70])).

fof(f70,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f46,f69])).

fof(f69,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f47,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f47,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f46,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f45,plain,(
    k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    & v1_funct_2(sK3,sK0,k1_tarski(sK1))
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f32,f31])).

fof(f31,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2)
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

fof(f32,plain,
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

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
              & v1_funct_2(X3,X0,k1_tarski(X1))
              & v1_funct_1(X3) )
           => k1_tarski(X3) = k5_partfun1(X0,k1_tarski(X1),X2) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
         => k1_tarski(X3) = k5_partfun1(X0,k1_tarski(X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_2)).

fof(f3360,plain,
    ( k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2) = k2_enumset1(sK3,sK3,sK3,sK3)
    | spl5_6
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | spl5_11 ),
    inference(equality_resolution,[],[f3284])).

fof(f3284,plain,
    ( ! [X6] :
        ( sK3 != X6
        | k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2) = k2_enumset1(X6,X6,X6,X6) )
    | spl5_6
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | spl5_11 ),
    inference(subsumption_resolution,[],[f3105,f158])).

fof(f158,plain,
    ( k1_xboole_0 != k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl5_6
  <=> k1_xboole_0 = k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f3105,plain,
    ( ! [X6] :
        ( sK3 != X6
        | k1_xboole_0 = k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2)
        | k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2) = k2_enumset1(X6,X6,X6,X6) )
    | spl5_6
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | spl5_11 ),
    inference(duplicate_literal_removal,[],[f3084])).

fof(f3084,plain,
    ( ! [X6] :
        ( sK3 != X6
        | k1_xboole_0 = k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2)
        | k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2) = k2_enumset1(X6,X6,X6,X6)
        | k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2) = k2_enumset1(X6,X6,X6,X6) )
    | spl5_6
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | spl5_11 ),
    inference(superposition,[],[f75,f2960])).

fof(f2960,plain,
    ( ! [X4] :
        ( k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2) = k2_enumset1(X4,X4,X4,X4)
        | sK3 = sK4(k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2),X4) )
    | spl5_6
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | spl5_11 ),
    inference(subsumption_resolution,[],[f2959,f873])).

fof(f873,plain,
    ( ! [X12] :
        ( v1_partfun1(sK4(k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2),X12),sK0)
        | k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2) = k2_enumset1(X12,X12,X12,X12) )
    | spl5_6
    | ~ spl5_7
    | ~ spl5_9
    | spl5_11 ),
    inference(subsumption_resolution,[],[f872,f402])).

fof(f402,plain,
    ( ! [X0] :
        ( v1_funct_2(sK4(k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2),X0),sK0,k2_enumset1(sK1,sK1,sK1,sK1))
        | k2_enumset1(X0,X0,X0,X0) = k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2) )
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f401])).

fof(f401,plain,
    ( spl5_9
  <=> ! [X0] :
        ( v1_funct_2(sK4(k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2),X0),sK0,k2_enumset1(sK1,sK1,sK1,sK1))
        | k2_enumset1(X0,X0,X0,X0) = k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f872,plain,
    ( ! [X12] :
        ( k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2) = k2_enumset1(X12,X12,X12,X12)
        | v1_partfun1(sK4(k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2),X12),sK0)
        | ~ v1_funct_2(sK4(k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2),X12),sK0,k2_enumset1(sK1,sK1,sK1,sK1)) )
    | spl5_6
    | ~ spl5_7
    | spl5_11 ),
    inference(subsumption_resolution,[],[f871,f162])).

fof(f162,plain,
    ( ! [X0] :
        ( v1_funct_1(sK4(k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2),X0))
        | k2_enumset1(X0,X0,X0,X0) = k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2) )
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl5_7
  <=> ! [X0] :
        ( v1_funct_1(sK4(k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2),X0))
        | k2_enumset1(X0,X0,X0,X0) = k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f871,plain,
    ( ! [X12] :
        ( k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2) = k2_enumset1(X12,X12,X12,X12)
        | v1_partfun1(sK4(k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2),X12),sK0)
        | ~ v1_funct_2(sK4(k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2),X12),sK0,k2_enumset1(sK1,sK1,sK1,sK1))
        | ~ v1_funct_1(sK4(k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2),X12)) )
    | spl5_6
    | spl5_11 ),
    inference(subsumption_resolution,[],[f858,f435])).

fof(f435,plain,
    ( k1_xboole_0 != k2_enumset1(sK1,sK1,sK1,sK1)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f434])).

fof(f434,plain,
    ( spl5_11
  <=> k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f858,plain,
    ( ! [X12] :
        ( k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2) = k2_enumset1(X12,X12,X12,X12)
        | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
        | v1_partfun1(sK4(k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2),X12),sK0)
        | ~ v1_funct_2(sK4(k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2),X12),sK0,k2_enumset1(sK1,sK1,sK1,sK1))
        | ~ v1_funct_1(sK4(k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2),X12)) )
    | spl5_6 ),
    inference(resolution,[],[f760,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f55])).

fof(f55,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f760,plain,
    ( ! [X0] :
        ( m1_subset_1(sK4(k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2),X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1))))
        | k2_enumset1(X0,X0,X0,X0) = k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2) )
    | spl5_6 ),
    inference(subsumption_resolution,[],[f759,f158])).

fof(f759,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2),X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1))))
      | k1_xboole_0 = k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2)
      | k2_enumset1(X0,X0,X0,X0) = k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ) ),
    inference(resolution,[],[f455,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f51,f70])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( sK4(X0,X1) != X1
        & r2_hidden(sK4(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK4(X0,X1) != X1
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).

fof(f455,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2))
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))) ) ),
    inference(subsumption_resolution,[],[f450,f40])).

fof(f40,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f450,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2))
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1))))
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f59,f74])).

fof(f74,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))) ),
    inference(definition_unfolding,[],[f41,f70])).

fof(f41,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f33])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
         => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_2)).

fof(f2959,plain,
    ( ! [X4] :
        ( k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2) = k2_enumset1(X4,X4,X4,X4)
        | sK3 = sK4(k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2),X4)
        | ~ v1_partfun1(sK4(k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2),X4),sK0) )
    | spl5_6
    | ~ spl5_7
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f2938,f162])).

fof(f2938,plain,
    ( ! [X4] :
        ( k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2) = k2_enumset1(X4,X4,X4,X4)
        | sK3 = sK4(k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2),X4)
        | ~ v1_partfun1(sK4(k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2),X4),sK0)
        | ~ v1_funct_1(sK4(k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2),X4)) )
    | spl5_6
    | ~ spl5_10 ),
    inference(resolution,[],[f760,f510])).

fof(f510,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1))))
        | sK3 = X0
        | ~ v1_partfun1(X0,sK0)
        | ~ v1_funct_1(X0) )
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f509,f463])).

fof(f463,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1))))
      | r1_partfun1(X0,sK3)
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f460,f42])).

fof(f42,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f460,plain,(
    ! [X0] :
      ( r1_partfun1(X0,sK3)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1))))
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f78,f72])).

fof(f72,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))) ),
    inference(definition_unfolding,[],[f44,f70])).

fof(f44,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f33])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1))))
      | r1_partfun1(X2,X3)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_unfolding,[],[f63,f70,f70])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_1(X3) )
         => r1_partfun1(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_partfun1)).

fof(f509,plain,
    ( ! [X0] :
        ( ~ r1_partfun1(X0,sK3)
        | ~ v1_partfun1(X0,sK0)
        | sK3 = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1))))
        | ~ v1_funct_1(X0) )
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f508,f42])).

fof(f508,plain,
    ( ! [X0] :
        ( ~ r1_partfun1(X0,sK3)
        | ~ v1_partfun1(X0,sK0)
        | sK3 = X0
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1))))
        | ~ v1_funct_1(X0) )
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f475,f432])).

fof(f432,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f430])).

fof(f430,plain,
    ( spl5_10
  <=> v1_partfun1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f475,plain,(
    ! [X0] :
      ( ~ r1_partfun1(X0,sK3)
      | ~ v1_partfun1(sK3,sK0)
      | ~ v1_partfun1(X0,sK0)
      | sK3 = X0
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1))))
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f62,f72])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_partfun1(X2,X3)
      | ~ v1_partfun1(X3,X0)
      | ~ v1_partfun1(X2,X0)
      | X2 = X3
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f75,plain,(
    ! [X0,X1] :
      ( sK4(X0,X1) != X1
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f52,f70])).

fof(f52,plain,(
    ! [X0,X1] :
      ( sK4(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f665,plain,
    ( ~ spl5_6
    | ~ spl5_22 ),
    inference(avatar_contradiction_clause,[],[f664])).

fof(f664,plain,
    ( $false
    | ~ spl5_6
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f663,f111])).

fof(f111,plain,(
    ! [X4] : ~ r2_hidden(X4,k1_xboole_0) ),
    inference(resolution,[],[f108,f99])).

fof(f99,plain,(
    ! [X0] : ~ r2_hidden(k4_tarski(X0,k2_enumset1(sK3,sK3,sK3,sK3)),k1_xboole_0) ),
    inference(extensionality_resolution,[],[f98,f71])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),k1_xboole_0)
      | X0 = X2 ) ),
    inference(superposition,[],[f82,f85])).

fof(f85,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))
      | X1 = X3 ) ),
    inference(definition_unfolding,[],[f67,f70])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <=> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

fof(f108,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,X0),k1_xboole_0)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f89,f85])).

fof(f89,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(k4_tarski(X0,X3),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))
      | ~ r2_hidden(X0,X2) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))
      | X1 != X3
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f68,f70])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
      | X1 != X3
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f663,plain,
    ( r2_hidden(sK3,k1_xboole_0)
    | ~ spl5_6
    | ~ spl5_22 ),
    inference(forward_demodulation,[],[f662,f159])).

fof(f159,plain,
    ( k1_xboole_0 = k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f157])).

fof(f662,plain,
    ( r2_hidden(sK3,k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2))
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f657,f40])).

fof(f657,plain,
    ( ~ v1_funct_1(sK2)
    | r2_hidden(sK3,k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2))
    | ~ spl5_22 ),
    inference(resolution,[],[f540,f74])).

fof(f540,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1))))
        | ~ v1_funct_1(X0)
        | r2_hidden(sK3,k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X0)) )
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f539])).

fof(f539,plain,
    ( spl5_22
  <=> ! [X0] :
        ( r2_hidden(sK3,k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X0))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f578,plain,
    ( ~ spl5_8
    | ~ spl5_11 ),
    inference(avatar_contradiction_clause,[],[f577])).

fof(f577,plain,
    ( $false
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f558,f190])).

fof(f190,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl5_8
  <=> r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f558,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl5_11 ),
    inference(superposition,[],[f86,f436])).

fof(f436,plain,
    ( k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f434])).

fof(f86,plain,(
    ! [X1] : ~ r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f53,f70,f70])).

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( X0 = X1
        & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).

fof(f541,plain,
    ( spl5_22
    | spl5_11 ),
    inference(avatar_split_clause,[],[f537,f434,f539])).

fof(f537,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
      | r2_hidden(sK3,k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1))))
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f536,f463])).

fof(f536,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
      | ~ r1_partfun1(X0,sK3)
      | r2_hidden(sK3,k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1))))
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f535,f42])).

fof(f535,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
      | ~ r1_partfun1(X0,sK3)
      | r2_hidden(sK3,k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X0))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1))))
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f531,f73])).

fof(f73,plain,(
    v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f43,f70])).

fof(f43,plain,(
    v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f531,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
      | ~ r1_partfun1(X0,sK3)
      | r2_hidden(sK3,k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X0))
      | ~ v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1))))
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f60,f72])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r1_partfun1(X2,X3)
      | r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f437,plain,
    ( spl5_10
    | spl5_11 ),
    inference(avatar_split_clause,[],[f428,f434,f430])).

fof(f428,plain,
    ( k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | v1_partfun1(sK3,sK0) ),
    inference(subsumption_resolution,[],[f427,f42])).

fof(f427,plain,
    ( k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | v1_partfun1(sK3,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f423,f73])).

fof(f423,plain,
    ( k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | v1_partfun1(sK3,sK0)
    | ~ v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f90,f72])).

fof(f403,plain,
    ( spl5_6
    | spl5_9 ),
    inference(avatar_split_clause,[],[f399,f401,f157])).

fof(f399,plain,(
    ! [X0] :
      ( v1_funct_2(sK4(k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2),X0),sK0,k2_enumset1(sK1,sK1,sK1,sK1))
      | k1_xboole_0 = k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2)
      | k2_enumset1(X0,X0,X0,X0) = k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ) ),
    inference(resolution,[],[f154,f76])).

fof(f154,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2))
      | v1_funct_2(X1,sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ) ),
    inference(subsumption_resolution,[],[f149,f40])).

fof(f149,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2))
      | v1_funct_2(X1,sK0,k2_enumset1(sK1,sK1,sK1,sK1))
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f58,f74])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f369,plain,
    ( spl5_6
    | spl5_7 ),
    inference(avatar_split_clause,[],[f368,f161,f157])).

fof(f368,plain,(
    ! [X0] :
      ( v1_funct_1(sK4(k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2),X0))
      | k1_xboole_0 = k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2)
      | k2_enumset1(X0,X0,X0,X0) = k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ) ),
    inference(resolution,[],[f137,f76])).

fof(f137,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2))
      | v1_funct_1(X1) ) ),
    inference(subsumption_resolution,[],[f133,f40])).

fof(f133,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2))
      | v1_funct_1(X1)
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f57,f74])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | v1_funct_1(X3)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f359,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f358])).

fof(f358,plain,
    ( $false
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f71,f116])).

fof(f116,plain,
    ( ! [X2,X3] : X2 = X3
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl5_1
  <=> ! [X3,X2] : X2 = X3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f191,plain,
    ( spl5_1
    | spl5_8 ),
    inference(avatar_split_clause,[],[f186,f188,f115])).

fof(f186,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
      | X0 = X1 ) ),
    inference(superposition,[],[f177,f85])).

fof(f177,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k1_xboole_0,k2_zfmisc_1(X1,k2_enumset1(X2,X2,X2,X2)))
      | X0 = X2 ) ),
    inference(superposition,[],[f79,f85])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X2,k2_enumset1(X0,X0,X0,X0)),k2_zfmisc_1(X3,k2_enumset1(X1,X1,X1,X1)))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f65,f70,f70])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,k1_tarski(X1)))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,k1_tarski(X1)))
        & r1_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X3)) )
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( X0 != X1
     => ( r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,k1_tarski(X1)))
        & r1_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:23:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (807)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.48  % (820)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (822)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.52  % (805)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (822)Refutation not found, incomplete strategy% (822)------------------------------
% 0.21/0.54  % (822)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (822)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (822)Memory used [KB]: 10746
% 0.21/0.54  % (822)Time elapsed: 0.091 s
% 0.21/0.54  % (822)------------------------------
% 0.21/0.54  % (822)------------------------------
% 0.21/0.55  % (816)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.56  % (806)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.57  % (831)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.57  % (826)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.57  % (823)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.57  % (811)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.57  % (830)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.58  % (830)Refutation not found, incomplete strategy% (830)------------------------------
% 0.21/0.58  % (830)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (830)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (830)Memory used [KB]: 10618
% 0.21/0.58  % (830)Time elapsed: 0.165 s
% 0.21/0.58  % (830)------------------------------
% 0.21/0.58  % (830)------------------------------
% 0.21/0.58  % (827)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.58  % (808)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.58  % (835)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.58  % (832)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.58  % (835)Refutation not found, incomplete strategy% (835)------------------------------
% 0.21/0.58  % (835)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (835)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (835)Memory used [KB]: 1663
% 0.21/0.58  % (835)Time elapsed: 0.002 s
% 0.21/0.58  % (835)------------------------------
% 0.21/0.58  % (835)------------------------------
% 0.21/0.58  % (828)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.59  % (814)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.59  % (807)Refutation not found, incomplete strategy% (807)------------------------------
% 0.21/0.59  % (807)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (807)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (807)Memory used [KB]: 6268
% 0.21/0.59  % (807)Time elapsed: 0.173 s
% 0.21/0.59  % (807)------------------------------
% 0.21/0.59  % (807)------------------------------
% 0.21/0.59  % (819)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.59  % (825)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.59  % (815)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.59  % (818)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.59  % (810)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.59  % (833)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.60  % (833)Refutation not found, incomplete strategy% (833)------------------------------
% 0.21/0.60  % (833)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.60  % (833)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.60  
% 0.21/0.60  % (833)Memory used [KB]: 6140
% 0.21/0.60  % (833)Time elapsed: 0.134 s
% 0.21/0.60  % (833)------------------------------
% 0.21/0.60  % (833)------------------------------
% 0.21/0.60  % (824)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.60  % (834)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.61  % (809)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.82/0.61  % (804)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.82/0.62  % (812)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 2.09/0.63  % (821)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 2.09/0.63  % (829)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 2.17/0.67  % (858)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.67/0.73  % (832)Refutation not found, incomplete strategy% (832)------------------------------
% 2.67/0.73  % (832)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.67/0.73  % (832)Termination reason: Refutation not found, incomplete strategy
% 2.67/0.73  
% 2.67/0.73  % (832)Memory used [KB]: 7036
% 2.67/0.73  % (832)Time elapsed: 0.319 s
% 2.67/0.73  % (832)------------------------------
% 2.67/0.73  % (832)------------------------------
% 2.67/0.74  % (863)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.67/0.75  % (861)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 3.06/0.78  % (864)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 3.06/0.78  % (862)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 3.06/0.78  % (862)Refutation not found, incomplete strategy% (862)------------------------------
% 3.06/0.78  % (862)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.06/0.78  % (862)Termination reason: Refutation not found, incomplete strategy
% 3.06/0.78  
% 3.06/0.78  % (862)Memory used [KB]: 6140
% 3.06/0.78  % (862)Time elapsed: 0.131 s
% 3.06/0.78  % (862)------------------------------
% 3.06/0.78  % (862)------------------------------
% 3.06/0.79  % (810)Refutation found. Thanks to Tanya!
% 3.06/0.79  % SZS status Theorem for theBenchmark
% 3.06/0.79  % SZS output start Proof for theBenchmark
% 3.06/0.79  fof(f3371,plain,(
% 3.06/0.79    $false),
% 3.06/0.79    inference(avatar_sat_refutation,[],[f191,f359,f369,f403,f437,f541,f578,f665,f3370])).
% 3.06/0.79  fof(f3370,plain,(
% 3.06/0.79    spl5_6 | ~spl5_7 | ~spl5_9 | ~spl5_10 | spl5_11),
% 3.06/0.79    inference(avatar_contradiction_clause,[],[f3369])).
% 3.06/0.79  fof(f3369,plain,(
% 3.06/0.79    $false | (spl5_6 | ~spl5_7 | ~spl5_9 | ~spl5_10 | spl5_11)),
% 3.06/0.79    inference(subsumption_resolution,[],[f3360,f71])).
% 3.06/0.79  fof(f71,plain,(
% 3.06/0.79    k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2) != k2_enumset1(sK3,sK3,sK3,sK3)),
% 3.06/0.79    inference(definition_unfolding,[],[f45,f70,f70])).
% 3.06/0.79  fof(f70,plain,(
% 3.06/0.79    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.06/0.79    inference(definition_unfolding,[],[f46,f69])).
% 3.06/0.79  fof(f69,plain,(
% 3.06/0.79    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.06/0.79    inference(definition_unfolding,[],[f47,f54])).
% 3.06/0.79  fof(f54,plain,(
% 3.06/0.79    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.06/0.79    inference(cnf_transformation,[],[f3])).
% 3.06/0.79  fof(f3,axiom,(
% 3.06/0.79    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.06/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 3.06/0.79  fof(f47,plain,(
% 3.06/0.79    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.06/0.79    inference(cnf_transformation,[],[f2])).
% 3.06/0.79  fof(f2,axiom,(
% 3.06/0.79    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.06/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 3.06/0.79  fof(f46,plain,(
% 3.06/0.79    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.06/0.79    inference(cnf_transformation,[],[f1])).
% 3.06/0.79  fof(f1,axiom,(
% 3.06/0.79    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.06/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 3.06/0.79  fof(f45,plain,(
% 3.06/0.79    k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3)),
% 3.06/0.79    inference(cnf_transformation,[],[f33])).
% 3.06/0.79  fof(f33,plain,(
% 3.06/0.79    (k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_1(sK2)),
% 3.06/0.79    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f32,f31])).
% 3.06/0.79  fof(f31,plain,(
% 3.06/0.79    ? [X0,X1,X2] : (? [X3] : (k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => (? [X3] : (k1_tarski(X3) != k5_partfun1(sK0,k1_tarski(sK1),sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(X3,sK0,k1_tarski(sK1)) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_1(sK2))),
% 3.06/0.79    introduced(choice_axiom,[])).
% 3.06/0.79  fof(f32,plain,(
% 3.06/0.79    ? [X3] : (k1_tarski(X3) != k5_partfun1(sK0,k1_tarski(sK1),sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(X3,sK0,k1_tarski(sK1)) & v1_funct_1(X3)) => (k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3))),
% 3.06/0.79    introduced(choice_axiom,[])).
% 3.06/0.79  fof(f17,plain,(
% 3.06/0.79    ? [X0,X1,X2] : (? [X3] : (k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2))),
% 3.06/0.79    inference(flattening,[],[f16])).
% 3.06/0.79  fof(f16,plain,(
% 3.06/0.79    ? [X0,X1,X2] : (? [X3] : (k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)))),
% 3.06/0.79    inference(ennf_transformation,[],[f15])).
% 3.06/0.79  fof(f15,negated_conjecture,(
% 3.06/0.79    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => k1_tarski(X3) = k5_partfun1(X0,k1_tarski(X1),X2)))),
% 3.06/0.79    inference(negated_conjecture,[],[f14])).
% 3.06/0.79  fof(f14,conjecture,(
% 3.06/0.79    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => k1_tarski(X3) = k5_partfun1(X0,k1_tarski(X1),X2)))),
% 3.06/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_2)).
% 3.06/0.79  fof(f3360,plain,(
% 3.06/0.79    k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2) = k2_enumset1(sK3,sK3,sK3,sK3) | (spl5_6 | ~spl5_7 | ~spl5_9 | ~spl5_10 | spl5_11)),
% 3.06/0.79    inference(equality_resolution,[],[f3284])).
% 3.06/0.79  fof(f3284,plain,(
% 3.06/0.79    ( ! [X6] : (sK3 != X6 | k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2) = k2_enumset1(X6,X6,X6,X6)) ) | (spl5_6 | ~spl5_7 | ~spl5_9 | ~spl5_10 | spl5_11)),
% 3.06/0.79    inference(subsumption_resolution,[],[f3105,f158])).
% 3.06/0.79  fof(f158,plain,(
% 3.06/0.79    k1_xboole_0 != k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2) | spl5_6),
% 3.06/0.79    inference(avatar_component_clause,[],[f157])).
% 3.06/0.79  fof(f157,plain,(
% 3.06/0.79    spl5_6 <=> k1_xboole_0 = k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2)),
% 3.06/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 3.06/0.79  fof(f3105,plain,(
% 3.06/0.79    ( ! [X6] : (sK3 != X6 | k1_xboole_0 = k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2) | k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2) = k2_enumset1(X6,X6,X6,X6)) ) | (spl5_6 | ~spl5_7 | ~spl5_9 | ~spl5_10 | spl5_11)),
% 3.06/0.79    inference(duplicate_literal_removal,[],[f3084])).
% 3.06/0.79  fof(f3084,plain,(
% 3.06/0.79    ( ! [X6] : (sK3 != X6 | k1_xboole_0 = k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2) | k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2) = k2_enumset1(X6,X6,X6,X6) | k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2) = k2_enumset1(X6,X6,X6,X6)) ) | (spl5_6 | ~spl5_7 | ~spl5_9 | ~spl5_10 | spl5_11)),
% 3.06/0.79    inference(superposition,[],[f75,f2960])).
% 3.06/0.79  fof(f2960,plain,(
% 3.06/0.79    ( ! [X4] : (k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2) = k2_enumset1(X4,X4,X4,X4) | sK3 = sK4(k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2),X4)) ) | (spl5_6 | ~spl5_7 | ~spl5_9 | ~spl5_10 | spl5_11)),
% 3.06/0.79    inference(subsumption_resolution,[],[f2959,f873])).
% 3.06/0.79  fof(f873,plain,(
% 3.06/0.79    ( ! [X12] : (v1_partfun1(sK4(k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2),X12),sK0) | k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2) = k2_enumset1(X12,X12,X12,X12)) ) | (spl5_6 | ~spl5_7 | ~spl5_9 | spl5_11)),
% 3.06/0.79    inference(subsumption_resolution,[],[f872,f402])).
% 3.06/0.79  fof(f402,plain,(
% 3.06/0.79    ( ! [X0] : (v1_funct_2(sK4(k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2),X0),sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | k2_enumset1(X0,X0,X0,X0) = k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ) | ~spl5_9),
% 3.06/0.79    inference(avatar_component_clause,[],[f401])).
% 3.06/0.79  fof(f401,plain,(
% 3.06/0.79    spl5_9 <=> ! [X0] : (v1_funct_2(sK4(k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2),X0),sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | k2_enumset1(X0,X0,X0,X0) = k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2))),
% 3.06/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 3.06/0.79  fof(f872,plain,(
% 3.06/0.79    ( ! [X12] : (k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2) = k2_enumset1(X12,X12,X12,X12) | v1_partfun1(sK4(k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2),X12),sK0) | ~v1_funct_2(sK4(k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2),X12),sK0,k2_enumset1(sK1,sK1,sK1,sK1))) ) | (spl5_6 | ~spl5_7 | spl5_11)),
% 3.06/0.79    inference(subsumption_resolution,[],[f871,f162])).
% 3.06/0.79  fof(f162,plain,(
% 3.06/0.79    ( ! [X0] : (v1_funct_1(sK4(k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2),X0)) | k2_enumset1(X0,X0,X0,X0) = k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ) | ~spl5_7),
% 3.06/0.79    inference(avatar_component_clause,[],[f161])).
% 3.06/0.79  fof(f161,plain,(
% 3.06/0.79    spl5_7 <=> ! [X0] : (v1_funct_1(sK4(k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2),X0)) | k2_enumset1(X0,X0,X0,X0) = k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2))),
% 3.06/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 3.06/0.79  fof(f871,plain,(
% 3.06/0.79    ( ! [X12] : (k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2) = k2_enumset1(X12,X12,X12,X12) | v1_partfun1(sK4(k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2),X12),sK0) | ~v1_funct_2(sK4(k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2),X12),sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | ~v1_funct_1(sK4(k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2),X12))) ) | (spl5_6 | spl5_11)),
% 3.06/0.79    inference(subsumption_resolution,[],[f858,f435])).
% 3.06/0.79  fof(f435,plain,(
% 3.06/0.79    k1_xboole_0 != k2_enumset1(sK1,sK1,sK1,sK1) | spl5_11),
% 3.06/0.79    inference(avatar_component_clause,[],[f434])).
% 3.06/0.79  fof(f434,plain,(
% 3.06/0.79    spl5_11 <=> k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)),
% 3.06/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 3.06/0.79  fof(f858,plain,(
% 3.06/0.79    ( ! [X12] : (k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2) = k2_enumset1(X12,X12,X12,X12) | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | v1_partfun1(sK4(k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2),X12),sK0) | ~v1_funct_2(sK4(k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2),X12),sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | ~v1_funct_1(sK4(k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2),X12))) ) | spl5_6),
% 3.06/0.79    inference(resolution,[],[f760,f90])).
% 3.06/0.79  fof(f90,plain,(
% 3.06/0.79    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.06/0.79    inference(duplicate_literal_removal,[],[f55])).
% 3.06/0.79  fof(f55,plain,(
% 3.06/0.79    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.06/0.79    inference(cnf_transformation,[],[f21])).
% 3.06/0.79  fof(f21,plain,(
% 3.06/0.79    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.06/0.79    inference(flattening,[],[f20])).
% 3.06/0.79  fof(f20,plain,(
% 3.06/0.79    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.06/0.79    inference(ennf_transformation,[],[f9])).
% 3.06/0.79  fof(f9,axiom,(
% 3.06/0.79    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.06/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).
% 3.06/0.79  fof(f760,plain,(
% 3.06/0.79    ( ! [X0] : (m1_subset_1(sK4(k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2),X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))) | k2_enumset1(X0,X0,X0,X0) = k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ) | spl5_6),
% 3.06/0.79    inference(subsumption_resolution,[],[f759,f158])).
% 3.06/0.79  fof(f759,plain,(
% 3.06/0.79    ( ! [X0] : (m1_subset_1(sK4(k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2),X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))) | k1_xboole_0 = k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2) | k2_enumset1(X0,X0,X0,X0) = k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2)) )),
% 3.06/0.79    inference(resolution,[],[f455,f76])).
% 3.06/0.79  fof(f76,plain,(
% 3.06/0.79    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 3.06/0.79    inference(definition_unfolding,[],[f51,f70])).
% 3.06/0.79  fof(f51,plain,(
% 3.06/0.79    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 3.06/0.79    inference(cnf_transformation,[],[f37])).
% 3.06/0.79  fof(f37,plain,(
% 3.06/0.79    ! [X0,X1] : ((sK4(X0,X1) != X1 & r2_hidden(sK4(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 3.06/0.79    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f36])).
% 3.06/0.79  fof(f36,plain,(
% 3.06/0.79    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK4(X0,X1) != X1 & r2_hidden(sK4(X0,X1),X0)))),
% 3.06/0.79    introduced(choice_axiom,[])).
% 3.06/0.79  fof(f18,plain,(
% 3.06/0.79    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 3.06/0.79    inference(ennf_transformation,[],[f4])).
% 3.06/0.79  fof(f4,axiom,(
% 3.06/0.79    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 3.06/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).
% 3.06/0.79  fof(f455,plain,(
% 3.06/0.79    ( ! [X1] : (~r2_hidden(X1,k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2)) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1))))) )),
% 3.06/0.79    inference(subsumption_resolution,[],[f450,f40])).
% 3.06/0.79  fof(f40,plain,(
% 3.06/0.79    v1_funct_1(sK2)),
% 3.06/0.79    inference(cnf_transformation,[],[f33])).
% 3.06/0.79  fof(f450,plain,(
% 3.06/0.79    ( ! [X1] : (~r2_hidden(X1,k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2)) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))) | ~v1_funct_1(sK2)) )),
% 3.06/0.79    inference(resolution,[],[f59,f74])).
% 3.06/0.79  fof(f74,plain,(
% 3.06/0.79    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1))))),
% 3.06/0.79    inference(definition_unfolding,[],[f41,f70])).
% 3.06/0.79  fof(f41,plain,(
% 3.06/0.79    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 3.06/0.79    inference(cnf_transformation,[],[f33])).
% 3.06/0.79  fof(f59,plain,(
% 3.06/0.79    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.06/0.79    inference(cnf_transformation,[],[f23])).
% 3.06/0.79  fof(f23,plain,(
% 3.06/0.79    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.06/0.79    inference(flattening,[],[f22])).
% 3.06/0.79  fof(f22,plain,(
% 3.06/0.79    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.06/0.79    inference(ennf_transformation,[],[f13])).
% 3.06/0.79  fof(f13,axiom,(
% 3.06/0.79    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (r2_hidden(X3,k5_partfun1(X0,X1,X2)) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))))),
% 3.06/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_2)).
% 3.06/0.79  fof(f2959,plain,(
% 3.06/0.79    ( ! [X4] : (k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2) = k2_enumset1(X4,X4,X4,X4) | sK3 = sK4(k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2),X4) | ~v1_partfun1(sK4(k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2),X4),sK0)) ) | (spl5_6 | ~spl5_7 | ~spl5_10)),
% 3.06/0.79    inference(subsumption_resolution,[],[f2938,f162])).
% 3.06/0.79  fof(f2938,plain,(
% 3.06/0.79    ( ! [X4] : (k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2) = k2_enumset1(X4,X4,X4,X4) | sK3 = sK4(k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2),X4) | ~v1_partfun1(sK4(k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2),X4),sK0) | ~v1_funct_1(sK4(k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2),X4))) ) | (spl5_6 | ~spl5_10)),
% 3.06/0.79    inference(resolution,[],[f760,f510])).
% 3.06/0.79  fof(f510,plain,(
% 3.06/0.79    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))) | sK3 = X0 | ~v1_partfun1(X0,sK0) | ~v1_funct_1(X0)) ) | ~spl5_10),
% 3.06/0.79    inference(subsumption_resolution,[],[f509,f463])).
% 3.06/0.79  fof(f463,plain,(
% 3.06/0.79    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))) | r1_partfun1(X0,sK3) | ~v1_funct_1(X0)) )),
% 3.06/0.79    inference(subsumption_resolution,[],[f460,f42])).
% 3.06/0.79  fof(f42,plain,(
% 3.06/0.79    v1_funct_1(sK3)),
% 3.06/0.79    inference(cnf_transformation,[],[f33])).
% 3.06/0.79  fof(f460,plain,(
% 3.06/0.79    ( ! [X0] : (r1_partfun1(X0,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))) | ~v1_funct_1(X0)) )),
% 3.06/0.79    inference(resolution,[],[f78,f72])).
% 3.06/0.79  fof(f72,plain,(
% 3.06/0.79    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1))))),
% 3.06/0.79    inference(definition_unfolding,[],[f44,f70])).
% 3.06/0.79  fof(f44,plain,(
% 3.06/0.79    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 3.06/0.79    inference(cnf_transformation,[],[f33])).
% 3.06/0.79  fof(f78,plain,(
% 3.06/0.79    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1)))) | r1_partfun1(X2,X3) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1)))) | ~v1_funct_1(X2)) )),
% 3.06/0.79    inference(definition_unfolding,[],[f63,f70,f70])).
% 3.06/0.79  fof(f63,plain,(
% 3.06/0.79    ( ! [X2,X0,X3,X1] : (r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2)) )),
% 3.06/0.79    inference(cnf_transformation,[],[f29])).
% 3.06/0.79  fof(f29,plain,(
% 3.06/0.79    ! [X0,X1,X2] : (! [X3] : (r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2))),
% 3.06/0.79    inference(flattening,[],[f28])).
% 3.06/0.79  fof(f28,plain,(
% 3.06/0.79    ! [X0,X1,X2] : (! [X3] : (r1_partfun1(X2,X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2)))),
% 3.06/0.79    inference(ennf_transformation,[],[f10])).
% 3.06/0.79  fof(f10,axiom,(
% 3.06/0.79    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X3)) => r1_partfun1(X2,X3)))),
% 3.06/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_partfun1)).
% 3.06/0.79  fof(f509,plain,(
% 3.06/0.79    ( ! [X0] : (~r1_partfun1(X0,sK3) | ~v1_partfun1(X0,sK0) | sK3 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))) | ~v1_funct_1(X0)) ) | ~spl5_10),
% 3.06/0.79    inference(subsumption_resolution,[],[f508,f42])).
% 3.06/0.79  fof(f508,plain,(
% 3.06/0.79    ( ! [X0] : (~r1_partfun1(X0,sK3) | ~v1_partfun1(X0,sK0) | sK3 = X0 | ~v1_funct_1(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))) | ~v1_funct_1(X0)) ) | ~spl5_10),
% 3.06/0.79    inference(subsumption_resolution,[],[f475,f432])).
% 3.06/0.79  fof(f432,plain,(
% 3.06/0.79    v1_partfun1(sK3,sK0) | ~spl5_10),
% 3.06/0.79    inference(avatar_component_clause,[],[f430])).
% 3.06/0.79  fof(f430,plain,(
% 3.06/0.79    spl5_10 <=> v1_partfun1(sK3,sK0)),
% 3.06/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 3.06/0.79  fof(f475,plain,(
% 3.06/0.79    ( ! [X0] : (~r1_partfun1(X0,sK3) | ~v1_partfun1(sK3,sK0) | ~v1_partfun1(X0,sK0) | sK3 = X0 | ~v1_funct_1(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))) | ~v1_funct_1(X0)) )),
% 3.06/0.79    inference(resolution,[],[f62,f72])).
% 3.06/0.79  fof(f62,plain,(
% 3.06/0.79    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | X2 = X3 | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.06/0.79    inference(cnf_transformation,[],[f27])).
% 3.06/0.79  fof(f27,plain,(
% 3.06/0.79    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.06/0.79    inference(flattening,[],[f26])).
% 3.06/0.79  fof(f26,plain,(
% 3.06/0.79    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.06/0.79    inference(ennf_transformation,[],[f11])).
% 3.06/0.79  fof(f11,axiom,(
% 3.06/0.79    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 3.06/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).
% 3.06/0.79  fof(f75,plain,(
% 3.06/0.79    ( ! [X0,X1] : (sK4(X0,X1) != X1 | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 3.06/0.79    inference(definition_unfolding,[],[f52,f70])).
% 3.06/0.79  fof(f52,plain,(
% 3.06/0.79    ( ! [X0,X1] : (sK4(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 3.06/0.79    inference(cnf_transformation,[],[f37])).
% 3.06/0.79  fof(f665,plain,(
% 3.06/0.79    ~spl5_6 | ~spl5_22),
% 3.06/0.79    inference(avatar_contradiction_clause,[],[f664])).
% 3.06/0.79  fof(f664,plain,(
% 3.06/0.79    $false | (~spl5_6 | ~spl5_22)),
% 3.06/0.79    inference(subsumption_resolution,[],[f663,f111])).
% 3.06/0.79  fof(f111,plain,(
% 3.06/0.79    ( ! [X4] : (~r2_hidden(X4,k1_xboole_0)) )),
% 3.06/0.79    inference(resolution,[],[f108,f99])).
% 3.06/0.79  fof(f99,plain,(
% 3.06/0.79    ( ! [X0] : (~r2_hidden(k4_tarski(X0,k2_enumset1(sK3,sK3,sK3,sK3)),k1_xboole_0)) )),
% 3.06/0.79    inference(extensionality_resolution,[],[f98,f71])).
% 3.06/0.79  fof(f98,plain,(
% 3.06/0.79    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X1,X2),k1_xboole_0) | X0 = X2) )),
% 3.06/0.79    inference(superposition,[],[f82,f85])).
% 3.06/0.79  fof(f85,plain,(
% 3.06/0.79    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.06/0.79    inference(equality_resolution,[],[f49])).
% 3.06/0.79  fof(f49,plain,(
% 3.06/0.79    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.06/0.79    inference(cnf_transformation,[],[f35])).
% 3.06/0.79  fof(f35,plain,(
% 3.06/0.79    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.06/0.79    inference(flattening,[],[f34])).
% 3.06/0.79  fof(f34,plain,(
% 3.06/0.79    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.06/0.79    inference(nnf_transformation,[],[f5])).
% 3.06/0.79  fof(f5,axiom,(
% 3.06/0.79    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.06/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 3.06/0.79  fof(f82,plain,(
% 3.06/0.79    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))) | X1 = X3) )),
% 3.06/0.79    inference(definition_unfolding,[],[f67,f70])).
% 3.06/0.79  fof(f67,plain,(
% 3.06/0.79    ( ! [X2,X0,X3,X1] : (X1 = X3 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))) )),
% 3.06/0.79    inference(cnf_transformation,[],[f39])).
% 3.06/0.79  fof(f39,plain,(
% 3.06/0.79    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | X1 != X3 | ~r2_hidden(X0,X2)) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 3.06/0.79    inference(flattening,[],[f38])).
% 3.06/0.79  fof(f38,plain,(
% 3.06/0.79    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | (X1 != X3 | ~r2_hidden(X0,X2))) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 3.06/0.79    inference(nnf_transformation,[],[f6])).
% 3.06/0.79  fof(f6,axiom,(
% 3.06/0.79    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <=> (X1 = X3 & r2_hidden(X0,X2)))),
% 3.06/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).
% 3.06/0.79  fof(f108,plain,(
% 3.06/0.79    ( ! [X0,X1] : (r2_hidden(k4_tarski(X1,X0),k1_xboole_0) | ~r2_hidden(X1,k1_xboole_0)) )),
% 3.06/0.79    inference(superposition,[],[f89,f85])).
% 3.06/0.79  fof(f89,plain,(
% 3.06/0.79    ( ! [X2,X0,X3] : (r2_hidden(k4_tarski(X0,X3),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))) | ~r2_hidden(X0,X2)) )),
% 3.06/0.79    inference(equality_resolution,[],[f81])).
% 3.06/0.79  fof(f81,plain,(
% 3.06/0.79    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))) | X1 != X3 | ~r2_hidden(X0,X2)) )),
% 3.06/0.79    inference(definition_unfolding,[],[f68,f70])).
% 3.06/0.79  fof(f68,plain,(
% 3.06/0.79    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | X1 != X3 | ~r2_hidden(X0,X2)) )),
% 3.06/0.79    inference(cnf_transformation,[],[f39])).
% 3.06/0.79  fof(f663,plain,(
% 3.06/0.79    r2_hidden(sK3,k1_xboole_0) | (~spl5_6 | ~spl5_22)),
% 3.06/0.79    inference(forward_demodulation,[],[f662,f159])).
% 3.06/0.79  fof(f159,plain,(
% 3.06/0.79    k1_xboole_0 = k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2) | ~spl5_6),
% 3.06/0.79    inference(avatar_component_clause,[],[f157])).
% 3.06/0.79  fof(f662,plain,(
% 3.06/0.79    r2_hidden(sK3,k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2)) | ~spl5_22),
% 3.06/0.79    inference(subsumption_resolution,[],[f657,f40])).
% 3.06/0.79  fof(f657,plain,(
% 3.06/0.79    ~v1_funct_1(sK2) | r2_hidden(sK3,k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2)) | ~spl5_22),
% 3.06/0.79    inference(resolution,[],[f540,f74])).
% 3.06/0.79  fof(f540,plain,(
% 3.06/0.79    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))) | ~v1_funct_1(X0) | r2_hidden(sK3,k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X0))) ) | ~spl5_22),
% 3.06/0.79    inference(avatar_component_clause,[],[f539])).
% 3.06/0.79  fof(f539,plain,(
% 3.06/0.79    spl5_22 <=> ! [X0] : (r2_hidden(sK3,k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X0)) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))))),
% 3.06/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 3.06/0.79  fof(f578,plain,(
% 3.06/0.79    ~spl5_8 | ~spl5_11),
% 3.06/0.79    inference(avatar_contradiction_clause,[],[f577])).
% 3.06/0.79  fof(f577,plain,(
% 3.06/0.79    $false | (~spl5_8 | ~spl5_11)),
% 3.06/0.79    inference(subsumption_resolution,[],[f558,f190])).
% 3.06/0.79  fof(f190,plain,(
% 3.06/0.79    r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl5_8),
% 3.06/0.79    inference(avatar_component_clause,[],[f188])).
% 3.06/0.79  fof(f188,plain,(
% 3.06/0.79    spl5_8 <=> r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 3.06/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 3.06/0.79  fof(f558,plain,(
% 3.06/0.79    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl5_11),
% 3.06/0.79    inference(superposition,[],[f86,f436])).
% 3.06/0.79  fof(f436,plain,(
% 3.06/0.79    k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl5_11),
% 3.06/0.79    inference(avatar_component_clause,[],[f434])).
% 3.06/0.79  fof(f86,plain,(
% 3.06/0.79    ( ! [X1] : (~r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))) )),
% 3.06/0.79    inference(equality_resolution,[],[f77])).
% 3.06/0.79  fof(f77,plain,(
% 3.06/0.79    ( ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) )),
% 3.06/0.79    inference(definition_unfolding,[],[f53,f70,f70])).
% 3.06/0.79  fof(f53,plain,(
% 3.06/0.79    ( ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 3.06/0.79    inference(cnf_transformation,[],[f19])).
% 3.06/0.79  fof(f19,plain,(
% 3.06/0.79    ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 3.06/0.79    inference(ennf_transformation,[],[f8])).
% 3.06/0.79  fof(f8,axiom,(
% 3.06/0.79    ! [X0,X1] : ~(X0 = X1 & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 3.06/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).
% 3.06/0.79  fof(f541,plain,(
% 3.06/0.79    spl5_22 | spl5_11),
% 3.06/0.79    inference(avatar_split_clause,[],[f537,f434,f539])).
% 3.06/0.79  fof(f537,plain,(
% 3.06/0.79    ( ! [X0] : (k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | r2_hidden(sK3,k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))) | ~v1_funct_1(X0)) )),
% 3.06/0.79    inference(subsumption_resolution,[],[f536,f463])).
% 3.06/0.79  fof(f536,plain,(
% 3.06/0.79    ( ! [X0] : (k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~r1_partfun1(X0,sK3) | r2_hidden(sK3,k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))) | ~v1_funct_1(X0)) )),
% 3.06/0.79    inference(subsumption_resolution,[],[f535,f42])).
% 3.06/0.79  fof(f535,plain,(
% 3.06/0.79    ( ! [X0] : (k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~r1_partfun1(X0,sK3) | r2_hidden(sK3,k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X0)) | ~v1_funct_1(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))) | ~v1_funct_1(X0)) )),
% 3.06/0.79    inference(subsumption_resolution,[],[f531,f73])).
% 3.06/0.79  fof(f73,plain,(
% 3.06/0.79    v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 3.06/0.79    inference(definition_unfolding,[],[f43,f70])).
% 3.06/0.79  fof(f43,plain,(
% 3.06/0.79    v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 3.06/0.79    inference(cnf_transformation,[],[f33])).
% 3.06/0.79  fof(f531,plain,(
% 3.06/0.79    ( ! [X0] : (k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~r1_partfun1(X0,sK3) | r2_hidden(sK3,k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X0)) | ~v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | ~v1_funct_1(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))) | ~v1_funct_1(X0)) )),
% 3.06/0.79    inference(resolution,[],[f60,f72])).
% 3.06/0.79  fof(f60,plain,(
% 3.06/0.79    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r1_partfun1(X2,X3) | r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.06/0.79    inference(cnf_transformation,[],[f25])).
% 3.06/0.79  fof(f25,plain,(
% 3.06/0.79    ! [X0,X1,X2] : (! [X3] : (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.06/0.79    inference(flattening,[],[f24])).
% 3.06/0.79  fof(f24,plain,(
% 3.06/0.79    ! [X0,X1,X2] : (! [X3] : (((r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_partfun1(X2,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.06/0.79    inference(ennf_transformation,[],[f12])).
% 3.06/0.79  fof(f12,axiom,(
% 3.06/0.79    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 3.06/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_2)).
% 3.06/0.79  fof(f437,plain,(
% 3.06/0.79    spl5_10 | spl5_11),
% 3.06/0.79    inference(avatar_split_clause,[],[f428,f434,f430])).
% 3.06/0.79  fof(f428,plain,(
% 3.06/0.79    k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | v1_partfun1(sK3,sK0)),
% 3.06/0.79    inference(subsumption_resolution,[],[f427,f42])).
% 3.06/0.79  fof(f427,plain,(
% 3.06/0.79    k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | v1_partfun1(sK3,sK0) | ~v1_funct_1(sK3)),
% 3.06/0.79    inference(subsumption_resolution,[],[f423,f73])).
% 3.06/0.79  fof(f423,plain,(
% 3.06/0.79    k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | v1_partfun1(sK3,sK0) | ~v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | ~v1_funct_1(sK3)),
% 3.06/0.79    inference(resolution,[],[f90,f72])).
% 3.06/0.79  fof(f403,plain,(
% 3.06/0.79    spl5_6 | spl5_9),
% 3.06/0.79    inference(avatar_split_clause,[],[f399,f401,f157])).
% 3.06/0.79  fof(f399,plain,(
% 3.06/0.79    ( ! [X0] : (v1_funct_2(sK4(k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2),X0),sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | k1_xboole_0 = k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2) | k2_enumset1(X0,X0,X0,X0) = k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2)) )),
% 3.06/0.79    inference(resolution,[],[f154,f76])).
% 3.06/0.79  fof(f154,plain,(
% 3.06/0.79    ( ! [X1] : (~r2_hidden(X1,k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2)) | v1_funct_2(X1,sK0,k2_enumset1(sK1,sK1,sK1,sK1))) )),
% 3.06/0.79    inference(subsumption_resolution,[],[f149,f40])).
% 3.06/0.79  fof(f149,plain,(
% 3.06/0.79    ( ! [X1] : (~r2_hidden(X1,k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2)) | v1_funct_2(X1,sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | ~v1_funct_1(sK2)) )),
% 3.06/0.79    inference(resolution,[],[f58,f74])).
% 3.06/0.79  fof(f58,plain,(
% 3.06/0.79    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | v1_funct_2(X3,X0,X1) | ~v1_funct_1(X2)) )),
% 3.06/0.79    inference(cnf_transformation,[],[f23])).
% 3.06/0.79  fof(f369,plain,(
% 3.06/0.79    spl5_6 | spl5_7),
% 3.06/0.79    inference(avatar_split_clause,[],[f368,f161,f157])).
% 3.06/0.79  fof(f368,plain,(
% 3.06/0.79    ( ! [X0] : (v1_funct_1(sK4(k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2),X0)) | k1_xboole_0 = k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2) | k2_enumset1(X0,X0,X0,X0) = k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2)) )),
% 3.06/0.79    inference(resolution,[],[f137,f76])).
% 3.06/0.79  fof(f137,plain,(
% 3.06/0.79    ( ! [X1] : (~r2_hidden(X1,k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2)) | v1_funct_1(X1)) )),
% 3.06/0.79    inference(subsumption_resolution,[],[f133,f40])).
% 3.06/0.79  fof(f133,plain,(
% 3.06/0.79    ( ! [X1] : (~r2_hidden(X1,k5_partfun1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK2)) | v1_funct_1(X1) | ~v1_funct_1(sK2)) )),
% 3.06/0.79    inference(resolution,[],[f57,f74])).
% 3.06/0.79  fof(f57,plain,(
% 3.06/0.79    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | v1_funct_1(X3) | ~v1_funct_1(X2)) )),
% 3.06/0.79    inference(cnf_transformation,[],[f23])).
% 3.06/0.79  fof(f359,plain,(
% 3.06/0.79    ~spl5_1),
% 3.06/0.79    inference(avatar_contradiction_clause,[],[f358])).
% 3.06/0.79  fof(f358,plain,(
% 3.06/0.79    $false | ~spl5_1),
% 3.06/0.79    inference(subsumption_resolution,[],[f71,f116])).
% 3.06/0.79  fof(f116,plain,(
% 3.06/0.79    ( ! [X2,X3] : (X2 = X3) ) | ~spl5_1),
% 3.06/0.79    inference(avatar_component_clause,[],[f115])).
% 3.06/0.79  fof(f115,plain,(
% 3.06/0.79    spl5_1 <=> ! [X3,X2] : X2 = X3),
% 3.06/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 3.06/0.79  fof(f191,plain,(
% 3.06/0.79    spl5_1 | spl5_8),
% 3.06/0.79    inference(avatar_split_clause,[],[f186,f188,f115])).
% 3.06/0.79  fof(f186,plain,(
% 3.06/0.79    ( ! [X0,X1] : (r1_xboole_0(k1_xboole_0,k1_xboole_0) | X0 = X1) )),
% 3.06/0.79    inference(superposition,[],[f177,f85])).
% 3.06/0.79  fof(f177,plain,(
% 3.06/0.79    ( ! [X2,X0,X1] : (r1_xboole_0(k1_xboole_0,k2_zfmisc_1(X1,k2_enumset1(X2,X2,X2,X2))) | X0 = X2) )),
% 3.06/0.79    inference(superposition,[],[f79,f85])).
% 3.06/0.79  fof(f79,plain,(
% 3.06/0.79    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X2,k2_enumset1(X0,X0,X0,X0)),k2_zfmisc_1(X3,k2_enumset1(X1,X1,X1,X1))) | X0 = X1) )),
% 3.06/0.79    inference(definition_unfolding,[],[f65,f70,f70])).
% 3.06/0.79  fof(f65,plain,(
% 3.06/0.79    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,k1_tarski(X1))) | X0 = X1) )),
% 3.06/0.79    inference(cnf_transformation,[],[f30])).
% 3.06/0.79  fof(f30,plain,(
% 3.06/0.79    ! [X0,X1,X2,X3] : ((r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,k1_tarski(X1))) & r1_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X3))) | X0 = X1)),
% 3.06/0.79    inference(ennf_transformation,[],[f7])).
% 3.06/0.79  fof(f7,axiom,(
% 3.06/0.79    ! [X0,X1,X2,X3] : (X0 != X1 => (r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,k1_tarski(X1))) & r1_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X3))))),
% 3.06/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_zfmisc_1)).
% 3.06/0.79  % SZS output end Proof for theBenchmark
% 3.06/0.79  % (810)------------------------------
% 3.06/0.79  % (810)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.06/0.79  % (810)Termination reason: Refutation
% 3.06/0.79  
% 3.06/0.79  % (810)Memory used [KB]: 12665
% 3.06/0.79  % (810)Time elapsed: 0.349 s
% 3.06/0.79  % (810)------------------------------
% 3.06/0.79  % (810)------------------------------
% 3.06/0.79  % (801)Success in time 0.43 s
%------------------------------------------------------------------------------
