%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:31 EST 2020

% Result     : Theorem 1.88s
% Output     : Refutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 384 expanded)
%              Number of leaves         :   21 ( 105 expanded)
%              Depth                    :   21
%              Number of atoms          :  472 (2110 expanded)
%              Number of equality atoms :  215 (1082 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f406,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f207,f242,f304,f364,f400])).

fof(f400,plain,(
    ~ spl7_10 ),
    inference(avatar_contradiction_clause,[],[f399])).

fof(f399,plain,
    ( $false
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f398,f41])).

fof(f41,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK3 = X7
                | k3_mcart_1(X5,X6,X7) != sK4
                | ~ m1_subset_1(X7,sK2) )
            | ~ m1_subset_1(X6,sK1) )
        | ~ m1_subset_1(X5,sK0) )
    & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f19,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k7_mcart_1(X0,X1,X2,X4) != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X5] :
            ( ! [X6] :
                ( ! [X7] :
                    ( X3 = X7
                    | k3_mcart_1(X5,X6,X7) != X4
                    | ~ m1_subset_1(X7,X2) )
                | ~ m1_subset_1(X6,X1) )
            | ~ m1_subset_1(X5,X0) )
        & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) )
   => ( sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK3 = X7
                  | k3_mcart_1(X5,X6,X7) != sK4
                  | ~ m1_subset_1(X7,sK2) )
              | ~ m1_subset_1(X6,sK1) )
          | ~ m1_subset_1(X5,sK0) )
      & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X7 ) ) ) )
         => ( k7_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X7 ) ) ) )
       => ( k7_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_mcart_1)).

fof(f398,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f397,f42])).

fof(f42,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f30])).

fof(f397,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f396,f43])).

fof(f43,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f30])).

fof(f396,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_10 ),
    inference(condensation,[],[f395])).

fof(f395,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 = sK2
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0 )
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f392,f93])).

fof(f93,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(resolution,[],[f91,f49])).

fof(f49,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK6(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK6(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f20,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X5,X4,X3,X2] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK6(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK6(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).

fof(f91,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1)) ),
    inference(resolution,[],[f90,f45])).

fof(f45,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(resolution,[],[f58,f47])).

fof(f47,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK5(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f32,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f392,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0)
        | k1_xboole_0 = X0
        | k1_xboole_0 = sK2
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0 )
    | ~ spl7_10 ),
    inference(superposition,[],[f81,f387])).

fof(f387,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl7_10 ),
    inference(resolution,[],[f379,f87])).

fof(f87,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f49,f47])).

fof(f379,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl7_10 ),
    inference(resolution,[],[f373,f72])).

fof(f72,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f39,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f39,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f30])).

fof(f373,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1))
        | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1)) )
    | ~ spl7_10 ),
    inference(resolution,[],[f370,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f370,plain,
    ( ! [X0,X1] : ~ r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1))
    | ~ spl7_10 ),
    inference(resolution,[],[f206,f58])).

fof(f206,plain,
    ( ! [X0] : ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,sK1))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl7_10
  <=> ! [X0] : ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f65,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f63,f57])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).

fof(f364,plain,(
    ~ spl7_9 ),
    inference(avatar_contradiction_clause,[],[f363])).

fof(f363,plain,
    ( $false
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f362,f41])).

fof(f362,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f361,f42])).

fof(f361,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f360,f43])).

fof(f360,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_9 ),
    inference(condensation,[],[f359])).

fof(f359,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 = sK2
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0 )
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f356,f93])).

fof(f356,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0)
        | k1_xboole_0 = X0
        | k1_xboole_0 = sK2
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0 )
    | ~ spl7_9 ),
    inference(superposition,[],[f81,f351])).

fof(f351,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl7_9 ),
    inference(resolution,[],[f343,f87])).

fof(f343,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl7_9 ),
    inference(resolution,[],[f337,f72])).

fof(f337,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1))
        | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1)) )
    | ~ spl7_9 ),
    inference(resolution,[],[f313,f54])).

fof(f313,plain,
    ( ! [X0,X1] : ~ r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1))
    | ~ spl7_9 ),
    inference(resolution,[],[f203,f58])).

fof(f203,plain,
    ( ! [X1] : ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,X1))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f202])).

fof(f202,plain,
    ( spl7_9
  <=> ! [X1] : ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f304,plain,(
    ~ spl7_8 ),
    inference(avatar_contradiction_clause,[],[f303])).

fof(f303,plain,
    ( $false
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f302,f41])).

fof(f302,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f301,f42])).

fof(f301,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f300,f43])).

fof(f300,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f299,f72])).

fof(f299,plain,
    ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f294,f200])).

fof(f200,plain,
    ( sK3 = k2_mcart_1(sK4)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl7_8
  <=> sK3 = k2_mcart_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f294,plain,
    ( sK3 != k2_mcart_1(sK4)
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f44,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f62,f57])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f44,plain,(
    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f242,plain,(
    ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f241])).

fof(f241,plain,
    ( $false
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f240,f41])).

fof(f240,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f239,f42])).

fof(f239,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f238,f43])).

fof(f238,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_7 ),
    inference(condensation,[],[f237])).

fof(f237,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 = sK2
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0 )
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f229,f93])).

fof(f229,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0)
        | k1_xboole_0 = X0
        | k1_xboole_0 = sK2
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0 )
    | ~ spl7_7 ),
    inference(superposition,[],[f81,f215])).

fof(f215,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl7_7 ),
    inference(resolution,[],[f210,f87])).

fof(f210,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl7_7 ),
    inference(resolution,[],[f208,f72])).

fof(f208,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(X0,sK2))
        | v1_xboole_0(k2_zfmisc_1(X0,sK2)) )
    | ~ spl7_7 ),
    inference(resolution,[],[f196,f54])).

fof(f196,plain,
    ( ! [X2] : ~ r2_hidden(sK4,k2_zfmisc_1(X2,sK2))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl7_7
  <=> ! [X2] : ~ r2_hidden(sK4,k2_zfmisc_1(X2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f207,plain,
    ( spl7_7
    | spl7_8
    | spl7_9
    | spl7_10 ),
    inference(avatar_split_clause,[],[f193,f205,f202,f198,f195])).

fof(f193,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,sK1))
      | ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,X1))
      | sK3 = k2_mcart_1(sK4)
      | ~ r2_hidden(sK4,k2_zfmisc_1(X2,sK2)) ) ),
    inference(equality_resolution,[],[f192])).

fof(f192,plain,(
    ! [X2,X0,X5,X1] :
      ( sK4 != X0
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X1,sK1))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X2))
      | k2_mcart_1(X0) = sK3
      | ~ r2_hidden(X0,k2_zfmisc_1(X5,sK2)) ) ),
    inference(condensation,[],[f190])).

fof(f190,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sK4 != X0
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X1,sK1))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X2))
      | ~ r2_hidden(X0,k2_zfmisc_1(X3,X4))
      | k2_mcart_1(X0) = sK3
      | ~ r2_hidden(X0,k2_zfmisc_1(X5,sK2)) ) ),
    inference(resolution,[],[f189,f52])).

fof(f52,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f189,plain,(
    ! [X6,X4,X0,X5,X3] :
      ( ~ v1_relat_1(X5)
      | sK4 != X0
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X3,sK1))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X4))
      | ~ r2_hidden(X0,X5)
      | k2_mcart_1(X0) = sK3
      | ~ r2_hidden(X0,k2_zfmisc_1(X6,sK2)) ) ),
    inference(condensation,[],[f187])).

fof(f187,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X1,X2))
      | k2_mcart_1(X0) = sK3
      | sK4 != X0
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X3,sK1))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X4))
      | ~ r2_hidden(X0,X5)
      | ~ v1_relat_1(X5)
      | ~ r2_hidden(X0,k2_zfmisc_1(X6,sK2)) ) ),
    inference(resolution,[],[f171,f52])).

fof(f171,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k1_mcart_1(X1),X0)
      | sK3 = k2_mcart_1(X1)
      | sK4 != X1
      | ~ r2_hidden(k1_mcart_1(X1),k2_zfmisc_1(X2,sK1))
      | ~ r2_hidden(k1_mcart_1(X1),k2_zfmisc_1(sK0,X3))
      | ~ r2_hidden(X1,X4)
      | ~ v1_relat_1(X4)
      | ~ r2_hidden(X1,k2_zfmisc_1(X5,sK2)) ) ),
    inference(resolution,[],[f169,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f169,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(k2_mcart_1(X0),sK2)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(k1_mcart_1(X0),X1)
      | k2_mcart_1(X0) = sK3
      | sK4 != X0
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X2,sK1))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X3))
      | ~ r2_hidden(X0,X4)
      | ~ v1_relat_1(X4) ) ),
    inference(superposition,[],[f153,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f153,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sK4 != k4_tarski(X0,X2)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,X1)
      | sK3 = X2
      | ~ r2_hidden(X2,sK2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X3,sK1))
      | ~ r2_hidden(X0,k2_zfmisc_1(sK0,X4)) ) ),
    inference(resolution,[],[f143,f58])).

fof(f143,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k1_mcart_1(X1),sK0)
      | ~ r2_hidden(X1,X2)
      | ~ v1_relat_1(X2)
      | sK4 != k4_tarski(X1,X0)
      | sK3 = X0
      | ~ r2_hidden(X0,sK2)
      | ~ r2_hidden(X1,k2_zfmisc_1(X3,sK1)) ) ),
    inference(resolution,[],[f142,f59])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k2_mcart_1(X0),sK1)
      | sK3 = X1
      | ~ r2_hidden(X0,X2)
      | ~ v1_relat_1(X2)
      | k4_tarski(X0,X1) != sK4
      | ~ r2_hidden(k1_mcart_1(X0),sK0)
      | ~ r2_hidden(X1,sK2) ) ),
    inference(resolution,[],[f141,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,sK2)
      | sK4 != k4_tarski(X1,X0)
      | sK3 = X0
      | ~ r2_hidden(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(k2_mcart_1(X1),sK1)
      | ~ r2_hidden(k1_mcart_1(X1),sK0) ) ),
    inference(resolution,[],[f140,f55])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k1_mcart_1(X1),sK0)
      | ~ m1_subset_1(X0,sK2)
      | sK4 != k4_tarski(X1,X0)
      | sK3 = X0
      | ~ r2_hidden(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(k2_mcart_1(X1),sK1) ) ),
    inference(resolution,[],[f139,f55])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k2_mcart_1(X0),sK1)
      | sK3 = X1
      | ~ m1_subset_1(X1,sK2)
      | k4_tarski(X0,X1) != sK4
      | ~ m1_subset_1(k1_mcart_1(X0),sK0)
      | ~ r2_hidden(X0,X2)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f71,f53])).

fof(f71,plain,(
    ! [X6,X7,X5] :
      ( sK4 != k4_tarski(k4_tarski(X5,X6),X7)
      | sK3 = X7
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(definition_unfolding,[],[f40,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f40,plain,(
    ! [X6,X7,X5] :
      ( sK3 = X7
      | k3_mcart_1(X5,X6,X7) != sK4
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n009.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:58:41 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.55  % (31374)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.56  % (31376)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.56  % (31383)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.56  % (31375)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.56  % (31384)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.57  % (31376)Refutation not found, incomplete strategy% (31376)------------------------------
% 0.22/0.57  % (31376)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (31376)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (31376)Memory used [KB]: 10746
% 0.22/0.57  % (31376)Time elapsed: 0.125 s
% 0.22/0.57  % (31376)------------------------------
% 0.22/0.57  % (31376)------------------------------
% 0.22/0.57  % (31392)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.57  % (31382)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.58  % (31390)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.58  % (31391)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.58  % (31391)Refutation not found, incomplete strategy% (31391)------------------------------
% 0.22/0.58  % (31391)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (31391)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (31391)Memory used [KB]: 1791
% 0.22/0.58  % (31391)Time elapsed: 0.149 s
% 0.22/0.58  % (31391)------------------------------
% 0.22/0.58  % (31391)------------------------------
% 0.22/0.58  % (31390)Refutation not found, incomplete strategy% (31390)------------------------------
% 0.22/0.58  % (31390)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (31390)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (31390)Memory used [KB]: 10746
% 0.22/0.58  % (31390)Time elapsed: 0.134 s
% 0.22/0.58  % (31390)------------------------------
% 0.22/0.58  % (31390)------------------------------
% 1.55/0.60  % (31370)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.55/0.61  % (31371)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.55/0.61  % (31373)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.88/0.61  % (31378)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.88/0.61  % (31393)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.88/0.62  % (31387)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.88/0.62  % (31386)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.88/0.62  % (31385)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.88/0.62  % (31381)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.88/0.62  % (31385)Refutation not found, incomplete strategy% (31385)------------------------------
% 1.88/0.62  % (31385)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.88/0.62  % (31385)Termination reason: Refutation not found, incomplete strategy
% 1.88/0.62  
% 1.88/0.62  % (31385)Memory used [KB]: 10618
% 1.88/0.62  % (31385)Time elapsed: 0.144 s
% 1.88/0.62  % (31385)------------------------------
% 1.88/0.62  % (31385)------------------------------
% 1.88/0.62  % (31395)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.88/0.63  % (31369)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.88/0.63  % (31394)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.88/0.63  % (31379)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.88/0.63  % (31397)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.88/0.63  % (31370)Refutation not found, incomplete strategy% (31370)------------------------------
% 1.88/0.63  % (31370)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.88/0.63  % (31370)Termination reason: Refutation not found, incomplete strategy
% 1.88/0.63  
% 1.88/0.63  % (31370)Memory used [KB]: 10746
% 1.88/0.63  % (31370)Time elapsed: 0.175 s
% 1.88/0.63  % (31370)------------------------------
% 1.88/0.63  % (31370)------------------------------
% 1.88/0.63  % (31377)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.88/0.63  % (31389)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.88/0.63  % (31378)Refutation not found, incomplete strategy% (31378)------------------------------
% 1.88/0.63  % (31378)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.88/0.63  % (31378)Termination reason: Refutation not found, incomplete strategy
% 1.88/0.63  
% 1.88/0.63  % (31378)Memory used [KB]: 10618
% 1.88/0.63  % (31378)Time elapsed: 0.197 s
% 1.88/0.63  % (31378)------------------------------
% 1.88/0.63  % (31378)------------------------------
% 1.88/0.63  % (31389)Refutation not found, incomplete strategy% (31389)------------------------------
% 1.88/0.63  % (31389)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.88/0.63  % (31389)Termination reason: Refutation not found, incomplete strategy
% 1.88/0.63  
% 1.88/0.63  % (31389)Memory used [KB]: 1791
% 1.88/0.63  % (31389)Time elapsed: 0.198 s
% 1.88/0.63  % (31389)------------------------------
% 1.88/0.63  % (31389)------------------------------
% 1.88/0.65  % (31377)Refutation not found, incomplete strategy% (31377)------------------------------
% 1.88/0.65  % (31377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.88/0.65  % (31377)Termination reason: Refutation not found, incomplete strategy
% 1.88/0.65  
% 1.88/0.65  % (31377)Memory used [KB]: 10746
% 1.88/0.65  % (31377)Time elapsed: 0.160 s
% 1.88/0.65  % (31377)------------------------------
% 1.88/0.65  % (31377)------------------------------
% 1.88/0.66  % (31371)Refutation found. Thanks to Tanya!
% 1.88/0.66  % SZS status Theorem for theBenchmark
% 1.88/0.66  % SZS output start Proof for theBenchmark
% 1.88/0.66  fof(f406,plain,(
% 1.88/0.66    $false),
% 1.88/0.66    inference(avatar_sat_refutation,[],[f207,f242,f304,f364,f400])).
% 1.88/0.66  fof(f400,plain,(
% 1.88/0.66    ~spl7_10),
% 1.88/0.66    inference(avatar_contradiction_clause,[],[f399])).
% 1.88/0.66  fof(f399,plain,(
% 1.88/0.66    $false | ~spl7_10),
% 1.88/0.66    inference(subsumption_resolution,[],[f398,f41])).
% 1.88/0.66  fof(f41,plain,(
% 1.88/0.66    k1_xboole_0 != sK0),
% 1.88/0.66    inference(cnf_transformation,[],[f30])).
% 1.88/0.66  fof(f30,plain,(
% 1.88/0.66    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 1.88/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f19,f29])).
% 1.88/0.66  fof(f29,plain,(
% 1.88/0.66    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)))),
% 1.88/0.66    introduced(choice_axiom,[])).
% 1.88/0.66  fof(f19,plain,(
% 1.88/0.66    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 1.88/0.66    inference(flattening,[],[f18])).
% 1.88/0.66  fof(f18,plain,(
% 1.88/0.66    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 1.88/0.66    inference(ennf_transformation,[],[f17])).
% 1.88/0.66  fof(f17,negated_conjecture,(
% 1.88/0.66    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.88/0.66    inference(negated_conjecture,[],[f16])).
% 1.88/0.66  fof(f16,conjecture,(
% 1.88/0.66    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.88/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_mcart_1)).
% 1.88/0.66  fof(f398,plain,(
% 1.88/0.66    k1_xboole_0 = sK0 | ~spl7_10),
% 1.88/0.66    inference(subsumption_resolution,[],[f397,f42])).
% 1.88/0.66  fof(f42,plain,(
% 1.88/0.66    k1_xboole_0 != sK1),
% 1.88/0.66    inference(cnf_transformation,[],[f30])).
% 1.88/0.66  fof(f397,plain,(
% 1.88/0.66    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl7_10),
% 1.88/0.66    inference(subsumption_resolution,[],[f396,f43])).
% 1.88/0.66  fof(f43,plain,(
% 1.88/0.66    k1_xboole_0 != sK2),
% 1.88/0.66    inference(cnf_transformation,[],[f30])).
% 1.88/0.66  fof(f396,plain,(
% 1.88/0.66    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl7_10),
% 1.88/0.66    inference(condensation,[],[f395])).
% 1.88/0.66  fof(f395,plain,(
% 1.88/0.66    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) ) | ~spl7_10),
% 1.88/0.66    inference(subsumption_resolution,[],[f392,f93])).
% 1.88/0.66  fof(f93,plain,(
% 1.88/0.66    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.88/0.66    inference(resolution,[],[f91,f49])).
% 1.88/0.66  fof(f49,plain,(
% 1.88/0.66    ( ! [X0] : (r2_hidden(sK6(X0),X0) | k1_xboole_0 = X0) )),
% 1.88/0.66    inference(cnf_transformation,[],[f36])).
% 1.88/0.66  fof(f36,plain,(
% 1.88/0.66    ! [X0] : ((! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != sK6(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK6(X0),X0)) | k1_xboole_0 = X0)),
% 1.88/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f20,f35])).
% 1.88/0.66  fof(f35,plain,(
% 1.88/0.66    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X5,X4,X3,X2] : (k4_mcart_1(X2,X3,X4,X5) != sK6(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK6(X0),X0)))),
% 1.88/0.66    introduced(choice_axiom,[])).
% 1.88/0.66  fof(f20,plain,(
% 1.88/0.66    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.88/0.66    inference(ennf_transformation,[],[f13])).
% 1.88/0.66  fof(f13,axiom,(
% 1.88/0.66    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.88/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).
% 1.88/0.66  fof(f91,plain,(
% 1.88/0.66    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1))) )),
% 1.88/0.66    inference(resolution,[],[f90,f45])).
% 1.88/0.66  fof(f45,plain,(
% 1.88/0.66    v1_xboole_0(k1_xboole_0)),
% 1.88/0.66    inference(cnf_transformation,[],[f2])).
% 1.88/0.66  fof(f2,axiom,(
% 1.88/0.66    v1_xboole_0(k1_xboole_0)),
% 1.88/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.88/0.66  fof(f90,plain,(
% 1.88/0.66    ( ! [X2,X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 1.88/0.66    inference(resolution,[],[f58,f47])).
% 1.88/0.66  fof(f47,plain,(
% 1.88/0.66    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.88/0.66    inference(cnf_transformation,[],[f34])).
% 1.88/0.66  fof(f34,plain,(
% 1.88/0.66    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK5(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.88/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f32,f33])).
% 1.88/0.66  fof(f33,plain,(
% 1.88/0.66    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK5(X0),X0))),
% 1.88/0.66    introduced(choice_axiom,[])).
% 1.88/0.66  fof(f32,plain,(
% 1.88/0.66    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.88/0.66    inference(rectify,[],[f31])).
% 1.88/0.66  fof(f31,plain,(
% 1.88/0.66    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.88/0.66    inference(nnf_transformation,[],[f1])).
% 1.88/0.66  fof(f1,axiom,(
% 1.88/0.66    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.88/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.88/0.66  fof(f58,plain,(
% 1.88/0.66    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 1.88/0.66    inference(cnf_transformation,[],[f26])).
% 1.88/0.66  fof(f26,plain,(
% 1.88/0.66    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.88/0.66    inference(ennf_transformation,[],[f11])).
% 1.88/0.66  fof(f11,axiom,(
% 1.88/0.66    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.88/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.88/0.66  fof(f392,plain,(
% 1.88/0.66    ( ! [X0] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0) | k1_xboole_0 = X0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) ) | ~spl7_10),
% 1.88/0.66    inference(superposition,[],[f81,f387])).
% 1.88/0.66  fof(f387,plain,(
% 1.88/0.66    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl7_10),
% 1.88/0.66    inference(resolution,[],[f379,f87])).
% 1.88/0.66  fof(f87,plain,(
% 1.88/0.66    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.88/0.66    inference(resolution,[],[f49,f47])).
% 1.88/0.66  fof(f379,plain,(
% 1.88/0.66    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl7_10),
% 1.88/0.66    inference(resolution,[],[f373,f72])).
% 1.88/0.66  fof(f72,plain,(
% 1.88/0.66    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.88/0.66    inference(definition_unfolding,[],[f39,f57])).
% 1.88/0.66  fof(f57,plain,(
% 1.88/0.66    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.88/0.66    inference(cnf_transformation,[],[f8])).
% 1.88/0.66  fof(f8,axiom,(
% 1.88/0.66    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.88/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.88/0.66  fof(f39,plain,(
% 1.88/0.66    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 1.88/0.66    inference(cnf_transformation,[],[f30])).
% 1.88/0.66  fof(f373,plain,(
% 1.88/0.66    ( ! [X0,X1] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1))) ) | ~spl7_10),
% 1.88/0.66    inference(resolution,[],[f370,f54])).
% 1.88/0.66  fof(f54,plain,(
% 1.88/0.66    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.88/0.66    inference(cnf_transformation,[],[f24])).
% 1.88/0.66  fof(f24,plain,(
% 1.88/0.66    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.88/0.66    inference(flattening,[],[f23])).
% 1.88/0.66  fof(f23,plain,(
% 1.88/0.66    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.88/0.66    inference(ennf_transformation,[],[f5])).
% 1.88/0.66  fof(f5,axiom,(
% 1.88/0.66    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.88/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.88/0.66  fof(f370,plain,(
% 1.88/0.66    ( ! [X0,X1] : (~r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1))) ) | ~spl7_10),
% 1.88/0.66    inference(resolution,[],[f206,f58])).
% 1.88/0.66  fof(f206,plain,(
% 1.88/0.66    ( ! [X0] : (~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,sK1))) ) | ~spl7_10),
% 1.88/0.66    inference(avatar_component_clause,[],[f205])).
% 1.88/0.66  fof(f205,plain,(
% 1.88/0.66    spl7_10 <=> ! [X0] : ~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,sK1))),
% 1.88/0.66    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 1.88/0.66  fof(f81,plain,(
% 1.88/0.66    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.88/0.66    inference(definition_unfolding,[],[f65,f70])).
% 1.88/0.66  fof(f70,plain,(
% 1.88/0.66    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 1.88/0.66    inference(definition_unfolding,[],[f63,f57])).
% 1.88/0.66  fof(f63,plain,(
% 1.88/0.66    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 1.88/0.66    inference(cnf_transformation,[],[f9])).
% 1.88/0.66  fof(f9,axiom,(
% 1.88/0.66    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 1.88/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 1.88/0.66  fof(f65,plain,(
% 1.88/0.66    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.88/0.66    inference(cnf_transformation,[],[f38])).
% 1.88/0.66  fof(f38,plain,(
% 1.88/0.66    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.88/0.66    inference(flattening,[],[f37])).
% 1.88/0.66  fof(f37,plain,(
% 1.88/0.66    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | (k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.88/0.66    inference(nnf_transformation,[],[f15])).
% 1.88/0.66  fof(f15,axiom,(
% 1.88/0.66    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 1.88/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).
% 1.88/0.66  fof(f364,plain,(
% 1.88/0.66    ~spl7_9),
% 1.88/0.66    inference(avatar_contradiction_clause,[],[f363])).
% 1.88/0.66  fof(f363,plain,(
% 1.88/0.66    $false | ~spl7_9),
% 1.88/0.66    inference(subsumption_resolution,[],[f362,f41])).
% 1.88/0.66  fof(f362,plain,(
% 1.88/0.66    k1_xboole_0 = sK0 | ~spl7_9),
% 1.88/0.66    inference(subsumption_resolution,[],[f361,f42])).
% 1.88/0.66  fof(f361,plain,(
% 1.88/0.66    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl7_9),
% 1.88/0.66    inference(subsumption_resolution,[],[f360,f43])).
% 1.88/0.66  fof(f360,plain,(
% 1.88/0.66    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl7_9),
% 1.88/0.66    inference(condensation,[],[f359])).
% 1.88/0.66  fof(f359,plain,(
% 1.88/0.66    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) ) | ~spl7_9),
% 1.88/0.66    inference(subsumption_resolution,[],[f356,f93])).
% 1.88/0.66  fof(f356,plain,(
% 1.88/0.66    ( ! [X0] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0) | k1_xboole_0 = X0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) ) | ~spl7_9),
% 1.88/0.66    inference(superposition,[],[f81,f351])).
% 1.88/0.66  fof(f351,plain,(
% 1.88/0.66    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl7_9),
% 1.88/0.66    inference(resolution,[],[f343,f87])).
% 1.88/0.66  fof(f343,plain,(
% 1.88/0.66    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl7_9),
% 1.88/0.66    inference(resolution,[],[f337,f72])).
% 1.88/0.66  fof(f337,plain,(
% 1.88/0.66    ( ! [X0,X1] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1))) ) | ~spl7_9),
% 1.88/0.66    inference(resolution,[],[f313,f54])).
% 1.88/0.66  fof(f313,plain,(
% 1.88/0.66    ( ! [X0,X1] : (~r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1))) ) | ~spl7_9),
% 1.88/0.66    inference(resolution,[],[f203,f58])).
% 1.88/0.66  fof(f203,plain,(
% 1.88/0.66    ( ! [X1] : (~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,X1))) ) | ~spl7_9),
% 1.88/0.66    inference(avatar_component_clause,[],[f202])).
% 1.88/0.66  fof(f202,plain,(
% 1.88/0.66    spl7_9 <=> ! [X1] : ~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,X1))),
% 1.88/0.66    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 1.88/0.66  fof(f304,plain,(
% 1.88/0.66    ~spl7_8),
% 1.88/0.66    inference(avatar_contradiction_clause,[],[f303])).
% 1.88/0.66  fof(f303,plain,(
% 1.88/0.66    $false | ~spl7_8),
% 1.88/0.66    inference(subsumption_resolution,[],[f302,f41])).
% 1.88/0.66  fof(f302,plain,(
% 1.88/0.66    k1_xboole_0 = sK0 | ~spl7_8),
% 1.88/0.66    inference(subsumption_resolution,[],[f301,f42])).
% 1.88/0.66  fof(f301,plain,(
% 1.88/0.66    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl7_8),
% 1.88/0.66    inference(subsumption_resolution,[],[f300,f43])).
% 1.88/0.66  fof(f300,plain,(
% 1.88/0.66    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl7_8),
% 1.88/0.66    inference(subsumption_resolution,[],[f299,f72])).
% 1.88/0.66  fof(f299,plain,(
% 1.88/0.66    ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl7_8),
% 1.88/0.66    inference(subsumption_resolution,[],[f294,f200])).
% 1.88/0.66  fof(f200,plain,(
% 1.88/0.66    sK3 = k2_mcart_1(sK4) | ~spl7_8),
% 1.88/0.66    inference(avatar_component_clause,[],[f198])).
% 1.88/0.66  fof(f198,plain,(
% 1.88/0.66    spl7_8 <=> sK3 = k2_mcart_1(sK4)),
% 1.88/0.66    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 1.88/0.66  fof(f294,plain,(
% 1.88/0.66    sK3 != k2_mcart_1(sK4) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.88/0.66    inference(superposition,[],[f44,f73])).
% 1.88/0.66  fof(f73,plain,(
% 1.88/0.66    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.88/0.66    inference(definition_unfolding,[],[f62,f57])).
% 1.88/0.66  fof(f62,plain,(
% 1.88/0.66    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.88/0.66    inference(cnf_transformation,[],[f27])).
% 1.88/0.66  fof(f27,plain,(
% 1.88/0.66    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.88/0.66    inference(ennf_transformation,[],[f14])).
% 1.88/0.66  fof(f14,axiom,(
% 1.88/0.66    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.88/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).
% 1.88/0.66  fof(f44,plain,(
% 1.88/0.66    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)),
% 1.88/0.66    inference(cnf_transformation,[],[f30])).
% 1.88/0.66  fof(f242,plain,(
% 1.88/0.66    ~spl7_7),
% 1.88/0.66    inference(avatar_contradiction_clause,[],[f241])).
% 1.88/0.66  fof(f241,plain,(
% 1.88/0.66    $false | ~spl7_7),
% 1.88/0.66    inference(subsumption_resolution,[],[f240,f41])).
% 1.88/0.66  fof(f240,plain,(
% 1.88/0.66    k1_xboole_0 = sK0 | ~spl7_7),
% 1.88/0.66    inference(subsumption_resolution,[],[f239,f42])).
% 1.88/0.66  fof(f239,plain,(
% 1.88/0.66    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl7_7),
% 1.88/0.66    inference(subsumption_resolution,[],[f238,f43])).
% 1.88/0.66  fof(f238,plain,(
% 1.88/0.66    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl7_7),
% 1.88/0.66    inference(condensation,[],[f237])).
% 1.88/0.66  fof(f237,plain,(
% 1.88/0.66    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) ) | ~spl7_7),
% 1.88/0.66    inference(subsumption_resolution,[],[f229,f93])).
% 1.88/0.66  fof(f229,plain,(
% 1.88/0.66    ( ! [X0] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0) | k1_xboole_0 = X0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) ) | ~spl7_7),
% 1.88/0.66    inference(superposition,[],[f81,f215])).
% 1.88/0.66  fof(f215,plain,(
% 1.88/0.66    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl7_7),
% 1.88/0.66    inference(resolution,[],[f210,f87])).
% 1.88/0.66  fof(f210,plain,(
% 1.88/0.66    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl7_7),
% 1.88/0.66    inference(resolution,[],[f208,f72])).
% 1.88/0.66  fof(f208,plain,(
% 1.88/0.66    ( ! [X0] : (~m1_subset_1(sK4,k2_zfmisc_1(X0,sK2)) | v1_xboole_0(k2_zfmisc_1(X0,sK2))) ) | ~spl7_7),
% 1.88/0.66    inference(resolution,[],[f196,f54])).
% 1.88/0.66  fof(f196,plain,(
% 1.88/0.66    ( ! [X2] : (~r2_hidden(sK4,k2_zfmisc_1(X2,sK2))) ) | ~spl7_7),
% 1.88/0.66    inference(avatar_component_clause,[],[f195])).
% 1.88/0.66  fof(f195,plain,(
% 1.88/0.66    spl7_7 <=> ! [X2] : ~r2_hidden(sK4,k2_zfmisc_1(X2,sK2))),
% 1.88/0.66    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.88/0.66  fof(f207,plain,(
% 1.88/0.66    spl7_7 | spl7_8 | spl7_9 | spl7_10),
% 1.88/0.66    inference(avatar_split_clause,[],[f193,f205,f202,f198,f195])).
% 1.88/0.66  fof(f193,plain,(
% 1.88/0.66    ( ! [X2,X0,X1] : (~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,sK1)) | ~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,X1)) | sK3 = k2_mcart_1(sK4) | ~r2_hidden(sK4,k2_zfmisc_1(X2,sK2))) )),
% 1.88/0.66    inference(equality_resolution,[],[f192])).
% 1.88/0.66  fof(f192,plain,(
% 1.88/0.66    ( ! [X2,X0,X5,X1] : (sK4 != X0 | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X1,sK1)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X2)) | k2_mcart_1(X0) = sK3 | ~r2_hidden(X0,k2_zfmisc_1(X5,sK2))) )),
% 1.88/0.66    inference(condensation,[],[f190])).
% 1.88/0.66  fof(f190,plain,(
% 1.88/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (sK4 != X0 | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X1,sK1)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X2)) | ~r2_hidden(X0,k2_zfmisc_1(X3,X4)) | k2_mcart_1(X0) = sK3 | ~r2_hidden(X0,k2_zfmisc_1(X5,sK2))) )),
% 1.88/0.66    inference(resolution,[],[f189,f52])).
% 1.88/0.66  fof(f52,plain,(
% 1.88/0.66    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.88/0.66    inference(cnf_transformation,[],[f6])).
% 1.88/0.66  fof(f6,axiom,(
% 1.88/0.66    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.88/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.88/0.66  fof(f189,plain,(
% 1.88/0.66    ( ! [X6,X4,X0,X5,X3] : (~v1_relat_1(X5) | sK4 != X0 | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X3,sK1)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X4)) | ~r2_hidden(X0,X5) | k2_mcart_1(X0) = sK3 | ~r2_hidden(X0,k2_zfmisc_1(X6,sK2))) )),
% 1.88/0.66    inference(condensation,[],[f187])).
% 1.88/0.66  fof(f187,plain,(
% 1.88/0.66    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X1,X2)) | k2_mcart_1(X0) = sK3 | sK4 != X0 | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X3,sK1)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X4)) | ~r2_hidden(X0,X5) | ~v1_relat_1(X5) | ~r2_hidden(X0,k2_zfmisc_1(X6,sK2))) )),
% 1.88/0.66    inference(resolution,[],[f171,f52])).
% 1.88/0.66  fof(f171,plain,(
% 1.88/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_relat_1(X0) | ~r2_hidden(k1_mcart_1(X1),X0) | sK3 = k2_mcart_1(X1) | sK4 != X1 | ~r2_hidden(k1_mcart_1(X1),k2_zfmisc_1(X2,sK1)) | ~r2_hidden(k1_mcart_1(X1),k2_zfmisc_1(sK0,X3)) | ~r2_hidden(X1,X4) | ~v1_relat_1(X4) | ~r2_hidden(X1,k2_zfmisc_1(X5,sK2))) )),
% 1.88/0.66    inference(resolution,[],[f169,f59])).
% 1.88/0.66  fof(f59,plain,(
% 1.88/0.66    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 1.88/0.66    inference(cnf_transformation,[],[f26])).
% 1.88/0.66  fof(f169,plain,(
% 1.88/0.66    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(k2_mcart_1(X0),sK2) | ~v1_relat_1(X1) | ~r2_hidden(k1_mcart_1(X0),X1) | k2_mcart_1(X0) = sK3 | sK4 != X0 | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X2,sK1)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X3)) | ~r2_hidden(X0,X4) | ~v1_relat_1(X4)) )),
% 1.88/0.66    inference(superposition,[],[f153,f53])).
% 1.88/0.66  fof(f53,plain,(
% 1.88/0.66    ( ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1)) )),
% 1.88/0.66    inference(cnf_transformation,[],[f22])).
% 1.88/0.66  fof(f22,plain,(
% 1.88/0.66    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 1.88/0.66    inference(flattening,[],[f21])).
% 1.88/0.66  fof(f21,plain,(
% 1.88/0.66    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 1.88/0.66    inference(ennf_transformation,[],[f12])).
% 1.88/0.66  fof(f12,axiom,(
% 1.88/0.66    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 1.88/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).
% 1.88/0.66  fof(f153,plain,(
% 1.88/0.66    ( ! [X4,X2,X0,X3,X1] : (sK4 != k4_tarski(X0,X2) | ~v1_relat_1(X1) | ~r2_hidden(X0,X1) | sK3 = X2 | ~r2_hidden(X2,sK2) | ~r2_hidden(X0,k2_zfmisc_1(X3,sK1)) | ~r2_hidden(X0,k2_zfmisc_1(sK0,X4))) )),
% 1.88/0.66    inference(resolution,[],[f143,f58])).
% 1.88/0.66  fof(f143,plain,(
% 1.88/0.66    ( ! [X2,X0,X3,X1] : (~r2_hidden(k1_mcart_1(X1),sK0) | ~r2_hidden(X1,X2) | ~v1_relat_1(X2) | sK4 != k4_tarski(X1,X0) | sK3 = X0 | ~r2_hidden(X0,sK2) | ~r2_hidden(X1,k2_zfmisc_1(X3,sK1))) )),
% 1.88/0.66    inference(resolution,[],[f142,f59])).
% 1.88/0.66  fof(f142,plain,(
% 1.88/0.66    ( ! [X2,X0,X1] : (~r2_hidden(k2_mcart_1(X0),sK1) | sK3 = X1 | ~r2_hidden(X0,X2) | ~v1_relat_1(X2) | k4_tarski(X0,X1) != sK4 | ~r2_hidden(k1_mcart_1(X0),sK0) | ~r2_hidden(X1,sK2)) )),
% 1.88/0.66    inference(resolution,[],[f141,f55])).
% 1.88/0.66  fof(f55,plain,(
% 1.88/0.66    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.88/0.66    inference(cnf_transformation,[],[f25])).
% 1.88/0.66  fof(f25,plain,(
% 1.88/0.66    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.88/0.66    inference(ennf_transformation,[],[f4])).
% 1.88/0.66  fof(f4,axiom,(
% 1.88/0.66    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.88/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 1.88/0.66  fof(f141,plain,(
% 1.88/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X0,sK2) | sK4 != k4_tarski(X1,X0) | sK3 = X0 | ~r2_hidden(X1,X2) | ~v1_relat_1(X2) | ~r2_hidden(k2_mcart_1(X1),sK1) | ~r2_hidden(k1_mcart_1(X1),sK0)) )),
% 1.88/0.66    inference(resolution,[],[f140,f55])).
% 1.88/0.66  fof(f140,plain,(
% 1.88/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(k1_mcart_1(X1),sK0) | ~m1_subset_1(X0,sK2) | sK4 != k4_tarski(X1,X0) | sK3 = X0 | ~r2_hidden(X1,X2) | ~v1_relat_1(X2) | ~r2_hidden(k2_mcart_1(X1),sK1)) )),
% 1.88/0.66    inference(resolution,[],[f139,f55])).
% 1.88/0.66  fof(f139,plain,(
% 1.88/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(k2_mcart_1(X0),sK1) | sK3 = X1 | ~m1_subset_1(X1,sK2) | k4_tarski(X0,X1) != sK4 | ~m1_subset_1(k1_mcart_1(X0),sK0) | ~r2_hidden(X0,X2) | ~v1_relat_1(X2)) )),
% 1.88/0.66    inference(superposition,[],[f71,f53])).
% 1.88/0.66  fof(f71,plain,(
% 1.88/0.66    ( ! [X6,X7,X5] : (sK4 != k4_tarski(k4_tarski(X5,X6),X7) | sK3 = X7 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 1.88/0.66    inference(definition_unfolding,[],[f40,f56])).
% 1.88/0.66  fof(f56,plain,(
% 1.88/0.66    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 1.88/0.66    inference(cnf_transformation,[],[f7])).
% 1.88/0.66  fof(f7,axiom,(
% 1.88/0.66    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 1.88/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 1.88/0.66  fof(f40,plain,(
% 1.88/0.66    ( ! [X6,X7,X5] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 1.88/0.66    inference(cnf_transformation,[],[f30])).
% 1.88/0.66  % SZS output end Proof for theBenchmark
% 1.88/0.66  % (31371)------------------------------
% 1.88/0.66  % (31371)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.88/0.66  % (31371)Termination reason: Refutation
% 1.88/0.66  
% 1.88/0.66  % (31371)Memory used [KB]: 10874
% 1.88/0.66  % (31371)Time elapsed: 0.210 s
% 1.88/0.66  % (31371)------------------------------
% 1.88/0.66  % (31371)------------------------------
% 1.88/0.66  % (31367)Success in time 0.289 s
%------------------------------------------------------------------------------
