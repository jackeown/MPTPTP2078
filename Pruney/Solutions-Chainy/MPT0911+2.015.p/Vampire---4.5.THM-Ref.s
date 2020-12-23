%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:31 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 349 expanded)
%              Number of leaves         :   26 (  98 expanded)
%              Depth                    :   18
%              Number of atoms          :  547 (2204 expanded)
%              Number of equality atoms :  273 (1255 expanded)
%              Maximal formula depth    :   25 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f291,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f182,f185,f258,f262,f270,f278,f284,f290])).

fof(f290,plain,(
    ~ spl7_3 ),
    inference(avatar_contradiction_clause,[],[f289])).

fof(f289,plain,
    ( $false
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f288,f44])).

fof(f44,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f20,f31])).

fof(f31,plain,
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

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

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
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
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

fof(f288,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f285,f43])).

fof(f43,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f32])).

fof(f285,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ spl7_3 ),
    inference(resolution,[],[f245,f75])).

fof(f75,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f41,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f41,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f32])).

fof(f245,plain,
    ( ! [X8,X9] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X8,X9),sK2))
        | k1_xboole_0 = X8
        | k1_xboole_0 = X9 )
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f244])).

fof(f244,plain,
    ( spl7_3
  <=> ! [X9,X8] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X8,X9),sK2))
        | k1_xboole_0 = X8
        | k1_xboole_0 = X9 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f284,plain,(
    ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f283])).

fof(f283,plain,
    ( $false
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f282,f45])).

fof(f45,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f32])).

fof(f282,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f279,f44])).

fof(f279,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | ~ spl7_7 ),
    inference(resolution,[],[f257,f75])).

fof(f257,plain,
    ( ! [X0,X3] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X3))
        | k1_xboole_0 = X0
        | k1_xboole_0 = X3 )
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f256])).

fof(f256,plain,
    ( spl7_7
  <=> ! [X3,X0] :
        ( k1_xboole_0 = X0
        | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X3))
        | k1_xboole_0 = X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f278,plain,(
    ~ spl7_6 ),
    inference(avatar_contradiction_clause,[],[f277])).

fof(f277,plain,
    ( $false
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f276,f45])).

fof(f276,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f273,f43])).

fof(f273,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl7_6 ),
    inference(resolution,[],[f254,f75])).

fof(f254,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X2,sK1),X1))
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1 )
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f253])).

fof(f253,plain,
    ( spl7_6
  <=> ! [X1,X2] :
        ( k1_xboole_0 = X1
        | k1_xboole_0 = X2
        | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X2,sK1),X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f270,plain,
    ( ~ spl7_1
    | ~ spl7_5 ),
    inference(avatar_contradiction_clause,[],[f266])).

fof(f266,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_5 ),
    inference(resolution,[],[f263,f98])).

fof(f98,plain,
    ( r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl7_1
  <=> r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f263,plain,
    ( ! [X2,X0,X1] : ~ r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
    | ~ spl7_5 ),
    inference(resolution,[],[f251,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f251,plain,
    ( ! [X4,X5] : ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X4,X5))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f250])).

fof(f250,plain,
    ( spl7_5
  <=> ! [X5,X4] : ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f262,plain,
    ( ~ spl7_1
    | ~ spl7_4 ),
    inference(avatar_contradiction_clause,[],[f259])).

fof(f259,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_4 ),
    inference(resolution,[],[f248,f98])).

fof(f248,plain,
    ( ! [X6,X7] : ~ r2_hidden(sK4,k2_zfmisc_1(X6,X7))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f247])).

fof(f247,plain,
    ( spl7_4
  <=> ! [X7,X6] : ~ r2_hidden(sK4,k2_zfmisc_1(X6,X7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f258,plain,
    ( spl7_3
    | spl7_4
    | spl7_5
    | spl7_6
    | spl7_7 ),
    inference(avatar_split_clause,[],[f242,f256,f253,f250,f247,f244])).

fof(f242,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X3))
      | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X2,sK1),X1))
      | ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X4,X5))
      | ~ r2_hidden(sK4,k2_zfmisc_1(X6,X7))
      | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X8,X9),sK2))
      | k1_xboole_0 = X9
      | k1_xboole_0 = X8 ) ),
    inference(subsumption_resolution,[],[f241,f199])).

fof(f199,plain,(
    sK3 != k2_mcart_1(sK4) ),
    inference(subsumption_resolution,[],[f198,f43])).

fof(f198,plain,
    ( sK3 != k2_mcart_1(sK4)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f197,f44])).

fof(f197,plain,
    ( sK3 != k2_mcart_1(sK4)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f196,f45])).

fof(f196,plain,
    ( sK3 != k2_mcart_1(sK4)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f191,f75])).

fof(f191,plain,
    ( sK3 != k2_mcart_1(sK4)
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f46,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f63,f58])).

fof(f63,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f46,plain,(
    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f241,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | sK3 = k2_mcart_1(sK4)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X3))
      | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X2,sK1),X1))
      | ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X4,X5))
      | ~ r2_hidden(sK4,k2_zfmisc_1(X6,X7))
      | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X8,X9),sK2))
      | k1_xboole_0 = X9
      | k1_xboole_0 = X8 ) ),
    inference(equality_resolution,[],[f233])).

fof(f233,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] :
      ( sK4 != X4
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | sK3 = k2_mcart_1(X4)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(sK0,X1),X0))
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X3,sK1),X2))
      | ~ r2_hidden(k1_mcart_1(X4),k2_zfmisc_1(X5,X6))
      | ~ r2_hidden(X4,k2_zfmisc_1(X7,X8))
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X9,X10),sK2))
      | k1_xboole_0 = X10
      | k1_xboole_0 = X9 ) ),
    inference(subsumption_resolution,[],[f231,f45])).

fof(f231,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | sK3 = k2_mcart_1(X4)
      | sK4 != X4
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(sK0,X1),X0))
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X3,sK1),X2))
      | ~ r2_hidden(k1_mcart_1(X4),k2_zfmisc_1(X5,X6))
      | ~ r2_hidden(X4,k2_zfmisc_1(X7,X8))
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X9,X10),sK2))
      | k1_xboole_0 = sK2
      | k1_xboole_0 = X10
      | k1_xboole_0 = X9 ) ),
    inference(resolution,[],[f229,f194])).

fof(f194,plain,(
    ! [X6,X4,X7,X5] :
      ( m1_subset_1(k2_mcart_1(X7),X6)
      | ~ m1_subset_1(X7,k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6))
      | k1_xboole_0 = X6
      | k1_xboole_0 = X5
      | k1_xboole_0 = X4 ) ),
    inference(duplicate_literal_removal,[],[f193])).

fof(f193,plain,(
    ! [X6,X4,X7,X5] :
      ( m1_subset_1(k2_mcart_1(X7),X6)
      | ~ m1_subset_1(X7,k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6))
      | ~ m1_subset_1(X7,k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6))
      | k1_xboole_0 = X6
      | k1_xboole_0 = X5
      | k1_xboole_0 = X4 ) ),
    inference(superposition,[],[f81,f76])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f67,f58])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_mcart_1)).

fof(f229,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(k2_mcart_1(X0),sK2)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X4
      | k2_mcart_1(X0) = sK3
      | sK4 != X0
      | ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,X2),X1))
      | ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X4,sK1),X3))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X5,X6))
      | ~ r2_hidden(X0,k2_zfmisc_1(X7,X8)) ) ),
    inference(superposition,[],[f226,f153])).

fof(f153,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(resolution,[],[f55,f54])).

fof(f54,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,X1)
      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f226,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( sK4 != k4_tarski(k1_mcart_1(X0),X5)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X3
      | k1_xboole_0 = X4
      | sK3 = X5
      | ~ m1_subset_1(X5,sK2)
      | ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,X1),X2))
      | ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X4,sK1),X3))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X6,X7)) ) ),
    inference(subsumption_resolution,[],[f223,f43])).

fof(f223,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = sK0
      | k1_xboole_0 = X3
      | k1_xboole_0 = X4
      | sK3 = X5
      | ~ m1_subset_1(X5,sK2)
      | sK4 != k4_tarski(k1_mcart_1(X0),X5)
      | ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X4,sK1),X3))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X6,X7)) ) ),
    inference(resolution,[],[f220,f214])).

fof(f214,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(k1_mcart_1(k1_mcart_1(X0)),sK0)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | sK3 = X3
      | ~ m1_subset_1(X3,sK2)
      | sK4 != k4_tarski(k1_mcart_1(X0),X3)
      | ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,sK1),X2))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X4,X5)) ) ),
    inference(subsumption_resolution,[],[f212,f44])).

fof(f212,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,sK1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = sK1
      | k1_xboole_0 = X1
      | sK3 = X3
      | ~ m1_subset_1(X3,sK2)
      | sK4 != k4_tarski(k1_mcart_1(X0),X3)
      | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(X0)),sK0)
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X4,X5)) ) ),
    inference(resolution,[],[f209,f155])).

fof(f155,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(k2_mcart_1(X0),sK1)
      | sK3 = X1
      | ~ m1_subset_1(X1,sK2)
      | k4_tarski(X0,X1) != sK4
      | ~ m1_subset_1(k1_mcart_1(X0),sK0)
      | ~ r2_hidden(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(superposition,[],[f74,f153])).

fof(f74,plain,(
    ! [X6,X7,X5] :
      ( sK4 != k4_tarski(k4_tarski(X5,X6),X7)
      | sK3 = X7
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(definition_unfolding,[],[f42,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f42,plain,(
    ! [X6,X7,X5] :
      ( sK3 = X7
      | k3_mcart_1(X5,X6,X7) != sK4
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f209,plain,(
    ! [X6,X4,X7,X5] :
      ( m1_subset_1(k2_mcart_1(k1_mcart_1(X7)),X5)
      | ~ m1_subset_1(X7,k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6))
      | k1_xboole_0 = X6
      | k1_xboole_0 = X5
      | k1_xboole_0 = X4 ) ),
    inference(duplicate_literal_removal,[],[f208])).

fof(f208,plain,(
    ! [X6,X4,X7,X5] :
      ( m1_subset_1(k2_mcart_1(k1_mcart_1(X7)),X5)
      | ~ m1_subset_1(X7,k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6))
      | ~ m1_subset_1(X7,k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6))
      | k1_xboole_0 = X6
      | k1_xboole_0 = X5
      | k1_xboole_0 = X4 ) ),
    inference(superposition,[],[f80,f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f62,f58])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f66,f58])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_mcart_1)).

fof(f220,plain,(
    ! [X6,X4,X7,X5] :
      ( m1_subset_1(k1_mcart_1(k1_mcart_1(X7)),X4)
      | ~ m1_subset_1(X7,k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6))
      | k1_xboole_0 = X6
      | k1_xboole_0 = X5
      | k1_xboole_0 = X4 ) ),
    inference(duplicate_literal_removal,[],[f219])).

fof(f219,plain,(
    ! [X6,X4,X7,X5] :
      ( m1_subset_1(k1_mcart_1(k1_mcart_1(X7)),X4)
      | ~ m1_subset_1(X7,k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6))
      | ~ m1_subset_1(X7,k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6))
      | k1_xboole_0 = X6
      | k1_xboole_0 = X5
      | k1_xboole_0 = X4 ) ),
    inference(superposition,[],[f79,f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f61,f58])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f65,f58])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_mcart_1)).

fof(f185,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f184,f100,f96])).

fof(f100,plain,
    ( spl7_2
  <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f184,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f75,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f182,plain,(
    ~ spl7_2 ),
    inference(avatar_contradiction_clause,[],[f181])).

fof(f181,plain,
    ( $false
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f180,f43])).

fof(f180,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f179,f44])).

fof(f179,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f178,f45])).

fof(f178,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_2 ),
    inference(condensation,[],[f177])).

fof(f177,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 = sK2
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0 )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f169,f112])).

fof(f112,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(resolution,[],[f110,f50])).

fof(f50,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK6(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK6(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f21,f37])).

fof(f37,plain,(
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

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).

fof(f110,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1)) ),
    inference(resolution,[],[f109,f47])).

fof(f47,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(resolution,[],[f59,f48])).

fof(f48,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK5(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
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

fof(f169,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0)
        | k1_xboole_0 = X0
        | k1_xboole_0 = sK2
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0 )
    | ~ spl7_2 ),
    inference(superposition,[],[f86,f104])).

fof(f104,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl7_2 ),
    inference(resolution,[],[f102,f92])).

fof(f92,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f50,f48])).

fof(f102,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f100])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f68,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f64,f58])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:24:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (12686)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.50  % (12678)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.50  % (12670)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.50  % (12686)Refutation not found, incomplete strategy% (12686)------------------------------
% 0.21/0.50  % (12686)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (12686)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (12686)Memory used [KB]: 10746
% 0.21/0.50  % (12686)Time elapsed: 0.054 s
% 0.21/0.50  % (12686)------------------------------
% 0.21/0.50  % (12686)------------------------------
% 0.21/0.51  % (12679)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (12668)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (12665)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (12669)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (12667)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (12666)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (12666)Refutation not found, incomplete strategy% (12666)------------------------------
% 0.21/0.52  % (12666)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (12671)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (12692)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (12693)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (12682)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (12681)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (12684)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (12687)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (12685)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (12672)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (12664)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (12664)Refutation not found, incomplete strategy% (12664)------------------------------
% 0.21/0.53  % (12664)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (12664)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (12664)Memory used [KB]: 1663
% 0.21/0.53  % (12664)Time elapsed: 0.118 s
% 0.21/0.53  % (12664)------------------------------
% 0.21/0.53  % (12664)------------------------------
% 0.21/0.53  % (12674)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.30/0.53  % (12676)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.30/0.53  % (12673)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.30/0.53  % (12675)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.30/0.54  % (12688)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.30/0.54  % (12690)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.30/0.54  % (12677)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.30/0.54  % (12680)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.30/0.54  % (12683)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.30/0.54  % (12666)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.54  
% 1.30/0.54  % (12666)Memory used [KB]: 10746
% 1.30/0.54  % (12666)Time elapsed: 0.110 s
% 1.30/0.54  % (12666)------------------------------
% 1.30/0.54  % (12666)------------------------------
% 1.30/0.54  % (12689)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.30/0.54  % (12672)Refutation not found, incomplete strategy% (12672)------------------------------
% 1.30/0.54  % (12672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (12672)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.54  
% 1.30/0.54  % (12672)Memory used [KB]: 10746
% 1.30/0.54  % (12672)Time elapsed: 0.133 s
% 1.30/0.54  % (12672)------------------------------
% 1.30/0.54  % (12672)------------------------------
% 1.30/0.54  % (12687)Refutation not found, incomplete strategy% (12687)------------------------------
% 1.30/0.54  % (12687)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (12674)Refutation not found, incomplete strategy% (12674)------------------------------
% 1.30/0.54  % (12674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (12687)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.54  
% 1.30/0.54  % (12687)Memory used [KB]: 1791
% 1.30/0.54  % (12687)Time elapsed: 0.117 s
% 1.30/0.54  % (12687)------------------------------
% 1.30/0.54  % (12687)------------------------------
% 1.30/0.54  % (12674)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.54  
% 1.30/0.54  % (12674)Memory used [KB]: 10618
% 1.30/0.54  % (12674)Time elapsed: 0.124 s
% 1.30/0.54  % (12674)------------------------------
% 1.30/0.54  % (12674)------------------------------
% 1.30/0.55  % (12691)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.30/0.55  % (12681)Refutation not found, incomplete strategy% (12681)------------------------------
% 1.30/0.55  % (12681)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.55  % (12681)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.55  
% 1.30/0.55  % (12681)Memory used [KB]: 10618
% 1.30/0.55  % (12681)Time elapsed: 0.142 s
% 1.30/0.55  % (12681)------------------------------
% 1.30/0.55  % (12681)------------------------------
% 1.30/0.55  % (12667)Refutation found. Thanks to Tanya!
% 1.30/0.55  % SZS status Theorem for theBenchmark
% 1.30/0.55  % (12673)Refutation not found, incomplete strategy% (12673)------------------------------
% 1.30/0.55  % (12673)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.55  % (12673)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.55  
% 1.30/0.55  % (12673)Memory used [KB]: 10618
% 1.30/0.55  % (12673)Time elapsed: 0.144 s
% 1.30/0.55  % (12673)------------------------------
% 1.30/0.55  % (12673)------------------------------
% 1.30/0.55  % (12684)Refutation not found, incomplete strategy% (12684)------------------------------
% 1.30/0.55  % (12684)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.55  % (12684)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.55  
% 1.30/0.55  % (12684)Memory used [KB]: 10874
% 1.30/0.55  % (12684)Time elapsed: 0.128 s
% 1.30/0.55  % (12684)------------------------------
% 1.30/0.55  % (12684)------------------------------
% 1.30/0.55  % (12685)Refutation not found, incomplete strategy% (12685)------------------------------
% 1.30/0.55  % (12685)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.55  % (12685)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.55  
% 1.30/0.55  % (12685)Memory used [KB]: 1791
% 1.30/0.55  % (12685)Time elapsed: 0.125 s
% 1.30/0.55  % (12685)------------------------------
% 1.30/0.55  % (12685)------------------------------
% 1.49/0.56  % SZS output start Proof for theBenchmark
% 1.49/0.56  fof(f291,plain,(
% 1.49/0.56    $false),
% 1.49/0.56    inference(avatar_sat_refutation,[],[f182,f185,f258,f262,f270,f278,f284,f290])).
% 1.49/0.56  fof(f290,plain,(
% 1.49/0.56    ~spl7_3),
% 1.49/0.56    inference(avatar_contradiction_clause,[],[f289])).
% 1.49/0.56  fof(f289,plain,(
% 1.49/0.56    $false | ~spl7_3),
% 1.49/0.56    inference(subsumption_resolution,[],[f288,f44])).
% 1.49/0.56  fof(f44,plain,(
% 1.49/0.56    k1_xboole_0 != sK1),
% 1.49/0.56    inference(cnf_transformation,[],[f32])).
% 1.49/0.56  fof(f32,plain,(
% 1.49/0.56    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 1.49/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f20,f31])).
% 1.49/0.56  fof(f31,plain,(
% 1.49/0.56    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)))),
% 1.49/0.56    introduced(choice_axiom,[])).
% 1.49/0.56  fof(f20,plain,(
% 1.49/0.56    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 1.49/0.56    inference(flattening,[],[f19])).
% 1.49/0.56  fof(f19,plain,(
% 1.49/0.56    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 1.49/0.56    inference(ennf_transformation,[],[f18])).
% 1.49/0.56  fof(f18,negated_conjecture,(
% 1.49/0.56    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.49/0.56    inference(negated_conjecture,[],[f17])).
% 1.49/0.56  fof(f17,conjecture,(
% 1.49/0.56    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_mcart_1)).
% 1.49/0.56  fof(f288,plain,(
% 1.49/0.56    k1_xboole_0 = sK1 | ~spl7_3),
% 1.49/0.56    inference(subsumption_resolution,[],[f285,f43])).
% 1.49/0.56  fof(f43,plain,(
% 1.49/0.56    k1_xboole_0 != sK0),
% 1.49/0.56    inference(cnf_transformation,[],[f32])).
% 1.49/0.56  fof(f285,plain,(
% 1.49/0.56    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | ~spl7_3),
% 1.49/0.56    inference(resolution,[],[f245,f75])).
% 1.49/0.56  fof(f75,plain,(
% 1.49/0.56    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.49/0.56    inference(definition_unfolding,[],[f41,f58])).
% 1.49/0.56  fof(f58,plain,(
% 1.49/0.56    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f7])).
% 1.49/0.56  fof(f7,axiom,(
% 1.49/0.56    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.49/0.56  fof(f41,plain,(
% 1.49/0.56    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 1.49/0.56    inference(cnf_transformation,[],[f32])).
% 1.49/0.56  fof(f245,plain,(
% 1.49/0.56    ( ! [X8,X9] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X8,X9),sK2)) | k1_xboole_0 = X8 | k1_xboole_0 = X9) ) | ~spl7_3),
% 1.49/0.56    inference(avatar_component_clause,[],[f244])).
% 1.49/0.56  fof(f244,plain,(
% 1.49/0.56    spl7_3 <=> ! [X9,X8] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X8,X9),sK2)) | k1_xboole_0 = X8 | k1_xboole_0 = X9)),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.49/0.56  fof(f284,plain,(
% 1.49/0.56    ~spl7_7),
% 1.49/0.56    inference(avatar_contradiction_clause,[],[f283])).
% 1.49/0.56  fof(f283,plain,(
% 1.49/0.56    $false | ~spl7_7),
% 1.49/0.56    inference(subsumption_resolution,[],[f282,f45])).
% 1.49/0.56  fof(f45,plain,(
% 1.49/0.56    k1_xboole_0 != sK2),
% 1.49/0.56    inference(cnf_transformation,[],[f32])).
% 1.49/0.56  fof(f282,plain,(
% 1.49/0.56    k1_xboole_0 = sK2 | ~spl7_7),
% 1.49/0.56    inference(subsumption_resolution,[],[f279,f44])).
% 1.49/0.56  fof(f279,plain,(
% 1.49/0.56    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | ~spl7_7),
% 1.49/0.56    inference(resolution,[],[f257,f75])).
% 1.49/0.56  fof(f257,plain,(
% 1.49/0.56    ( ! [X0,X3] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X3) ) | ~spl7_7),
% 1.49/0.56    inference(avatar_component_clause,[],[f256])).
% 1.49/0.56  fof(f256,plain,(
% 1.49/0.56    spl7_7 <=> ! [X3,X0] : (k1_xboole_0 = X0 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X3)) | k1_xboole_0 = X3)),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.49/0.56  fof(f278,plain,(
% 1.49/0.56    ~spl7_6),
% 1.49/0.56    inference(avatar_contradiction_clause,[],[f277])).
% 1.49/0.56  fof(f277,plain,(
% 1.49/0.56    $false | ~spl7_6),
% 1.49/0.56    inference(subsumption_resolution,[],[f276,f45])).
% 1.49/0.56  fof(f276,plain,(
% 1.49/0.56    k1_xboole_0 = sK2 | ~spl7_6),
% 1.49/0.56    inference(subsumption_resolution,[],[f273,f43])).
% 1.49/0.56  fof(f273,plain,(
% 1.49/0.56    k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~spl7_6),
% 1.49/0.56    inference(resolution,[],[f254,f75])).
% 1.49/0.56  fof(f254,plain,(
% 1.49/0.56    ( ! [X2,X1] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X2,sK1),X1)) | k1_xboole_0 = X2 | k1_xboole_0 = X1) ) | ~spl7_6),
% 1.49/0.56    inference(avatar_component_clause,[],[f253])).
% 1.49/0.56  fof(f253,plain,(
% 1.49/0.56    spl7_6 <=> ! [X1,X2] : (k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X2,sK1),X1)))),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.49/0.56  fof(f270,plain,(
% 1.49/0.56    ~spl7_1 | ~spl7_5),
% 1.49/0.56    inference(avatar_contradiction_clause,[],[f266])).
% 1.49/0.56  fof(f266,plain,(
% 1.49/0.56    $false | (~spl7_1 | ~spl7_5)),
% 1.49/0.56    inference(resolution,[],[f263,f98])).
% 1.49/0.56  fof(f98,plain,(
% 1.49/0.56    r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl7_1),
% 1.49/0.56    inference(avatar_component_clause,[],[f96])).
% 1.49/0.56  fof(f96,plain,(
% 1.49/0.56    spl7_1 <=> r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.49/0.56  fof(f263,plain,(
% 1.49/0.56    ( ! [X2,X0,X1] : (~r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) ) | ~spl7_5),
% 1.49/0.56    inference(resolution,[],[f251,f59])).
% 1.49/0.56  fof(f59,plain,(
% 1.49/0.56    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 1.49/0.56    inference(cnf_transformation,[],[f26])).
% 1.49/0.56  fof(f26,plain,(
% 1.49/0.56    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.49/0.56    inference(ennf_transformation,[],[f12])).
% 1.49/0.56  fof(f12,axiom,(
% 1.49/0.56    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.49/0.56  fof(f251,plain,(
% 1.49/0.56    ( ! [X4,X5] : (~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X4,X5))) ) | ~spl7_5),
% 1.49/0.56    inference(avatar_component_clause,[],[f250])).
% 1.49/0.56  fof(f250,plain,(
% 1.49/0.56    spl7_5 <=> ! [X5,X4] : ~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X4,X5))),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.49/0.56  fof(f262,plain,(
% 1.49/0.56    ~spl7_1 | ~spl7_4),
% 1.49/0.56    inference(avatar_contradiction_clause,[],[f259])).
% 1.49/0.56  fof(f259,plain,(
% 1.49/0.56    $false | (~spl7_1 | ~spl7_4)),
% 1.49/0.56    inference(resolution,[],[f248,f98])).
% 1.49/0.56  fof(f248,plain,(
% 1.49/0.56    ( ! [X6,X7] : (~r2_hidden(sK4,k2_zfmisc_1(X6,X7))) ) | ~spl7_4),
% 1.49/0.56    inference(avatar_component_clause,[],[f247])).
% 1.49/0.56  fof(f247,plain,(
% 1.49/0.56    spl7_4 <=> ! [X7,X6] : ~r2_hidden(sK4,k2_zfmisc_1(X6,X7))),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.49/0.56  fof(f258,plain,(
% 1.49/0.56    spl7_3 | spl7_4 | spl7_5 | spl7_6 | spl7_7),
% 1.49/0.56    inference(avatar_split_clause,[],[f242,f256,f253,f250,f247,f244])).
% 1.49/0.56  fof(f242,plain,(
% 1.49/0.56    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X3)) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X2,sK1),X1)) | ~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X4,X5)) | ~r2_hidden(sK4,k2_zfmisc_1(X6,X7)) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X8,X9),sK2)) | k1_xboole_0 = X9 | k1_xboole_0 = X8) )),
% 1.49/0.56    inference(subsumption_resolution,[],[f241,f199])).
% 1.49/0.56  fof(f199,plain,(
% 1.49/0.56    sK3 != k2_mcart_1(sK4)),
% 1.49/0.56    inference(subsumption_resolution,[],[f198,f43])).
% 1.49/0.56  fof(f198,plain,(
% 1.49/0.56    sK3 != k2_mcart_1(sK4) | k1_xboole_0 = sK0),
% 1.49/0.56    inference(subsumption_resolution,[],[f197,f44])).
% 1.49/0.56  fof(f197,plain,(
% 1.49/0.56    sK3 != k2_mcart_1(sK4) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.49/0.56    inference(subsumption_resolution,[],[f196,f45])).
% 1.49/0.56  fof(f196,plain,(
% 1.49/0.56    sK3 != k2_mcart_1(sK4) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.49/0.56    inference(subsumption_resolution,[],[f191,f75])).
% 1.49/0.56  fof(f191,plain,(
% 1.49/0.56    sK3 != k2_mcart_1(sK4) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.49/0.56    inference(superposition,[],[f46,f76])).
% 1.49/0.56  fof(f76,plain,(
% 1.49/0.56    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.49/0.56    inference(definition_unfolding,[],[f63,f58])).
% 1.49/0.56  fof(f63,plain,(
% 1.49/0.56    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.49/0.56    inference(cnf_transformation,[],[f27])).
% 1.49/0.56  fof(f27,plain,(
% 1.49/0.56    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.49/0.56    inference(ennf_transformation,[],[f15])).
% 1.49/0.56  fof(f15,axiom,(
% 1.49/0.56    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).
% 1.49/0.56  fof(f46,plain,(
% 1.49/0.56    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)),
% 1.49/0.56    inference(cnf_transformation,[],[f32])).
% 1.49/0.56  fof(f241,plain,(
% 1.49/0.56    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | sK3 = k2_mcart_1(sK4) | k1_xboole_0 = X3 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X3)) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X2,sK1),X1)) | ~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X4,X5)) | ~r2_hidden(sK4,k2_zfmisc_1(X6,X7)) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X8,X9),sK2)) | k1_xboole_0 = X9 | k1_xboole_0 = X8) )),
% 1.49/0.56    inference(equality_resolution,[],[f233])).
% 1.49/0.56  fof(f233,plain,(
% 1.49/0.56    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] : (sK4 != X4 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | sK3 = k2_mcart_1(X4) | k1_xboole_0 = X0 | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(sK0,X1),X0)) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X3,sK1),X2)) | ~r2_hidden(k1_mcart_1(X4),k2_zfmisc_1(X5,X6)) | ~r2_hidden(X4,k2_zfmisc_1(X7,X8)) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X9,X10),sK2)) | k1_xboole_0 = X10 | k1_xboole_0 = X9) )),
% 1.49/0.56    inference(subsumption_resolution,[],[f231,f45])).
% 1.49/0.56  fof(f231,plain,(
% 1.49/0.56    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | sK3 = k2_mcart_1(X4) | sK4 != X4 | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(sK0,X1),X0)) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X3,sK1),X2)) | ~r2_hidden(k1_mcart_1(X4),k2_zfmisc_1(X5,X6)) | ~r2_hidden(X4,k2_zfmisc_1(X7,X8)) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X9,X10),sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = X10 | k1_xboole_0 = X9) )),
% 1.49/0.56    inference(resolution,[],[f229,f194])).
% 1.49/0.56  fof(f194,plain,(
% 1.49/0.56    ( ! [X6,X4,X7,X5] : (m1_subset_1(k2_mcart_1(X7),X6) | ~m1_subset_1(X7,k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6)) | k1_xboole_0 = X6 | k1_xboole_0 = X5 | k1_xboole_0 = X4) )),
% 1.49/0.56    inference(duplicate_literal_removal,[],[f193])).
% 1.49/0.56  fof(f193,plain,(
% 1.49/0.56    ( ! [X6,X4,X7,X5] : (m1_subset_1(k2_mcart_1(X7),X6) | ~m1_subset_1(X7,k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6)) | ~m1_subset_1(X7,k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6)) | k1_xboole_0 = X6 | k1_xboole_0 = X5 | k1_xboole_0 = X4) )),
% 1.49/0.56    inference(superposition,[],[f81,f76])).
% 1.49/0.56  fof(f81,plain,(
% 1.49/0.56    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 1.49/0.56    inference(definition_unfolding,[],[f67,f58])).
% 1.49/0.56  fof(f67,plain,(
% 1.49/0.56    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 1.49/0.56    inference(cnf_transformation,[],[f30])).
% 1.49/0.56  fof(f30,plain,(
% 1.49/0.56    ! [X0,X1,X2,X3] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 1.49/0.56    inference(ennf_transformation,[],[f11])).
% 1.49/0.56  fof(f11,axiom,(
% 1.49/0.56    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_mcart_1)).
% 1.49/0.56  fof(f229,plain,(
% 1.49/0.56    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(k2_mcart_1(X0),sK2) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X4 | k2_mcart_1(X0) = sK3 | sK4 != X0 | ~m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,X2),X1)) | ~m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X4,sK1),X3)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X5,X6)) | ~r2_hidden(X0,k2_zfmisc_1(X7,X8))) )),
% 1.49/0.56    inference(superposition,[],[f226,f153])).
% 1.49/0.56  fof(f153,plain,(
% 1.49/0.56    ( ! [X2,X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 1.49/0.56    inference(resolution,[],[f55,f54])).
% 1.49/0.56  fof(f54,plain,(
% 1.49/0.56    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.49/0.56    inference(cnf_transformation,[],[f5])).
% 1.49/0.56  fof(f5,axiom,(
% 1.49/0.56    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.49/0.56  fof(f55,plain,(
% 1.49/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r2_hidden(X0,X1) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0) )),
% 1.49/0.56    inference(cnf_transformation,[],[f23])).
% 1.49/0.56  fof(f23,plain,(
% 1.49/0.56    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 1.49/0.56    inference(flattening,[],[f22])).
% 1.49/0.56  fof(f22,plain,(
% 1.49/0.56    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 1.49/0.56    inference(ennf_transformation,[],[f13])).
% 1.49/0.56  fof(f13,axiom,(
% 1.49/0.56    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).
% 1.49/0.56  fof(f226,plain,(
% 1.49/0.56    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sK4 != k4_tarski(k1_mcart_1(X0),X5) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X3 | k1_xboole_0 = X4 | sK3 = X5 | ~m1_subset_1(X5,sK2) | ~m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,X1),X2)) | ~m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X4,sK1),X3)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X6,X7))) )),
% 1.49/0.56    inference(subsumption_resolution,[],[f223,f43])).
% 1.49/0.56  fof(f223,plain,(
% 1.49/0.56    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (~m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = sK0 | k1_xboole_0 = X3 | k1_xboole_0 = X4 | sK3 = X5 | ~m1_subset_1(X5,sK2) | sK4 != k4_tarski(k1_mcart_1(X0),X5) | ~m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X4,sK1),X3)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X6,X7))) )),
% 1.49/0.56    inference(resolution,[],[f220,f214])).
% 1.49/0.56  fof(f214,plain,(
% 1.49/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k1_mcart_1(k1_mcart_1(X0)),sK0) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | sK3 = X3 | ~m1_subset_1(X3,sK2) | sK4 != k4_tarski(k1_mcart_1(X0),X3) | ~m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,sK1),X2)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X4,X5))) )),
% 1.49/0.56    inference(subsumption_resolution,[],[f212,f44])).
% 1.49/0.56  fof(f212,plain,(
% 1.49/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,sK1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = sK1 | k1_xboole_0 = X1 | sK3 = X3 | ~m1_subset_1(X3,sK2) | sK4 != k4_tarski(k1_mcart_1(X0),X3) | ~m1_subset_1(k1_mcart_1(k1_mcart_1(X0)),sK0) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X4,X5))) )),
% 1.49/0.56    inference(resolution,[],[f209,f155])).
% 1.49/0.56  fof(f155,plain,(
% 1.49/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(k2_mcart_1(X0),sK1) | sK3 = X1 | ~m1_subset_1(X1,sK2) | k4_tarski(X0,X1) != sK4 | ~m1_subset_1(k1_mcart_1(X0),sK0) | ~r2_hidden(X0,k2_zfmisc_1(X2,X3))) )),
% 1.49/0.56    inference(superposition,[],[f74,f153])).
% 1.49/0.56  fof(f74,plain,(
% 1.49/0.56    ( ! [X6,X7,X5] : (sK4 != k4_tarski(k4_tarski(X5,X6),X7) | sK3 = X7 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 1.49/0.56    inference(definition_unfolding,[],[f42,f57])).
% 1.49/0.56  fof(f57,plain,(
% 1.49/0.56    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f6])).
% 1.49/0.56  fof(f6,axiom,(
% 1.49/0.56    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 1.49/0.56  fof(f42,plain,(
% 1.49/0.56    ( ! [X6,X7,X5] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f32])).
% 1.49/0.56  fof(f209,plain,(
% 1.49/0.56    ( ! [X6,X4,X7,X5] : (m1_subset_1(k2_mcart_1(k1_mcart_1(X7)),X5) | ~m1_subset_1(X7,k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6)) | k1_xboole_0 = X6 | k1_xboole_0 = X5 | k1_xboole_0 = X4) )),
% 1.49/0.56    inference(duplicate_literal_removal,[],[f208])).
% 1.49/0.56  fof(f208,plain,(
% 1.49/0.56    ( ! [X6,X4,X7,X5] : (m1_subset_1(k2_mcart_1(k1_mcart_1(X7)),X5) | ~m1_subset_1(X7,k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6)) | ~m1_subset_1(X7,k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6)) | k1_xboole_0 = X6 | k1_xboole_0 = X5 | k1_xboole_0 = X4) )),
% 1.49/0.56    inference(superposition,[],[f80,f77])).
% 1.49/0.56  fof(f77,plain,(
% 1.49/0.56    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.49/0.56    inference(definition_unfolding,[],[f62,f58])).
% 1.49/0.56  fof(f62,plain,(
% 1.49/0.56    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.49/0.56    inference(cnf_transformation,[],[f27])).
% 1.49/0.56  fof(f80,plain,(
% 1.49/0.56    ( ! [X2,X0,X3,X1] : (m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 1.49/0.56    inference(definition_unfolding,[],[f66,f58])).
% 1.49/0.56  fof(f66,plain,(
% 1.49/0.56    ( ! [X2,X0,X3,X1] : (m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 1.49/0.56    inference(cnf_transformation,[],[f29])).
% 1.49/0.56  fof(f29,plain,(
% 1.49/0.56    ! [X0,X1,X2,X3] : (m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 1.49/0.56    inference(ennf_transformation,[],[f10])).
% 1.49/0.56  fof(f10,axiom,(
% 1.49/0.56    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_mcart_1)).
% 1.49/0.56  fof(f220,plain,(
% 1.49/0.56    ( ! [X6,X4,X7,X5] : (m1_subset_1(k1_mcart_1(k1_mcart_1(X7)),X4) | ~m1_subset_1(X7,k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6)) | k1_xboole_0 = X6 | k1_xboole_0 = X5 | k1_xboole_0 = X4) )),
% 1.49/0.56    inference(duplicate_literal_removal,[],[f219])).
% 1.49/0.56  fof(f219,plain,(
% 1.49/0.56    ( ! [X6,X4,X7,X5] : (m1_subset_1(k1_mcart_1(k1_mcart_1(X7)),X4) | ~m1_subset_1(X7,k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6)) | ~m1_subset_1(X7,k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6)) | k1_xboole_0 = X6 | k1_xboole_0 = X5 | k1_xboole_0 = X4) )),
% 1.49/0.56    inference(superposition,[],[f79,f78])).
% 1.49/0.56  fof(f78,plain,(
% 1.49/0.56    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.49/0.56    inference(definition_unfolding,[],[f61,f58])).
% 1.49/0.56  fof(f61,plain,(
% 1.49/0.56    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.49/0.56    inference(cnf_transformation,[],[f27])).
% 1.49/0.56  fof(f79,plain,(
% 1.49/0.56    ( ! [X2,X0,X3,X1] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 1.49/0.56    inference(definition_unfolding,[],[f65,f58])).
% 1.49/0.56  fof(f65,plain,(
% 1.49/0.56    ( ! [X2,X0,X3,X1] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 1.49/0.56    inference(cnf_transformation,[],[f28])).
% 1.49/0.56  fof(f28,plain,(
% 1.49/0.56    ! [X0,X1,X2,X3] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 1.49/0.56    inference(ennf_transformation,[],[f9])).
% 1.49/0.56  fof(f9,axiom,(
% 1.49/0.56    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_mcart_1)).
% 1.49/0.56  fof(f185,plain,(
% 1.49/0.56    spl7_1 | spl7_2),
% 1.49/0.56    inference(avatar_split_clause,[],[f184,f100,f96])).
% 1.49/0.56  fof(f100,plain,(
% 1.49/0.56    spl7_2 <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.49/0.56  fof(f184,plain,(
% 1.49/0.56    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.49/0.56    inference(resolution,[],[f75,f56])).
% 1.49/0.56  fof(f56,plain,(
% 1.49/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f25])).
% 1.49/0.56  fof(f25,plain,(
% 1.49/0.56    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.49/0.56    inference(flattening,[],[f24])).
% 1.49/0.56  fof(f24,plain,(
% 1.49/0.56    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.49/0.56    inference(ennf_transformation,[],[f4])).
% 1.49/0.56  fof(f4,axiom,(
% 1.49/0.56    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.49/0.56  fof(f182,plain,(
% 1.49/0.56    ~spl7_2),
% 1.49/0.56    inference(avatar_contradiction_clause,[],[f181])).
% 1.49/0.56  fof(f181,plain,(
% 1.49/0.56    $false | ~spl7_2),
% 1.49/0.56    inference(subsumption_resolution,[],[f180,f43])).
% 1.49/0.56  fof(f180,plain,(
% 1.49/0.56    k1_xboole_0 = sK0 | ~spl7_2),
% 1.49/0.56    inference(subsumption_resolution,[],[f179,f44])).
% 1.49/0.56  fof(f179,plain,(
% 1.49/0.56    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl7_2),
% 1.49/0.56    inference(subsumption_resolution,[],[f178,f45])).
% 1.49/0.56  fof(f178,plain,(
% 1.49/0.56    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl7_2),
% 1.49/0.56    inference(condensation,[],[f177])).
% 1.49/0.56  fof(f177,plain,(
% 1.49/0.56    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) ) | ~spl7_2),
% 1.49/0.56    inference(subsumption_resolution,[],[f169,f112])).
% 1.49/0.56  fof(f112,plain,(
% 1.49/0.56    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.49/0.56    inference(resolution,[],[f110,f50])).
% 1.49/0.56  fof(f50,plain,(
% 1.49/0.56    ( ! [X0] : (r2_hidden(sK6(X0),X0) | k1_xboole_0 = X0) )),
% 1.49/0.56    inference(cnf_transformation,[],[f38])).
% 1.49/0.56  fof(f38,plain,(
% 1.49/0.56    ! [X0] : ((! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != sK6(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK6(X0),X0)) | k1_xboole_0 = X0)),
% 1.49/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f21,f37])).
% 1.49/0.56  fof(f37,plain,(
% 1.49/0.56    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X5,X4,X3,X2] : (k4_mcart_1(X2,X3,X4,X5) != sK6(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK6(X0),X0)))),
% 1.49/0.56    introduced(choice_axiom,[])).
% 1.49/0.56  fof(f21,plain,(
% 1.49/0.56    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.49/0.56    inference(ennf_transformation,[],[f14])).
% 1.49/0.56  fof(f14,axiom,(
% 1.49/0.56    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).
% 1.49/0.57  fof(f110,plain,(
% 1.49/0.57    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1))) )),
% 1.49/0.57    inference(resolution,[],[f109,f47])).
% 1.49/0.57  fof(f47,plain,(
% 1.49/0.57    v1_xboole_0(k1_xboole_0)),
% 1.49/0.57    inference(cnf_transformation,[],[f2])).
% 1.49/0.57  fof(f2,axiom,(
% 1.49/0.57    v1_xboole_0(k1_xboole_0)),
% 1.49/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.49/0.57  fof(f109,plain,(
% 1.49/0.57    ( ! [X2,X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 1.49/0.57    inference(resolution,[],[f59,f48])).
% 1.49/0.57  fof(f48,plain,(
% 1.49/0.57    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f36])).
% 1.49/0.57  fof(f36,plain,(
% 1.49/0.57    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK5(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.49/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f35])).
% 1.49/0.57  fof(f35,plain,(
% 1.49/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK5(X0),X0))),
% 1.49/0.57    introduced(choice_axiom,[])).
% 1.49/0.57  fof(f34,plain,(
% 1.49/0.57    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.49/0.57    inference(rectify,[],[f33])).
% 1.49/0.57  fof(f33,plain,(
% 1.49/0.57    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.49/0.57    inference(nnf_transformation,[],[f1])).
% 1.49/0.57  fof(f1,axiom,(
% 1.49/0.57    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.49/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.49/0.57  fof(f169,plain,(
% 1.49/0.57    ( ! [X0] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0) | k1_xboole_0 = X0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) ) | ~spl7_2),
% 1.49/0.57    inference(superposition,[],[f86,f104])).
% 1.49/0.57  fof(f104,plain,(
% 1.49/0.57    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl7_2),
% 1.49/0.57    inference(resolution,[],[f102,f92])).
% 1.49/0.57  fof(f92,plain,(
% 1.49/0.57    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.49/0.57    inference(resolution,[],[f50,f48])).
% 1.49/0.57  fof(f102,plain,(
% 1.49/0.57    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl7_2),
% 1.49/0.57    inference(avatar_component_clause,[],[f100])).
% 1.49/0.57  fof(f86,plain,(
% 1.49/0.57    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.49/0.57    inference(definition_unfolding,[],[f68,f73])).
% 1.49/0.57  fof(f73,plain,(
% 1.49/0.57    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 1.49/0.57    inference(definition_unfolding,[],[f64,f58])).
% 1.49/0.57  fof(f64,plain,(
% 1.49/0.57    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f8])).
% 1.49/0.57  fof(f8,axiom,(
% 1.49/0.57    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 1.49/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 1.49/0.57  fof(f68,plain,(
% 1.49/0.57    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.49/0.57    inference(cnf_transformation,[],[f40])).
% 1.49/0.57  fof(f40,plain,(
% 1.49/0.57    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.49/0.57    inference(flattening,[],[f39])).
% 1.49/0.57  fof(f39,plain,(
% 1.49/0.57    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | (k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.49/0.57    inference(nnf_transformation,[],[f16])).
% 1.49/0.57  fof(f16,axiom,(
% 1.49/0.57    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 1.49/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).
% 1.49/0.57  % SZS output end Proof for theBenchmark
% 1.49/0.57  % (12667)------------------------------
% 1.49/0.57  % (12667)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.57  % (12667)Termination reason: Refutation
% 1.49/0.57  
% 1.49/0.57  % (12667)Memory used [KB]: 10874
% 1.49/0.57  % (12667)Time elapsed: 0.136 s
% 1.49/0.57  % (12667)------------------------------
% 1.49/0.57  % (12667)------------------------------
% 1.49/0.57  % (12663)Success in time 0.201 s
%------------------------------------------------------------------------------
