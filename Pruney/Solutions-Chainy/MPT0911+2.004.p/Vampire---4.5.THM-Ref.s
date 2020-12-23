%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:29 EST 2020

% Result     : Theorem 2.25s
% Output     : Refutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 283 expanded)
%              Number of leaves         :   15 (  73 expanded)
%              Depth                    :   20
%              Number of atoms          :  333 (1590 expanded)
%              Number of equality atoms :  151 ( 718 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1641,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1506,f1598])).

fof(f1598,plain,(
    ~ spl15_1 ),
    inference(avatar_contradiction_clause,[],[f1597])).

fof(f1597,plain,
    ( $false
    | ~ spl15_1 ),
    inference(subsumption_resolution,[],[f1596,f61])).

fof(f61,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( sK5 != k7_mcart_1(sK2,sK3,sK4,sK6)
    & k1_xboole_0 != sK4
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK5 = X7
                | k3_mcart_1(X5,X6,X7) != sK6
                | ~ m1_subset_1(X7,sK4) )
            | ~ m1_subset_1(X6,sK3) )
        | ~ m1_subset_1(X5,sK2) )
    & m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f22,f33])).

fof(f33,plain,
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
   => ( sK5 != k7_mcart_1(sK2,sK3,sK4,sK6)
      & k1_xboole_0 != sK4
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK5 = X7
                  | k3_mcart_1(X5,X6,X7) != sK6
                  | ~ m1_subset_1(X7,sK4) )
              | ~ m1_subset_1(X6,sK3) )
          | ~ m1_subset_1(X5,sK2) )
      & m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
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

fof(f1596,plain,
    ( k1_xboole_0 = sK2
    | ~ spl15_1 ),
    inference(subsumption_resolution,[],[f1595,f62])).

fof(f62,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f34])).

fof(f1595,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | ~ spl15_1 ),
    inference(subsumption_resolution,[],[f1594,f63])).

fof(f63,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f34])).

fof(f1594,plain,
    ( k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | ~ spl15_1 ),
    inference(trivial_inequality_removal,[],[f1561])).

fof(f1561,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | ~ spl15_1 ),
    inference(superposition,[],[f125,f1522])).

fof(f1522,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
    | ~ spl15_1 ),
    inference(resolution,[],[f144,f140])).

fof(f140,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f68,f66])).

fof(f66,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK7(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f36,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK7(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
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

fof(f68,plain,(
    ! [X0] :
      ( r2_hidden(sK8(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK8(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK8(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f23,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X5,X4,X3,X2] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK8(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK8(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).

fof(f144,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))
    | ~ spl15_1 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl15_1
  <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1])])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f106,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).

fof(f1506,plain,(
    spl15_1 ),
    inference(avatar_contradiction_clause,[],[f1505])).

fof(f1505,plain,
    ( $false
    | spl15_1 ),
    inference(subsumption_resolution,[],[f1504,f212])).

fof(f212,plain,
    ( m1_subset_1(k2_mcart_1(sK6),sK4)
    | spl15_1 ),
    inference(resolution,[],[f204,f186])).

fof(f186,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f77,f66])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f204,plain,
    ( r2_hidden(k2_mcart_1(sK6),sK4)
    | spl15_1 ),
    inference(resolution,[],[f84,f184])).

fof(f184,plain,
    ( r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))
    | spl15_1 ),
    inference(subsumption_resolution,[],[f182,f145])).

fof(f145,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))
    | spl15_1 ),
    inference(avatar_component_clause,[],[f143])).

fof(f182,plain,
    ( r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
    inference(resolution,[],[f76,f114])).

fof(f114,plain,(
    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
    inference(definition_unfolding,[],[f59,f82])).

fof(f59,plain,(
    m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f34])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f1504,plain,
    ( ~ m1_subset_1(k2_mcart_1(sK6),sK4)
    | spl15_1 ),
    inference(subsumption_resolution,[],[f1503,f1059])).

fof(f1059,plain,(
    sK5 != k2_mcart_1(sK6) ),
    inference(superposition,[],[f64,f1057])).

fof(f1057,plain,(
    k7_mcart_1(sK2,sK3,sK4,sK6) = k2_mcart_1(sK6) ),
    inference(subsumption_resolution,[],[f1056,f61])).

fof(f1056,plain,
    ( k7_mcart_1(sK2,sK3,sK4,sK6) = k2_mcart_1(sK6)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f1055,f62])).

fof(f1055,plain,
    ( k7_mcart_1(sK2,sK3,sK4,sK6) = k2_mcart_1(sK6)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f1048,f63])).

fof(f1048,plain,
    ( k7_mcart_1(sK2,sK3,sK4,sK6) = k2_mcart_1(sK6)
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f126,f114])).

fof(f126,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f112,f82])).

fof(f112,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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

fof(f64,plain,(
    sK5 != k7_mcart_1(sK2,sK3,sK4,sK6) ),
    inference(cnf_transformation,[],[f34])).

fof(f1503,plain,
    ( sK5 = k2_mcart_1(sK6)
    | ~ m1_subset_1(k2_mcart_1(sK6),sK4)
    | spl15_1 ),
    inference(trivial_inequality_removal,[],[f1502])).

fof(f1502,plain,
    ( sK6 != sK6
    | sK5 = k2_mcart_1(sK6)
    | ~ m1_subset_1(k2_mcart_1(sK6),sK4)
    | spl15_1 ),
    inference(superposition,[],[f395,f247])).

fof(f247,plain,
    ( sK6 = k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6))
    | spl15_1 ),
    inference(subsumption_resolution,[],[f242,f71])).

fof(f71,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f242,plain,
    ( sK6 = k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6))
    | ~ v1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))
    | spl15_1 ),
    inference(resolution,[],[f80,f184])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f395,plain,
    ( ! [X1] :
        ( sK6 != k4_tarski(k1_mcart_1(sK6),X1)
        | sK5 = X1
        | ~ m1_subset_1(X1,sK4) )
    | spl15_1 ),
    inference(subsumption_resolution,[],[f394,f202])).

fof(f202,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK6)),sK2)
    | spl15_1 ),
    inference(resolution,[],[f199,f186])).

fof(f199,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK2)
    | spl15_1 ),
    inference(resolution,[],[f192,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f192,plain,
    ( r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK2,sK3))
    | spl15_1 ),
    inference(resolution,[],[f83,f184])).

fof(f394,plain,
    ( ! [X1] :
        ( sK6 != k4_tarski(k1_mcart_1(sK6),X1)
        | sK5 = X1
        | ~ m1_subset_1(X1,sK4)
        | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK6)),sK2) )
    | spl15_1 ),
    inference(subsumption_resolution,[],[f381,f221])).

fof(f221,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK6)),sK3)
    | spl15_1 ),
    inference(resolution,[],[f205,f186])).

fof(f205,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK3)
    | spl15_1 ),
    inference(resolution,[],[f84,f192])).

fof(f381,plain,
    ( ! [X1] :
        ( sK6 != k4_tarski(k1_mcart_1(sK6),X1)
        | sK5 = X1
        | ~ m1_subset_1(X1,sK4)
        | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK6)),sK3)
        | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK6)),sK2) )
    | spl15_1 ),
    inference(superposition,[],[f113,f248])).

fof(f248,plain,
    ( k1_mcart_1(sK6) = k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6)))
    | spl15_1 ),
    inference(subsumption_resolution,[],[f243,f71])).

fof(f243,plain,
    ( k1_mcart_1(sK6) = k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6)))
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK3))
    | spl15_1 ),
    inference(resolution,[],[f80,f192])).

fof(f113,plain,(
    ! [X6,X7,X5] :
      ( sK6 != k4_tarski(k4_tarski(X5,X6),X7)
      | sK5 = X7
      | ~ m1_subset_1(X7,sK4)
      | ~ m1_subset_1(X6,sK3)
      | ~ m1_subset_1(X5,sK2) ) ),
    inference(definition_unfolding,[],[f60,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f60,plain,(
    ! [X6,X7,X5] :
      ( sK5 = X7
      | k3_mcart_1(X5,X6,X7) != sK6
      | ~ m1_subset_1(X7,sK4)
      | ~ m1_subset_1(X6,sK3)
      | ~ m1_subset_1(X5,sK2) ) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : run_vampire %s %d
% 0.10/0.32  % Computer   : n014.cluster.edu
% 0.10/0.32  % Model      : x86_64 x86_64
% 0.10/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.32  % Memory     : 8042.1875MB
% 0.10/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.32  % CPULimit   : 60
% 0.10/0.32  % WCLimit    : 600
% 0.10/0.32  % DateTime   : Tue Dec  1 12:17:07 EST 2020
% 0.10/0.32  % CPUTime    : 
% 0.17/0.49  % (24246)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.17/0.50  % (24253)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.17/0.50  % (24270)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.17/0.50  % (24253)Refutation not found, incomplete strategy% (24253)------------------------------
% 0.17/0.50  % (24253)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.50  % (24253)Termination reason: Refutation not found, incomplete strategy
% 0.17/0.50  
% 0.17/0.50  % (24253)Memory used [KB]: 10618
% 0.17/0.50  % (24253)Time elapsed: 0.107 s
% 0.17/0.50  % (24253)------------------------------
% 0.17/0.50  % (24253)------------------------------
% 0.17/0.50  % (24254)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.17/0.51  % (24261)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.17/0.51  % (24270)Refutation not found, incomplete strategy% (24270)------------------------------
% 0.17/0.51  % (24270)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.51  % (24270)Termination reason: Refutation not found, incomplete strategy
% 0.17/0.51  
% 0.17/0.51  % (24270)Memory used [KB]: 1663
% 0.17/0.51  % (24270)Time elapsed: 0.103 s
% 0.17/0.51  % (24270)------------------------------
% 0.17/0.51  % (24270)------------------------------
% 0.17/0.51  % (24269)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.17/0.51  % (24245)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.17/0.51  % (24249)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.17/0.51  % (24243)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.17/0.51  % (24244)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.17/0.53  % (24259)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.17/0.53  % (24255)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.17/0.53  % (24248)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.17/0.53  % (24257)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.17/0.53  % (24265)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.17/0.53  % (24257)Refutation not found, incomplete strategy% (24257)------------------------------
% 0.17/0.53  % (24257)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.53  % (24257)Termination reason: Refutation not found, incomplete strategy
% 0.17/0.53  
% 0.17/0.53  % (24257)Memory used [KB]: 10746
% 0.17/0.53  % (24257)Time elapsed: 0.129 s
% 0.17/0.53  % (24257)------------------------------
% 0.17/0.53  % (24257)------------------------------
% 0.17/0.53  % (24251)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.17/0.53  % (24241)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.17/0.54  % (24269)Refutation not found, incomplete strategy% (24269)------------------------------
% 0.17/0.54  % (24269)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.54  % (24269)Termination reason: Refutation not found, incomplete strategy
% 0.17/0.54  
% 0.17/0.54  % (24269)Memory used [KB]: 11129
% 0.17/0.54  % (24269)Time elapsed: 0.153 s
% 0.17/0.54  % (24269)------------------------------
% 0.17/0.54  % (24269)------------------------------
% 0.17/0.54  % (24247)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.17/0.54  % (24266)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.17/0.54  % (24262)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.17/0.54  % (24252)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.17/0.54  % (24263)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.17/0.55  % (24259)Refutation not found, incomplete strategy% (24259)------------------------------
% 0.17/0.55  % (24259)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.55  % (24259)Termination reason: Refutation not found, incomplete strategy
% 0.17/0.55  
% 0.17/0.55  % (24259)Memory used [KB]: 1791
% 0.17/0.55  % (24259)Time elapsed: 0.170 s
% 0.17/0.55  % (24259)------------------------------
% 0.17/0.55  % (24259)------------------------------
% 0.17/0.55  % (24264)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.17/0.55  % (24250)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.17/0.55  % (24265)Refutation not found, incomplete strategy% (24265)------------------------------
% 0.17/0.55  % (24265)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.55  % (24265)Termination reason: Refutation not found, incomplete strategy
% 0.17/0.55  
% 0.17/0.55  % (24265)Memory used [KB]: 10746
% 0.17/0.55  % (24265)Time elapsed: 0.169 s
% 0.17/0.55  % (24265)------------------------------
% 0.17/0.55  % (24265)------------------------------
% 0.17/0.55  % (24242)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.17/0.55  % (24242)Refutation not found, incomplete strategy% (24242)------------------------------
% 0.17/0.55  % (24242)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.55  % (24242)Termination reason: Refutation not found, incomplete strategy
% 0.17/0.55  
% 0.17/0.55  % (24242)Memory used [KB]: 1663
% 0.17/0.55  % (24242)Time elapsed: 0.150 s
% 0.17/0.55  % (24242)------------------------------
% 0.17/0.55  % (24242)------------------------------
% 0.17/0.55  % (24260)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.17/0.55  % (24267)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.17/0.55  % (24268)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.17/0.56  % (24268)Refutation not found, incomplete strategy% (24268)------------------------------
% 0.17/0.56  % (24268)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.56  % (24268)Termination reason: Refutation not found, incomplete strategy
% 0.17/0.56  
% 0.17/0.56  % (24268)Memory used [KB]: 6268
% 0.17/0.56  % (24268)Time elapsed: 0.178 s
% 0.17/0.56  % (24268)------------------------------
% 0.17/0.56  % (24268)------------------------------
% 0.17/0.56  % (24258)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.17/0.57  % (24251)Refutation not found, incomplete strategy% (24251)------------------------------
% 0.17/0.57  % (24251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.57  % (24251)Termination reason: Refutation not found, incomplete strategy
% 0.17/0.57  
% 0.17/0.57  % (24251)Memory used [KB]: 11129
% 0.17/0.57  % (24251)Time elapsed: 0.177 s
% 0.17/0.57  % (24251)------------------------------
% 0.17/0.57  % (24251)------------------------------
% 0.17/0.57  % (24256)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 2.25/0.65  % (24247)Refutation found. Thanks to Tanya!
% 2.25/0.65  % SZS status Theorem for theBenchmark
% 2.25/0.65  % SZS output start Proof for theBenchmark
% 2.25/0.65  fof(f1641,plain,(
% 2.25/0.65    $false),
% 2.25/0.65    inference(avatar_sat_refutation,[],[f1506,f1598])).
% 2.25/0.65  fof(f1598,plain,(
% 2.25/0.65    ~spl15_1),
% 2.25/0.65    inference(avatar_contradiction_clause,[],[f1597])).
% 2.25/0.65  fof(f1597,plain,(
% 2.25/0.65    $false | ~spl15_1),
% 2.25/0.65    inference(subsumption_resolution,[],[f1596,f61])).
% 2.25/0.65  fof(f61,plain,(
% 2.25/0.65    k1_xboole_0 != sK2),
% 2.25/0.65    inference(cnf_transformation,[],[f34])).
% 2.25/0.65  fof(f34,plain,(
% 2.25/0.65    sK5 != k7_mcart_1(sK2,sK3,sK4,sK6) & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & ! [X5] : (! [X6] : (! [X7] : (sK5 = X7 | k3_mcart_1(X5,X6,X7) != sK6 | ~m1_subset_1(X7,sK4)) | ~m1_subset_1(X6,sK3)) | ~m1_subset_1(X5,sK2)) & m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4))),
% 2.25/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f22,f33])).
% 2.25/0.65  fof(f33,plain,(
% 2.25/0.65    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (sK5 != k7_mcart_1(sK2,sK3,sK4,sK6) & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & ! [X5] : (! [X6] : (! [X7] : (sK5 = X7 | k3_mcart_1(X5,X6,X7) != sK6 | ~m1_subset_1(X7,sK4)) | ~m1_subset_1(X6,sK3)) | ~m1_subset_1(X5,sK2)) & m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4)))),
% 2.25/0.65    introduced(choice_axiom,[])).
% 2.25/0.65  fof(f22,plain,(
% 2.25/0.65    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 2.25/0.65    inference(flattening,[],[f21])).
% 2.25/0.65  fof(f21,plain,(
% 2.25/0.65    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 2.25/0.65    inference(ennf_transformation,[],[f20])).
% 2.25/0.65  fof(f20,negated_conjecture,(
% 2.25/0.65    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.25/0.65    inference(negated_conjecture,[],[f19])).
% 2.25/0.65  fof(f19,conjecture,(
% 2.25/0.65    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.25/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_mcart_1)).
% 2.25/0.65  fof(f1596,plain,(
% 2.25/0.65    k1_xboole_0 = sK2 | ~spl15_1),
% 2.25/0.65    inference(subsumption_resolution,[],[f1595,f62])).
% 2.25/0.65  fof(f62,plain,(
% 2.25/0.65    k1_xboole_0 != sK3),
% 2.25/0.65    inference(cnf_transformation,[],[f34])).
% 2.25/0.65  fof(f1595,plain,(
% 2.25/0.65    k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | ~spl15_1),
% 2.25/0.65    inference(subsumption_resolution,[],[f1594,f63])).
% 2.25/0.65  fof(f63,plain,(
% 2.25/0.65    k1_xboole_0 != sK4),
% 2.25/0.65    inference(cnf_transformation,[],[f34])).
% 2.25/0.65  fof(f1594,plain,(
% 2.25/0.65    k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | ~spl15_1),
% 2.25/0.65    inference(trivial_inequality_removal,[],[f1561])).
% 2.25/0.65  fof(f1561,plain,(
% 2.25/0.65    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | ~spl15_1),
% 2.25/0.65    inference(superposition,[],[f125,f1522])).
% 2.25/0.65  fof(f1522,plain,(
% 2.25/0.65    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) | ~spl15_1),
% 2.25/0.65    inference(resolution,[],[f144,f140])).
% 2.25/0.65  fof(f140,plain,(
% 2.25/0.65    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 2.25/0.65    inference(resolution,[],[f68,f66])).
% 2.25/0.65  fof(f66,plain,(
% 2.25/0.65    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.25/0.65    inference(cnf_transformation,[],[f38])).
% 2.25/0.65  fof(f38,plain,(
% 2.25/0.65    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK7(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.25/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f36,f37])).
% 2.25/0.65  fof(f37,plain,(
% 2.25/0.65    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK7(X0),X0))),
% 2.25/0.65    introduced(choice_axiom,[])).
% 2.25/0.65  fof(f36,plain,(
% 2.25/0.65    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.25/0.65    inference(rectify,[],[f35])).
% 2.25/0.65  fof(f35,plain,(
% 2.25/0.65    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.25/0.65    inference(nnf_transformation,[],[f1])).
% 2.25/0.65  fof(f1,axiom,(
% 2.25/0.65    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.25/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.25/0.65  fof(f68,plain,(
% 2.25/0.65    ( ! [X0] : (r2_hidden(sK8(X0),X0) | k1_xboole_0 = X0) )),
% 2.25/0.65    inference(cnf_transformation,[],[f40])).
% 2.25/0.65  fof(f40,plain,(
% 2.25/0.65    ! [X0] : ((! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != sK8(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK8(X0),X0)) | k1_xboole_0 = X0)),
% 2.25/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f23,f39])).
% 2.25/0.65  fof(f39,plain,(
% 2.25/0.65    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X5,X4,X3,X2] : (k4_mcart_1(X2,X3,X4,X5) != sK8(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK8(X0),X0)))),
% 2.25/0.65    introduced(choice_axiom,[])).
% 2.25/0.65  fof(f23,plain,(
% 2.25/0.65    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 2.25/0.65    inference(ennf_transformation,[],[f16])).
% 2.25/0.65  fof(f16,axiom,(
% 2.25/0.65    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.25/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).
% 2.25/0.65  fof(f144,plain,(
% 2.25/0.65    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) | ~spl15_1),
% 2.25/0.65    inference(avatar_component_clause,[],[f143])).
% 2.25/0.65  fof(f143,plain,(
% 2.25/0.65    spl15_1 <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))),
% 2.25/0.65    introduced(avatar_definition,[new_symbols(naming,[spl15_1])])).
% 2.25/0.65  fof(f125,plain,(
% 2.25/0.65    ( ! [X2,X0,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.25/0.65    inference(definition_unfolding,[],[f106,f82])).
% 2.25/0.65  fof(f82,plain,(
% 2.25/0.65    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 2.25/0.65    inference(cnf_transformation,[],[f13])).
% 2.25/0.65  fof(f13,axiom,(
% 2.25/0.65    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 2.25/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 2.25/0.65  fof(f106,plain,(
% 2.25/0.65    ( ! [X2,X0,X1] : (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.25/0.65    inference(cnf_transformation,[],[f58])).
% 2.25/0.65  fof(f58,plain,(
% 2.25/0.65    ! [X0,X1,X2] : (((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) & (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.25/0.65    inference(flattening,[],[f57])).
% 2.25/0.65  fof(f57,plain,(
% 2.25/0.65    ! [X0,X1,X2] : (((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) & (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | (k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.25/0.65    inference(nnf_transformation,[],[f17])).
% 2.25/0.65  fof(f17,axiom,(
% 2.25/0.65    ! [X0,X1,X2] : ((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2))),
% 2.25/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).
% 2.25/0.65  fof(f1506,plain,(
% 2.25/0.65    spl15_1),
% 2.25/0.65    inference(avatar_contradiction_clause,[],[f1505])).
% 2.25/0.65  fof(f1505,plain,(
% 2.25/0.65    $false | spl15_1),
% 2.25/0.65    inference(subsumption_resolution,[],[f1504,f212])).
% 2.25/0.65  fof(f212,plain,(
% 2.25/0.65    m1_subset_1(k2_mcart_1(sK6),sK4) | spl15_1),
% 2.25/0.65    inference(resolution,[],[f204,f186])).
% 2.25/0.65  fof(f186,plain,(
% 2.25/0.65    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 2.25/0.65    inference(subsumption_resolution,[],[f77,f66])).
% 2.25/0.65  fof(f77,plain,(
% 2.25/0.65    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.25/0.65    inference(cnf_transformation,[],[f41])).
% 2.25/0.65  fof(f41,plain,(
% 2.25/0.65    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.25/0.65    inference(nnf_transformation,[],[f24])).
% 2.25/0.65  fof(f24,plain,(
% 2.25/0.65    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.25/0.65    inference(ennf_transformation,[],[f10])).
% 2.25/0.65  fof(f10,axiom,(
% 2.25/0.65    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.25/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 2.25/0.65  fof(f204,plain,(
% 2.25/0.65    r2_hidden(k2_mcart_1(sK6),sK4) | spl15_1),
% 2.25/0.65    inference(resolution,[],[f84,f184])).
% 2.25/0.65  fof(f184,plain,(
% 2.25/0.65    r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) | spl15_1),
% 2.25/0.65    inference(subsumption_resolution,[],[f182,f145])).
% 2.25/0.65  fof(f145,plain,(
% 2.25/0.65    ~v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) | spl15_1),
% 2.25/0.65    inference(avatar_component_clause,[],[f143])).
% 2.25/0.65  fof(f182,plain,(
% 2.25/0.65    r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))),
% 2.25/0.65    inference(resolution,[],[f76,f114])).
% 2.25/0.65  fof(f114,plain,(
% 2.25/0.65    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))),
% 2.25/0.65    inference(definition_unfolding,[],[f59,f82])).
% 2.25/0.65  fof(f59,plain,(
% 2.25/0.65    m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4))),
% 2.25/0.65    inference(cnf_transformation,[],[f34])).
% 2.25/0.65  fof(f76,plain,(
% 2.25/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.25/0.65    inference(cnf_transformation,[],[f41])).
% 2.25/0.65  fof(f84,plain,(
% 2.25/0.65    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 2.25/0.65    inference(cnf_transformation,[],[f27])).
% 2.25/0.65  fof(f27,plain,(
% 2.25/0.65    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 2.25/0.65    inference(ennf_transformation,[],[f14])).
% 2.25/0.65  fof(f14,axiom,(
% 2.25/0.65    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 2.25/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 2.25/0.65  fof(f1504,plain,(
% 2.25/0.65    ~m1_subset_1(k2_mcart_1(sK6),sK4) | spl15_1),
% 2.25/0.65    inference(subsumption_resolution,[],[f1503,f1059])).
% 2.25/0.65  fof(f1059,plain,(
% 2.25/0.65    sK5 != k2_mcart_1(sK6)),
% 2.25/0.65    inference(superposition,[],[f64,f1057])).
% 2.25/0.65  fof(f1057,plain,(
% 2.25/0.65    k7_mcart_1(sK2,sK3,sK4,sK6) = k2_mcart_1(sK6)),
% 2.25/0.65    inference(subsumption_resolution,[],[f1056,f61])).
% 2.25/0.65  fof(f1056,plain,(
% 2.25/0.65    k7_mcart_1(sK2,sK3,sK4,sK6) = k2_mcart_1(sK6) | k1_xboole_0 = sK2),
% 2.25/0.65    inference(subsumption_resolution,[],[f1055,f62])).
% 2.25/0.65  fof(f1055,plain,(
% 2.25/0.65    k7_mcart_1(sK2,sK3,sK4,sK6) = k2_mcart_1(sK6) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2),
% 2.25/0.65    inference(subsumption_resolution,[],[f1048,f63])).
% 2.25/0.65  fof(f1048,plain,(
% 2.25/0.65    k7_mcart_1(sK2,sK3,sK4,sK6) = k2_mcart_1(sK6) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2),
% 2.25/0.65    inference(resolution,[],[f126,f114])).
% 2.25/0.65  fof(f126,plain,(
% 2.25/0.65    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.25/0.65    inference(definition_unfolding,[],[f112,f82])).
% 2.25/0.65  fof(f112,plain,(
% 2.25/0.65    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.25/0.65    inference(cnf_transformation,[],[f28])).
% 2.25/0.65  fof(f28,plain,(
% 2.25/0.65    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.25/0.65    inference(ennf_transformation,[],[f18])).
% 2.25/0.65  fof(f18,axiom,(
% 2.25/0.65    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.25/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).
% 2.25/0.65  fof(f64,plain,(
% 2.25/0.65    sK5 != k7_mcart_1(sK2,sK3,sK4,sK6)),
% 2.25/0.65    inference(cnf_transformation,[],[f34])).
% 2.25/0.65  fof(f1503,plain,(
% 2.25/0.65    sK5 = k2_mcart_1(sK6) | ~m1_subset_1(k2_mcart_1(sK6),sK4) | spl15_1),
% 2.25/0.65    inference(trivial_inequality_removal,[],[f1502])).
% 2.25/0.65  fof(f1502,plain,(
% 2.25/0.65    sK6 != sK6 | sK5 = k2_mcart_1(sK6) | ~m1_subset_1(k2_mcart_1(sK6),sK4) | spl15_1),
% 2.25/0.65    inference(superposition,[],[f395,f247])).
% 2.25/0.65  fof(f247,plain,(
% 2.25/0.65    sK6 = k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) | spl15_1),
% 2.25/0.65    inference(subsumption_resolution,[],[f242,f71])).
% 2.25/0.65  fof(f71,plain,(
% 2.25/0.65    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.25/0.65    inference(cnf_transformation,[],[f11])).
% 2.25/0.65  fof(f11,axiom,(
% 2.25/0.65    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.25/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.25/0.65  fof(f242,plain,(
% 2.25/0.65    sK6 = k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) | ~v1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) | spl15_1),
% 2.25/0.65    inference(resolution,[],[f80,f184])).
% 2.25/0.65  fof(f80,plain,(
% 2.25/0.65    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~v1_relat_1(X1)) )),
% 2.25/0.65    inference(cnf_transformation,[],[f26])).
% 2.25/0.65  fof(f26,plain,(
% 2.25/0.65    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 2.25/0.65    inference(flattening,[],[f25])).
% 2.25/0.65  fof(f25,plain,(
% 2.25/0.65    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 2.25/0.65    inference(ennf_transformation,[],[f15])).
% 2.25/0.65  fof(f15,axiom,(
% 2.25/0.65    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 2.25/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).
% 2.25/0.65  fof(f395,plain,(
% 2.25/0.65    ( ! [X1] : (sK6 != k4_tarski(k1_mcart_1(sK6),X1) | sK5 = X1 | ~m1_subset_1(X1,sK4)) ) | spl15_1),
% 2.25/0.65    inference(subsumption_resolution,[],[f394,f202])).
% 2.25/0.65  fof(f202,plain,(
% 2.25/0.65    m1_subset_1(k1_mcart_1(k1_mcart_1(sK6)),sK2) | spl15_1),
% 2.25/0.65    inference(resolution,[],[f199,f186])).
% 2.25/0.65  fof(f199,plain,(
% 2.25/0.65    r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK2) | spl15_1),
% 2.25/0.65    inference(resolution,[],[f192,f83])).
% 2.25/0.65  fof(f83,plain,(
% 2.25/0.65    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 2.25/0.65    inference(cnf_transformation,[],[f27])).
% 2.25/0.65  fof(f192,plain,(
% 2.25/0.65    r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK2,sK3)) | spl15_1),
% 2.25/0.65    inference(resolution,[],[f83,f184])).
% 2.25/0.65  fof(f394,plain,(
% 2.25/0.65    ( ! [X1] : (sK6 != k4_tarski(k1_mcart_1(sK6),X1) | sK5 = X1 | ~m1_subset_1(X1,sK4) | ~m1_subset_1(k1_mcart_1(k1_mcart_1(sK6)),sK2)) ) | spl15_1),
% 2.25/0.65    inference(subsumption_resolution,[],[f381,f221])).
% 2.25/0.65  fof(f221,plain,(
% 2.25/0.65    m1_subset_1(k2_mcart_1(k1_mcart_1(sK6)),sK3) | spl15_1),
% 2.25/0.65    inference(resolution,[],[f205,f186])).
% 2.25/0.65  fof(f205,plain,(
% 2.25/0.65    r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK3) | spl15_1),
% 2.25/0.65    inference(resolution,[],[f84,f192])).
% 2.25/0.65  fof(f381,plain,(
% 2.25/0.65    ( ! [X1] : (sK6 != k4_tarski(k1_mcart_1(sK6),X1) | sK5 = X1 | ~m1_subset_1(X1,sK4) | ~m1_subset_1(k2_mcart_1(k1_mcart_1(sK6)),sK3) | ~m1_subset_1(k1_mcart_1(k1_mcart_1(sK6)),sK2)) ) | spl15_1),
% 2.25/0.65    inference(superposition,[],[f113,f248])).
% 2.25/0.65  fof(f248,plain,(
% 2.25/0.65    k1_mcart_1(sK6) = k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))) | spl15_1),
% 2.25/0.65    inference(subsumption_resolution,[],[f243,f71])).
% 2.25/0.65  fof(f243,plain,(
% 2.25/0.65    k1_mcart_1(sK6) = k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))) | ~v1_relat_1(k2_zfmisc_1(sK2,sK3)) | spl15_1),
% 2.25/0.65    inference(resolution,[],[f80,f192])).
% 2.25/0.65  fof(f113,plain,(
% 2.25/0.65    ( ! [X6,X7,X5] : (sK6 != k4_tarski(k4_tarski(X5,X6),X7) | sK5 = X7 | ~m1_subset_1(X7,sK4) | ~m1_subset_1(X6,sK3) | ~m1_subset_1(X5,sK2)) )),
% 2.25/0.65    inference(definition_unfolding,[],[f60,f81])).
% 2.25/0.65  fof(f81,plain,(
% 2.25/0.65    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 2.25/0.65    inference(cnf_transformation,[],[f12])).
% 2.25/0.65  fof(f12,axiom,(
% 2.25/0.65    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 2.25/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 2.25/0.65  fof(f60,plain,(
% 2.25/0.65    ( ! [X6,X7,X5] : (sK5 = X7 | k3_mcart_1(X5,X6,X7) != sK6 | ~m1_subset_1(X7,sK4) | ~m1_subset_1(X6,sK3) | ~m1_subset_1(X5,sK2)) )),
% 2.25/0.65    inference(cnf_transformation,[],[f34])).
% 2.25/0.65  % SZS output end Proof for theBenchmark
% 2.25/0.65  % (24247)------------------------------
% 2.25/0.65  % (24247)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.25/0.65  % (24247)Termination reason: Refutation
% 2.25/0.65  
% 2.25/0.65  % (24247)Memory used [KB]: 11769
% 2.25/0.65  % (24247)Time elapsed: 0.203 s
% 2.25/0.65  % (24247)------------------------------
% 2.25/0.65  % (24247)------------------------------
% 2.25/0.65  % (24240)Success in time 0.315 s
%------------------------------------------------------------------------------
