%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:47 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 397 expanded)
%              Number of leaves         :   14 ( 130 expanded)
%              Depth                    :   21
%              Number of atoms          :  395 (3040 expanded)
%              Number of equality atoms :   31 ( 314 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f599,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f246,f509,f554,f598])).

fof(f598,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_contradiction_clause,[],[f592])).

fof(f592,plain,
    ( $false
    | ~ spl7_1
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f30,f240,f586,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f586,plain,
    ( ~ r2_hidden(sK5(sK2,sK3,sK1),sK0)
    | ~ spl7_1
    | spl7_2 ),
    inference(subsumption_resolution,[],[f585,f240])).

fof(f585,plain,
    ( ~ r2_hidden(sK5(sK2,sK3,sK1),sK1)
    | ~ r2_hidden(sK5(sK2,sK3,sK1),sK0)
    | ~ spl7_1
    | spl7_2 ),
    inference(subsumption_resolution,[],[f577,f245])).

fof(f245,plain,
    ( ~ r2_hidden(sK5(sK2,sK3,sK1),sK2)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl7_2
  <=> r2_hidden(sK5(sK2,sK3,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f577,plain,
    ( r2_hidden(sK5(sK2,sK3,sK1),sK2)
    | ~ r2_hidden(sK5(sK2,sK3,sK1),sK1)
    | ~ r2_hidden(sK5(sK2,sK3,sK1),sK0)
    | ~ spl7_1 ),
    inference(resolution,[],[f572,f75])).

fof(f75,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK3)
      | r2_hidden(X0,sK2)
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f73,f33])).

fof(f33,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK0)
      | r2_hidden(X4,sK2)
      | ~ r2_hidden(X4,sK1)
      | r2_hidden(X4,sK3) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( sK1 != k4_subset_1(sK0,sK2,sK3)
    & ! [X4] :
        ( ( ( r2_hidden(X4,sK1)
            | ( ~ r2_hidden(X4,sK3)
              & ~ r2_hidden(X4,sK2) ) )
          & ( r2_hidden(X4,sK3)
            | r2_hidden(X4,sK2)
            | ~ r2_hidden(X4,sK1) ) )
        | ~ m1_subset_1(X4,sK0) )
    & m1_subset_1(sK3,k1_zfmisc_1(sK0))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f18,f17,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( k4_subset_1(X0,X2,X3) != X1
                & ! [X4] :
                    ( ( ( r2_hidden(X4,X1)
                        | ( ~ r2_hidden(X4,X3)
                          & ~ r2_hidden(X4,X2) ) )
                      & ( r2_hidden(X4,X3)
                        | r2_hidden(X4,X2)
                        | ~ r2_hidden(X4,X1) ) )
                    | ~ m1_subset_1(X4,X0) )
                & m1_subset_1(X3,k1_zfmisc_1(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( sK1 != k4_subset_1(sK0,X2,X3)
              & ! [X4] :
                  ( ( ( r2_hidden(X4,sK1)
                      | ( ~ r2_hidden(X4,X3)
                        & ~ r2_hidden(X4,X2) ) )
                    & ( r2_hidden(X4,X3)
                      | r2_hidden(X4,X2)
                      | ~ r2_hidden(X4,sK1) ) )
                  | ~ m1_subset_1(X4,sK0) )
              & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( sK1 != k4_subset_1(sK0,X2,X3)
            & ! [X4] :
                ( ( ( r2_hidden(X4,sK1)
                    | ( ~ r2_hidden(X4,X3)
                      & ~ r2_hidden(X4,X2) ) )
                  & ( r2_hidden(X4,X3)
                    | r2_hidden(X4,X2)
                    | ~ r2_hidden(X4,sK1) ) )
                | ~ m1_subset_1(X4,sK0) )
            & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ? [X3] :
          ( sK1 != k4_subset_1(sK0,sK2,X3)
          & ! [X4] :
              ( ( ( r2_hidden(X4,sK1)
                  | ( ~ r2_hidden(X4,X3)
                    & ~ r2_hidden(X4,sK2) ) )
                & ( r2_hidden(X4,X3)
                  | r2_hidden(X4,sK2)
                  | ~ r2_hidden(X4,sK1) ) )
              | ~ m1_subset_1(X4,sK0) )
          & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X3] :
        ( sK1 != k4_subset_1(sK0,sK2,X3)
        & ! [X4] :
            ( ( ( r2_hidden(X4,sK1)
                | ( ~ r2_hidden(X4,X3)
                  & ~ r2_hidden(X4,sK2) ) )
              & ( r2_hidden(X4,X3)
                | r2_hidden(X4,sK2)
                | ~ r2_hidden(X4,sK1) ) )
            | ~ m1_subset_1(X4,sK0) )
        & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
   => ( sK1 != k4_subset_1(sK0,sK2,sK3)
      & ! [X4] :
          ( ( ( r2_hidden(X4,sK1)
              | ( ~ r2_hidden(X4,sK3)
                & ~ r2_hidden(X4,sK2) ) )
            & ( r2_hidden(X4,sK3)
              | r2_hidden(X4,sK2)
              | ~ r2_hidden(X4,sK1) ) )
          | ~ m1_subset_1(X4,sK0) )
      & m1_subset_1(sK3,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k4_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( ( r2_hidden(X4,X1)
                      | ( ~ r2_hidden(X4,X3)
                        & ~ r2_hidden(X4,X2) ) )
                    & ( r2_hidden(X4,X3)
                      | r2_hidden(X4,X2)
                      | ~ r2_hidden(X4,X1) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k4_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( ( r2_hidden(X4,X1)
                      | ( ~ r2_hidden(X4,X3)
                        & ~ r2_hidden(X4,X2) ) )
                    & ( r2_hidden(X4,X3)
                      | r2_hidden(X4,X2)
                      | ~ r2_hidden(X4,X1) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k4_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( r2_hidden(X4,X1)
                  <=> ( r2_hidden(X4,X3)
                      | r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k4_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( r2_hidden(X4,X1)
                  <=> ( r2_hidden(X4,X3)
                      | r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,X1)
                      <=> ( r2_hidden(X4,X3)
                          | r2_hidden(X4,X2) ) ) )
                 => k4_subset_1(X0,X2,X3) = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(X0))
             => ( ! [X4] :
                    ( m1_subset_1(X4,X0)
                   => ( r2_hidden(X4,X1)
                    <=> ( r2_hidden(X4,X3)
                        | r2_hidden(X4,X2) ) ) )
               => k4_subset_1(X0,X2,X3) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_subset_1)).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(subsumption_resolution,[],[f40,f37])).

fof(f37,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
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

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f572,plain,
    ( ~ r2_hidden(sK5(sK2,sK3,sK1),sK3)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f91,f240])).

fof(f91,plain,
    ( ~ r2_hidden(sK5(sK2,sK3,sK1),sK3)
    | ~ r2_hidden(sK5(sK2,sK3,sK1),sK1) ),
    inference(resolution,[],[f88,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( sQ6_eqProxy(k2_xboole_0(X0,X1),X2)
      | ~ r2_hidden(sK5(X0,X1,X2),X1)
      | ~ r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f50,f54])).

fof(f54,plain,(
    ! [X1,X0] :
      ( sQ6_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ6_eqProxy])])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK5(X0,X1,X2),X1)
      | ~ r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
              & ~ r2_hidden(sK5(X0,X1,X2),X0) )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( r2_hidden(sK5(X0,X1,X2),X1)
            | r2_hidden(sK5(X0,X1,X2),X0)
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f27,f28])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            & ~ r2_hidden(sK5(X0,X1,X2),X0) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( r2_hidden(sK5(X0,X1,X2),X1)
          | r2_hidden(sK5(X0,X1,X2),X0)
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f88,plain,(
    ~ sQ6_eqProxy(k2_xboole_0(sK2,sK3),sK1) ),
    inference(subsumption_resolution,[],[f87,f31])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f87,plain,
    ( ~ sQ6_eqProxy(k2_xboole_0(sK2,sK3),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f83,f32])).

fof(f32,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f83,plain,
    ( ~ sQ6_eqProxy(k2_xboole_0(sK2,sK3),sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f79,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( sQ6_eqProxy(k4_subset_1(X0,X1,X2),k2_xboole_0(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(equality_proxy_replacement,[],[f44,f54])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f79,plain,(
    ! [X1] :
      ( ~ sQ6_eqProxy(k4_subset_1(sK0,sK2,sK3),X1)
      | ~ sQ6_eqProxy(X1,sK1) ) ),
    inference(resolution,[],[f70,f71])).

fof(f71,plain,(
    ~ sQ6_eqProxy(k4_subset_1(sK0,sK2,sK3),sK1) ),
    inference(resolution,[],[f69,f55])).

fof(f55,plain,(
    ~ sQ6_eqProxy(sK1,k4_subset_1(sK0,sK2,sK3)) ),
    inference(equality_proxy_replacement,[],[f36,f54])).

fof(f36,plain,(
    sK1 != k4_subset_1(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f69,plain,(
    ! [X0,X1] :
      ( sQ6_eqProxy(X1,X0)
      | ~ sQ6_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f54])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( sQ6_eqProxy(X0,X2)
      | ~ sQ6_eqProxy(X1,X2)
      | ~ sQ6_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f54])).

fof(f240,plain,
    ( r2_hidden(sK5(sK2,sK3,sK1),sK1)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f239])).

fof(f239,plain,
    ( spl7_1
  <=> r2_hidden(sK5(sK2,sK3,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f554,plain,
    ( spl7_1
    | ~ spl7_2 ),
    inference(avatar_contradiction_clause,[],[f548])).

fof(f548,plain,
    ( $false
    | spl7_1
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f31,f244,f547,f43])).

fof(f547,plain,
    ( ~ r2_hidden(sK5(sK2,sK3,sK1),sK0)
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f521,f244])).

fof(f521,plain,
    ( ~ r2_hidden(sK5(sK2,sK3,sK1),sK2)
    | ~ r2_hidden(sK5(sK2,sK3,sK1),sK0)
    | spl7_1 ),
    inference(resolution,[],[f241,f77])).

fof(f77,plain,(
    ! [X2] :
      ( r2_hidden(X2,sK1)
      | ~ r2_hidden(X2,sK2)
      | ~ r2_hidden(X2,sK0) ) ),
    inference(resolution,[],[f73,f34])).

fof(f34,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK0)
      | ~ r2_hidden(X4,sK2)
      | r2_hidden(X4,sK1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f241,plain,
    ( ~ r2_hidden(sK5(sK2,sK3,sK1),sK1)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f239])).

fof(f244,plain,
    ( r2_hidden(sK5(sK2,sK3,sK1),sK2)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f243])).

fof(f509,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_contradiction_clause,[],[f503])).

fof(f503,plain,
    ( $false
    | spl7_1
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f32,f339,f490,f43])).

fof(f490,plain,
    ( ~ r2_hidden(sK5(sK2,sK3,sK1),sK0)
    | spl7_1
    | spl7_2 ),
    inference(subsumption_resolution,[],[f251,f339])).

fof(f251,plain,
    ( ~ r2_hidden(sK5(sK2,sK3,sK1),sK3)
    | ~ r2_hidden(sK5(sK2,sK3,sK1),sK0)
    | spl7_1 ),
    inference(resolution,[],[f241,f76])).

fof(f76,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK1)
      | ~ r2_hidden(X1,sK3)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f73,f35])).

fof(f35,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK0)
      | ~ r2_hidden(X4,sK3)
      | r2_hidden(X4,sK1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f339,plain,
    ( r2_hidden(sK5(sK2,sK3,sK1),sK3)
    | spl7_1
    | spl7_2 ),
    inference(subsumption_resolution,[],[f338,f241])).

fof(f338,plain,
    ( r2_hidden(sK5(sK2,sK3,sK1),sK3)
    | r2_hidden(sK5(sK2,sK3,sK1),sK1)
    | spl7_2 ),
    inference(subsumption_resolution,[],[f89,f245])).

fof(f89,plain,
    ( r2_hidden(sK5(sK2,sK3,sK1),sK3)
    | r2_hidden(sK5(sK2,sK3,sK1),sK2)
    | r2_hidden(sK5(sK2,sK3,sK1),sK1) ),
    inference(resolution,[],[f88,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( sQ6_eqProxy(k2_xboole_0(X0,X1),X2)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | r2_hidden(sK5(X0,X1,X2),X0)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f48,f54])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK5(X0,X1,X2),X1)
      | r2_hidden(sK5(X0,X1,X2),X0)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f246,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f90,f243,f239])).

fof(f90,plain,
    ( ~ r2_hidden(sK5(sK2,sK3,sK1),sK2)
    | ~ r2_hidden(sK5(sK2,sK3,sK1),sK1) ),
    inference(resolution,[],[f88,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( sQ6_eqProxy(k2_xboole_0(X0,X1),X2)
      | ~ r2_hidden(sK5(X0,X1,X2),X0)
      | ~ r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f49,f54])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK5(X0,X1,X2),X0)
      | ~ r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:37:42 EST 2020
% 0.18/0.33  % CPUTime    : 
% 0.18/0.45  % (31058)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.18/0.45  % (31050)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.18/0.46  % (31053)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.18/0.46  % (31067)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.18/0.47  % (31057)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.18/0.47  % (31068)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.18/0.47  % (31052)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.18/0.47  % (31056)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.18/0.48  % (31066)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.18/0.48  % (31063)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.18/0.48  % (31054)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.18/0.48  % (31060)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.18/0.48  % (31048)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.18/0.48  % (31055)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.18/0.49  % (31049)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.18/0.49  % (31065)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.18/0.49  % (31049)Refutation not found, incomplete strategy% (31049)------------------------------
% 0.18/0.49  % (31049)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.49  % (31049)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.49  
% 0.18/0.49  % (31049)Memory used [KB]: 10618
% 0.18/0.49  % (31049)Time elapsed: 0.084 s
% 0.18/0.49  % (31049)------------------------------
% 0.18/0.49  % (31049)------------------------------
% 0.18/0.49  % (31064)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.18/0.49  % (31051)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.18/0.50  % (31061)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.18/0.50  % (31062)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.18/0.50  % (31059)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.18/0.50  % (31068)Refutation not found, incomplete strategy% (31068)------------------------------
% 0.18/0.50  % (31068)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.50  % (31068)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.50  
% 0.18/0.50  % (31068)Memory used [KB]: 11001
% 0.18/0.50  % (31068)Time elapsed: 0.093 s
% 0.18/0.50  % (31068)------------------------------
% 0.18/0.50  % (31068)------------------------------
% 0.18/0.50  % (31059)Refutation not found, incomplete strategy% (31059)------------------------------
% 0.18/0.50  % (31059)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.50  % (31059)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.50  
% 0.18/0.50  % (31059)Memory used [KB]: 10618
% 0.18/0.50  % (31059)Time elapsed: 0.108 s
% 0.18/0.50  % (31059)------------------------------
% 0.18/0.50  % (31059)------------------------------
% 0.18/0.51  % (31053)Refutation found. Thanks to Tanya!
% 0.18/0.51  % SZS status Theorem for theBenchmark
% 0.18/0.51  % SZS output start Proof for theBenchmark
% 0.18/0.51  fof(f599,plain,(
% 0.18/0.51    $false),
% 0.18/0.51    inference(avatar_sat_refutation,[],[f246,f509,f554,f598])).
% 0.18/0.51  fof(f598,plain,(
% 0.18/0.51    ~spl7_1 | spl7_2),
% 0.18/0.51    inference(avatar_contradiction_clause,[],[f592])).
% 0.18/0.51  fof(f592,plain,(
% 0.18/0.51    $false | (~spl7_1 | spl7_2)),
% 0.18/0.51    inference(unit_resulting_resolution,[],[f30,f240,f586,f43])).
% 0.18/0.51  fof(f43,plain,(
% 0.18/0.51    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.18/0.51    inference(cnf_transformation,[],[f11])).
% 0.18/0.51  fof(f11,plain,(
% 0.18/0.51    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.18/0.51    inference(ennf_transformation,[],[f4])).
% 0.18/0.51  fof(f4,axiom,(
% 0.18/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.18/0.51  fof(f586,plain,(
% 0.18/0.51    ~r2_hidden(sK5(sK2,sK3,sK1),sK0) | (~spl7_1 | spl7_2)),
% 0.18/0.51    inference(subsumption_resolution,[],[f585,f240])).
% 0.18/0.51  fof(f585,plain,(
% 0.18/0.51    ~r2_hidden(sK5(sK2,sK3,sK1),sK1) | ~r2_hidden(sK5(sK2,sK3,sK1),sK0) | (~spl7_1 | spl7_2)),
% 0.18/0.51    inference(subsumption_resolution,[],[f577,f245])).
% 0.18/0.51  fof(f245,plain,(
% 0.18/0.51    ~r2_hidden(sK5(sK2,sK3,sK1),sK2) | spl7_2),
% 0.18/0.51    inference(avatar_component_clause,[],[f243])).
% 0.18/0.51  fof(f243,plain,(
% 0.18/0.51    spl7_2 <=> r2_hidden(sK5(sK2,sK3,sK1),sK2)),
% 0.18/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.18/0.51  fof(f577,plain,(
% 0.18/0.51    r2_hidden(sK5(sK2,sK3,sK1),sK2) | ~r2_hidden(sK5(sK2,sK3,sK1),sK1) | ~r2_hidden(sK5(sK2,sK3,sK1),sK0) | ~spl7_1),
% 0.18/0.51    inference(resolution,[],[f572,f75])).
% 0.18/0.51  fof(f75,plain,(
% 0.18/0.51    ( ! [X0] : (r2_hidden(X0,sK3) | r2_hidden(X0,sK2) | ~r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) )),
% 0.18/0.51    inference(resolution,[],[f73,f33])).
% 0.18/0.51  fof(f33,plain,(
% 0.18/0.51    ( ! [X4] : (~m1_subset_1(X4,sK0) | r2_hidden(X4,sK2) | ~r2_hidden(X4,sK1) | r2_hidden(X4,sK3)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f19])).
% 0.18/0.51  fof(f19,plain,(
% 0.18/0.51    ((sK1 != k4_subset_1(sK0,sK2,sK3) & ! [X4] : (((r2_hidden(X4,sK1) | (~r2_hidden(X4,sK3) & ~r2_hidden(X4,sK2))) & (r2_hidden(X4,sK3) | r2_hidden(X4,sK2) | ~r2_hidden(X4,sK1))) | ~m1_subset_1(X4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.18/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f18,f17,f16])).
% 0.18/0.51  fof(f16,plain,(
% 0.18/0.51    ? [X0,X1] : (? [X2] : (? [X3] : (k4_subset_1(X0,X2,X3) != X1 & ! [X4] : (((r2_hidden(X4,X1) | (~r2_hidden(X4,X3) & ~r2_hidden(X4,X2))) & (r2_hidden(X4,X3) | r2_hidden(X4,X2) | ~r2_hidden(X4,X1))) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (? [X3] : (sK1 != k4_subset_1(sK0,X2,X3) & ! [X4] : (((r2_hidden(X4,sK1) | (~r2_hidden(X4,X3) & ~r2_hidden(X4,X2))) & (r2_hidden(X4,X3) | r2_hidden(X4,X2) | ~r2_hidden(X4,sK1))) | ~m1_subset_1(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.18/0.51    introduced(choice_axiom,[])).
% 0.18/0.51  fof(f17,plain,(
% 0.18/0.51    ? [X2] : (? [X3] : (sK1 != k4_subset_1(sK0,X2,X3) & ! [X4] : (((r2_hidden(X4,sK1) | (~r2_hidden(X4,X3) & ~r2_hidden(X4,X2))) & (r2_hidden(X4,X3) | r2_hidden(X4,X2) | ~r2_hidden(X4,sK1))) | ~m1_subset_1(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (? [X3] : (sK1 != k4_subset_1(sK0,sK2,X3) & ! [X4] : (((r2_hidden(X4,sK1) | (~r2_hidden(X4,X3) & ~r2_hidden(X4,sK2))) & (r2_hidden(X4,X3) | r2_hidden(X4,sK2) | ~r2_hidden(X4,sK1))) | ~m1_subset_1(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.18/0.51    introduced(choice_axiom,[])).
% 0.18/0.51  fof(f18,plain,(
% 0.18/0.51    ? [X3] : (sK1 != k4_subset_1(sK0,sK2,X3) & ! [X4] : (((r2_hidden(X4,sK1) | (~r2_hidden(X4,X3) & ~r2_hidden(X4,sK2))) & (r2_hidden(X4,X3) | r2_hidden(X4,sK2) | ~r2_hidden(X4,sK1))) | ~m1_subset_1(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(sK0))) => (sK1 != k4_subset_1(sK0,sK2,sK3) & ! [X4] : (((r2_hidden(X4,sK1) | (~r2_hidden(X4,sK3) & ~r2_hidden(X4,sK2))) & (r2_hidden(X4,sK3) | r2_hidden(X4,sK2) | ~r2_hidden(X4,sK1))) | ~m1_subset_1(X4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(sK0)))),
% 0.18/0.51    introduced(choice_axiom,[])).
% 0.18/0.51  fof(f15,plain,(
% 0.18/0.51    ? [X0,X1] : (? [X2] : (? [X3] : (k4_subset_1(X0,X2,X3) != X1 & ! [X4] : (((r2_hidden(X4,X1) | (~r2_hidden(X4,X3) & ~r2_hidden(X4,X2))) & (r2_hidden(X4,X3) | r2_hidden(X4,X2) | ~r2_hidden(X4,X1))) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.18/0.51    inference(flattening,[],[f14])).
% 0.18/0.51  fof(f14,plain,(
% 0.18/0.51    ? [X0,X1] : (? [X2] : (? [X3] : (k4_subset_1(X0,X2,X3) != X1 & ! [X4] : (((r2_hidden(X4,X1) | (~r2_hidden(X4,X3) & ~r2_hidden(X4,X2))) & ((r2_hidden(X4,X3) | r2_hidden(X4,X2)) | ~r2_hidden(X4,X1))) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.18/0.51    inference(nnf_transformation,[],[f9])).
% 0.18/0.51  fof(f9,plain,(
% 0.18/0.51    ? [X0,X1] : (? [X2] : (? [X3] : (k4_subset_1(X0,X2,X3) != X1 & ! [X4] : ((r2_hidden(X4,X1) <=> (r2_hidden(X4,X3) | r2_hidden(X4,X2))) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.18/0.51    inference(flattening,[],[f8])).
% 0.18/0.51  fof(f8,plain,(
% 0.18/0.51    ? [X0,X1] : (? [X2] : (? [X3] : ((k4_subset_1(X0,X2,X3) != X1 & ! [X4] : ((r2_hidden(X4,X1) <=> (r2_hidden(X4,X3) | r2_hidden(X4,X2))) | ~m1_subset_1(X4,X0))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.18/0.51    inference(ennf_transformation,[],[f7])).
% 0.18/0.51  fof(f7,negated_conjecture,(
% 0.18/0.51    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,X1) <=> (r2_hidden(X4,X3) | r2_hidden(X4,X2)))) => k4_subset_1(X0,X2,X3) = X1))))),
% 0.18/0.51    inference(negated_conjecture,[],[f6])).
% 0.18/0.51  fof(f6,conjecture,(
% 0.18/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,X1) <=> (r2_hidden(X4,X3) | r2_hidden(X4,X2)))) => k4_subset_1(X0,X2,X3) = X1))))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_subset_1)).
% 0.18/0.51  fof(f73,plain,(
% 0.18/0.51    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) )),
% 0.18/0.51    inference(subsumption_resolution,[],[f40,f37])).
% 0.18/0.51  fof(f37,plain,(
% 0.18/0.51    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f23])).
% 0.18/0.51  fof(f23,plain,(
% 0.18/0.51    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.18/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f22])).
% 0.18/0.51  fof(f22,plain,(
% 0.18/0.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.18/0.51    introduced(choice_axiom,[])).
% 0.18/0.51  fof(f21,plain,(
% 0.18/0.51    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.18/0.51    inference(rectify,[],[f20])).
% 0.18/0.51  fof(f20,plain,(
% 0.18/0.51    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.18/0.51    inference(nnf_transformation,[],[f1])).
% 0.18/0.51  fof(f1,axiom,(
% 0.18/0.51    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.18/0.51  fof(f40,plain,(
% 0.18/0.51    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f24])).
% 0.18/0.51  fof(f24,plain,(
% 0.18/0.51    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.18/0.51    inference(nnf_transformation,[],[f10])).
% 0.18/0.51  fof(f10,plain,(
% 0.18/0.51    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.18/0.51    inference(ennf_transformation,[],[f3])).
% 0.18/0.51  fof(f3,axiom,(
% 0.18/0.51    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.18/0.51  fof(f572,plain,(
% 0.18/0.51    ~r2_hidden(sK5(sK2,sK3,sK1),sK3) | ~spl7_1),
% 0.18/0.51    inference(subsumption_resolution,[],[f91,f240])).
% 0.18/0.51  fof(f91,plain,(
% 0.18/0.51    ~r2_hidden(sK5(sK2,sK3,sK1),sK3) | ~r2_hidden(sK5(sK2,sK3,sK1),sK1)),
% 0.18/0.51    inference(resolution,[],[f88,f57])).
% 0.18/0.51  fof(f57,plain,(
% 0.18/0.51    ( ! [X2,X0,X1] : (sQ6_eqProxy(k2_xboole_0(X0,X1),X2) | ~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X2)) )),
% 0.18/0.51    inference(equality_proxy_replacement,[],[f50,f54])).
% 0.18/0.51  fof(f54,plain,(
% 0.18/0.51    ! [X1,X0] : (sQ6_eqProxy(X0,X1) <=> X0 = X1)),
% 0.18/0.51    introduced(equality_proxy_definition,[new_symbols(naming,[sQ6_eqProxy])])).
% 0.18/0.51  fof(f50,plain,(
% 0.18/0.51    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X2)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f29])).
% 0.18/0.51  fof(f29,plain,(
% 0.18/0.51    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK5(X0,X1,X2),X1) & ~r2_hidden(sK5(X0,X1,X2),X0)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.18/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f27,f28])).
% 0.18/0.51  fof(f28,plain,(
% 0.18/0.51    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK5(X0,X1,X2),X1) & ~r2_hidden(sK5(X0,X1,X2),X0)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.18/0.51    introduced(choice_axiom,[])).
% 0.18/0.51  fof(f27,plain,(
% 0.18/0.51    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.18/0.51    inference(rectify,[],[f26])).
% 0.18/0.51  fof(f26,plain,(
% 0.18/0.51    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.18/0.51    inference(flattening,[],[f25])).
% 0.18/0.51  fof(f25,plain,(
% 0.18/0.51    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.18/0.51    inference(nnf_transformation,[],[f2])).
% 0.18/0.51  fof(f2,axiom,(
% 0.18/0.51    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.18/0.51  fof(f88,plain,(
% 0.18/0.51    ~sQ6_eqProxy(k2_xboole_0(sK2,sK3),sK1)),
% 0.18/0.51    inference(subsumption_resolution,[],[f87,f31])).
% 0.18/0.51  fof(f31,plain,(
% 0.18/0.51    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.18/0.51    inference(cnf_transformation,[],[f19])).
% 0.18/0.51  fof(f87,plain,(
% 0.18/0.51    ~sQ6_eqProxy(k2_xboole_0(sK2,sK3),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.18/0.51    inference(subsumption_resolution,[],[f83,f32])).
% 0.18/0.51  fof(f32,plain,(
% 0.18/0.51    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.18/0.51    inference(cnf_transformation,[],[f19])).
% 0.18/0.51  fof(f83,plain,(
% 0.18/0.51    ~sQ6_eqProxy(k2_xboole_0(sK2,sK3),sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.18/0.51    inference(resolution,[],[f79,f56])).
% 0.18/0.51  fof(f56,plain,(
% 0.18/0.51    ( ! [X2,X0,X1] : (sQ6_eqProxy(k4_subset_1(X0,X1,X2),k2_xboole_0(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.18/0.51    inference(equality_proxy_replacement,[],[f44,f54])).
% 0.18/0.51  fof(f44,plain,(
% 0.18/0.51    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.18/0.51    inference(cnf_transformation,[],[f13])).
% 0.18/0.51  fof(f13,plain,(
% 0.18/0.51    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.18/0.51    inference(flattening,[],[f12])).
% 0.18/0.51  fof(f12,plain,(
% 0.18/0.51    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.18/0.51    inference(ennf_transformation,[],[f5])).
% 0.18/0.51  fof(f5,axiom,(
% 0.18/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.18/0.51  fof(f79,plain,(
% 0.18/0.51    ( ! [X1] : (~sQ6_eqProxy(k4_subset_1(sK0,sK2,sK3),X1) | ~sQ6_eqProxy(X1,sK1)) )),
% 0.18/0.51    inference(resolution,[],[f70,f71])).
% 0.18/0.51  fof(f71,plain,(
% 0.18/0.51    ~sQ6_eqProxy(k4_subset_1(sK0,sK2,sK3),sK1)),
% 0.18/0.51    inference(resolution,[],[f69,f55])).
% 0.18/0.51  fof(f55,plain,(
% 0.18/0.51    ~sQ6_eqProxy(sK1,k4_subset_1(sK0,sK2,sK3))),
% 0.18/0.51    inference(equality_proxy_replacement,[],[f36,f54])).
% 0.18/0.51  fof(f36,plain,(
% 0.18/0.51    sK1 != k4_subset_1(sK0,sK2,sK3)),
% 0.18/0.51    inference(cnf_transformation,[],[f19])).
% 0.18/0.51  fof(f69,plain,(
% 0.18/0.51    ( ! [X0,X1] : (sQ6_eqProxy(X1,X0) | ~sQ6_eqProxy(X0,X1)) )),
% 0.18/0.51    inference(equality_proxy_axiom,[],[f54])).
% 0.18/0.51  fof(f70,plain,(
% 0.18/0.51    ( ! [X2,X0,X1] : (sQ6_eqProxy(X0,X2) | ~sQ6_eqProxy(X1,X2) | ~sQ6_eqProxy(X0,X1)) )),
% 0.18/0.51    inference(equality_proxy_axiom,[],[f54])).
% 0.18/0.51  fof(f240,plain,(
% 0.18/0.51    r2_hidden(sK5(sK2,sK3,sK1),sK1) | ~spl7_1),
% 0.18/0.51    inference(avatar_component_clause,[],[f239])).
% 0.18/0.51  fof(f239,plain,(
% 0.18/0.51    spl7_1 <=> r2_hidden(sK5(sK2,sK3,sK1),sK1)),
% 0.18/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.18/0.51  fof(f30,plain,(
% 0.18/0.51    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.18/0.51    inference(cnf_transformation,[],[f19])).
% 0.18/0.51  fof(f554,plain,(
% 0.18/0.51    spl7_1 | ~spl7_2),
% 0.18/0.51    inference(avatar_contradiction_clause,[],[f548])).
% 0.18/0.51  fof(f548,plain,(
% 0.18/0.51    $false | (spl7_1 | ~spl7_2)),
% 0.18/0.51    inference(unit_resulting_resolution,[],[f31,f244,f547,f43])).
% 0.18/0.51  fof(f547,plain,(
% 0.18/0.51    ~r2_hidden(sK5(sK2,sK3,sK1),sK0) | (spl7_1 | ~spl7_2)),
% 0.18/0.51    inference(subsumption_resolution,[],[f521,f244])).
% 0.18/0.51  fof(f521,plain,(
% 0.18/0.51    ~r2_hidden(sK5(sK2,sK3,sK1),sK2) | ~r2_hidden(sK5(sK2,sK3,sK1),sK0) | spl7_1),
% 0.18/0.51    inference(resolution,[],[f241,f77])).
% 0.18/0.51  fof(f77,plain,(
% 0.18/0.51    ( ! [X2] : (r2_hidden(X2,sK1) | ~r2_hidden(X2,sK2) | ~r2_hidden(X2,sK0)) )),
% 0.18/0.51    inference(resolution,[],[f73,f34])).
% 0.18/0.51  fof(f34,plain,(
% 0.18/0.51    ( ! [X4] : (~m1_subset_1(X4,sK0) | ~r2_hidden(X4,sK2) | r2_hidden(X4,sK1)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f19])).
% 0.18/0.51  fof(f241,plain,(
% 0.18/0.51    ~r2_hidden(sK5(sK2,sK3,sK1),sK1) | spl7_1),
% 0.18/0.51    inference(avatar_component_clause,[],[f239])).
% 0.18/0.51  fof(f244,plain,(
% 0.18/0.51    r2_hidden(sK5(sK2,sK3,sK1),sK2) | ~spl7_2),
% 0.18/0.51    inference(avatar_component_clause,[],[f243])).
% 0.18/0.51  fof(f509,plain,(
% 0.18/0.51    spl7_1 | spl7_2),
% 0.18/0.51    inference(avatar_contradiction_clause,[],[f503])).
% 0.18/0.51  fof(f503,plain,(
% 0.18/0.51    $false | (spl7_1 | spl7_2)),
% 0.18/0.51    inference(unit_resulting_resolution,[],[f32,f339,f490,f43])).
% 0.18/0.51  fof(f490,plain,(
% 0.18/0.51    ~r2_hidden(sK5(sK2,sK3,sK1),sK0) | (spl7_1 | spl7_2)),
% 0.18/0.51    inference(subsumption_resolution,[],[f251,f339])).
% 0.18/0.51  fof(f251,plain,(
% 0.18/0.51    ~r2_hidden(sK5(sK2,sK3,sK1),sK3) | ~r2_hidden(sK5(sK2,sK3,sK1),sK0) | spl7_1),
% 0.18/0.51    inference(resolution,[],[f241,f76])).
% 0.18/0.51  fof(f76,plain,(
% 0.18/0.51    ( ! [X1] : (r2_hidden(X1,sK1) | ~r2_hidden(X1,sK3) | ~r2_hidden(X1,sK0)) )),
% 0.18/0.51    inference(resolution,[],[f73,f35])).
% 0.18/0.51  fof(f35,plain,(
% 0.18/0.51    ( ! [X4] : (~m1_subset_1(X4,sK0) | ~r2_hidden(X4,sK3) | r2_hidden(X4,sK1)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f19])).
% 0.18/0.51  fof(f339,plain,(
% 0.18/0.51    r2_hidden(sK5(sK2,sK3,sK1),sK3) | (spl7_1 | spl7_2)),
% 0.18/0.51    inference(subsumption_resolution,[],[f338,f241])).
% 0.18/0.51  fof(f338,plain,(
% 0.18/0.51    r2_hidden(sK5(sK2,sK3,sK1),sK3) | r2_hidden(sK5(sK2,sK3,sK1),sK1) | spl7_2),
% 0.18/0.51    inference(subsumption_resolution,[],[f89,f245])).
% 0.18/0.51  fof(f89,plain,(
% 0.18/0.51    r2_hidden(sK5(sK2,sK3,sK1),sK3) | r2_hidden(sK5(sK2,sK3,sK1),sK2) | r2_hidden(sK5(sK2,sK3,sK1),sK1)),
% 0.18/0.51    inference(resolution,[],[f88,f59])).
% 0.18/0.51  fof(f59,plain,(
% 0.18/0.51    ( ! [X2,X0,X1] : (sQ6_eqProxy(k2_xboole_0(X0,X1),X2) | r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2)) )),
% 0.18/0.51    inference(equality_proxy_replacement,[],[f48,f54])).
% 0.18/0.51  fof(f48,plain,(
% 0.18/0.51    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f29])).
% 0.18/0.51  fof(f246,plain,(
% 0.18/0.51    ~spl7_1 | ~spl7_2),
% 0.18/0.51    inference(avatar_split_clause,[],[f90,f243,f239])).
% 0.18/0.51  fof(f90,plain,(
% 0.18/0.51    ~r2_hidden(sK5(sK2,sK3,sK1),sK2) | ~r2_hidden(sK5(sK2,sK3,sK1),sK1)),
% 0.18/0.51    inference(resolution,[],[f88,f58])).
% 0.18/0.51  fof(f58,plain,(
% 0.18/0.51    ( ! [X2,X0,X1] : (sQ6_eqProxy(k2_xboole_0(X0,X1),X2) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) )),
% 0.18/0.51    inference(equality_proxy_replacement,[],[f49,f54])).
% 0.18/0.51  fof(f49,plain,(
% 0.18/0.51    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f29])).
% 0.18/0.51  % SZS output end Proof for theBenchmark
% 0.18/0.51  % (31053)------------------------------
% 0.18/0.51  % (31053)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.51  % (31053)Termination reason: Refutation
% 0.18/0.51  
% 0.18/0.51  % (31053)Memory used [KB]: 6396
% 0.18/0.51  % (31053)Time elapsed: 0.098 s
% 0.18/0.51  % (31053)------------------------------
% 0.18/0.51  % (31053)------------------------------
% 0.18/0.51  % (31047)Success in time 0.169 s
%------------------------------------------------------------------------------
