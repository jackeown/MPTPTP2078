%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:47 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 342 expanded)
%              Number of leaves         :   14 ( 113 expanded)
%              Depth                    :   20
%              Number of atoms          :  384 (2485 expanded)
%              Number of equality atoms :   30 ( 258 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f585,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f239,f529,f564,f584])).

fof(f584,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_contradiction_clause,[],[f578])).

fof(f578,plain,
    ( $false
    | ~ spl7_1
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f29,f234,f577,f42])).

fof(f42,plain,(
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

fof(f577,plain,
    ( ~ r2_hidden(sK5(sK2,sK3,sK1),sK0)
    | ~ spl7_1
    | spl7_2 ),
    inference(subsumption_resolution,[],[f570,f234])).

fof(f570,plain,
    ( ~ r2_hidden(sK5(sK2,sK3,sK1),sK1)
    | ~ r2_hidden(sK5(sK2,sK3,sK1),sK0)
    | spl7_2 ),
    inference(resolution,[],[f237,f75])).

fof(f75,plain,(
    ! [X2] :
      ( r2_hidden(X2,sK2)
      | ~ r2_hidden(X2,sK1)
      | ~ r2_hidden(X2,sK0) ) ),
    inference(resolution,[],[f72,f32])).

fof(f32,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK0)
      | ~ r2_hidden(X4,sK1)
      | r2_hidden(X4,sK2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( sK1 != k9_subset_1(sK0,sK2,sK3)
    & ! [X4] :
        ( ( ( r2_hidden(X4,sK1)
            | ~ r2_hidden(X4,sK3)
            | ~ r2_hidden(X4,sK2) )
          & ( ( r2_hidden(X4,sK3)
              & r2_hidden(X4,sK2) )
            | ~ r2_hidden(X4,sK1) ) )
        | ~ m1_subset_1(X4,sK0) )
    & m1_subset_1(sK3,k1_zfmisc_1(sK0))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f17,f16,f15])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( k9_subset_1(X0,X2,X3) != X1
                & ! [X4] :
                    ( ( ( r2_hidden(X4,X1)
                        | ~ r2_hidden(X4,X3)
                        | ~ r2_hidden(X4,X2) )
                      & ( ( r2_hidden(X4,X3)
                          & r2_hidden(X4,X2) )
                        | ~ r2_hidden(X4,X1) ) )
                    | ~ m1_subset_1(X4,X0) )
                & m1_subset_1(X3,k1_zfmisc_1(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( sK1 != k9_subset_1(sK0,X2,X3)
              & ! [X4] :
                  ( ( ( r2_hidden(X4,sK1)
                      | ~ r2_hidden(X4,X3)
                      | ~ r2_hidden(X4,X2) )
                    & ( ( r2_hidden(X4,X3)
                        & r2_hidden(X4,X2) )
                      | ~ r2_hidden(X4,sK1) ) )
                  | ~ m1_subset_1(X4,sK0) )
              & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( sK1 != k9_subset_1(sK0,X2,X3)
            & ! [X4] :
                ( ( ( r2_hidden(X4,sK1)
                    | ~ r2_hidden(X4,X3)
                    | ~ r2_hidden(X4,X2) )
                  & ( ( r2_hidden(X4,X3)
                      & r2_hidden(X4,X2) )
                    | ~ r2_hidden(X4,sK1) ) )
                | ~ m1_subset_1(X4,sK0) )
            & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ? [X3] :
          ( sK1 != k9_subset_1(sK0,sK2,X3)
          & ! [X4] :
              ( ( ( r2_hidden(X4,sK1)
                  | ~ r2_hidden(X4,X3)
                  | ~ r2_hidden(X4,sK2) )
                & ( ( r2_hidden(X4,X3)
                    & r2_hidden(X4,sK2) )
                  | ~ r2_hidden(X4,sK1) ) )
              | ~ m1_subset_1(X4,sK0) )
          & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X3] :
        ( sK1 != k9_subset_1(sK0,sK2,X3)
        & ! [X4] :
            ( ( ( r2_hidden(X4,sK1)
                | ~ r2_hidden(X4,X3)
                | ~ r2_hidden(X4,sK2) )
              & ( ( r2_hidden(X4,X3)
                  & r2_hidden(X4,sK2) )
                | ~ r2_hidden(X4,sK1) ) )
            | ~ m1_subset_1(X4,sK0) )
        & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
   => ( sK1 != k9_subset_1(sK0,sK2,sK3)
      & ! [X4] :
          ( ( ( r2_hidden(X4,sK1)
              | ~ r2_hidden(X4,sK3)
              | ~ r2_hidden(X4,sK2) )
            & ( ( r2_hidden(X4,sK3)
                & r2_hidden(X4,sK2) )
              | ~ r2_hidden(X4,sK1) ) )
          | ~ m1_subset_1(X4,sK0) )
      & m1_subset_1(sK3,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k9_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( ( r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,X3)
                      | ~ r2_hidden(X4,X2) )
                    & ( ( r2_hidden(X4,X3)
                        & r2_hidden(X4,X2) )
                      | ~ r2_hidden(X4,X1) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k9_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( ( r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,X3)
                      | ~ r2_hidden(X4,X2) )
                    & ( ( r2_hidden(X4,X3)
                        & r2_hidden(X4,X2) )
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
              ( k9_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( r2_hidden(X4,X1)
                  <=> ( r2_hidden(X4,X3)
                      & r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k9_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( r2_hidden(X4,X1)
                  <=> ( r2_hidden(X4,X3)
                      & r2_hidden(X4,X2) ) )
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
                          & r2_hidden(X4,X2) ) ) )
                 => k9_subset_1(X0,X2,X3) = X1 ) ) ) ) ),
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
                        & r2_hidden(X4,X2) ) ) )
               => k9_subset_1(X0,X2,X3) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_subset_1)).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(subsumption_resolution,[],[f39,f36])).

fof(f36,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f21])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
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

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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

fof(f237,plain,
    ( ~ r2_hidden(sK5(sK2,sK3,sK1),sK2)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f236])).

fof(f236,plain,
    ( spl7_2
  <=> r2_hidden(sK5(sK2,sK3,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f234,plain,
    ( r2_hidden(sK5(sK2,sK3,sK1),sK1)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl7_1
  <=> r2_hidden(sK5(sK2,sK3,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f29,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f564,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_contradiction_clause,[],[f557])).

fof(f557,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f29,f234,f555,f42])).

fof(f555,plain,
    ( ~ r2_hidden(sK5(sK2,sK3,sK1),sK0)
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f548,f234])).

fof(f548,plain,
    ( ~ r2_hidden(sK5(sK2,sK3,sK1),sK1)
    | ~ r2_hidden(sK5(sK2,sK3,sK1),sK0)
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(resolution,[],[f545,f74])).

fof(f74,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK3)
      | ~ r2_hidden(X1,sK1)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f72,f33])).

fof(f33,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK0)
      | ~ r2_hidden(X4,sK1)
      | r2_hidden(X4,sK3) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f545,plain,
    ( ~ r2_hidden(sK5(sK2,sK3,sK1),sK3)
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f532,f234])).

fof(f532,plain,
    ( ~ r2_hidden(sK5(sK2,sK3,sK1),sK3)
    | ~ r2_hidden(sK5(sK2,sK3,sK1),sK1)
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f86,f238])).

fof(f238,plain,
    ( r2_hidden(sK5(sK2,sK3,sK1),sK2)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f236])).

fof(f86,plain,
    ( ~ r2_hidden(sK5(sK2,sK3,sK1),sK3)
    | ~ r2_hidden(sK5(sK2,sK3,sK1),sK2)
    | ~ r2_hidden(sK5(sK2,sK3,sK1),sK1) ),
    inference(resolution,[],[f85,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( sQ6_eqProxy(k3_xboole_0(X0,X1),X2)
      | ~ r2_hidden(sK5(X0,X1,X2),X1)
      | ~ r2_hidden(sK5(X0,X1,X2),X0)
      | ~ r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f49,f53])).

fof(f53,plain,(
    ! [X1,X0] :
      ( sQ6_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ6_eqProxy])])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK5(X0,X1,X2),X1)
      | ~ r2_hidden(sK5(X0,X1,X2),X0)
      | ~ r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f85,plain,(
    ~ sQ6_eqProxy(k3_xboole_0(sK2,sK3),sK1) ),
    inference(subsumption_resolution,[],[f81,f31])).

fof(f31,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f81,plain,
    ( ~ sQ6_eqProxy(k3_xboole_0(sK2,sK3),sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f77,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( sQ6_eqProxy(k9_subset_1(X0,X1,X2),k3_xboole_0(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_proxy_replacement,[],[f43,f53])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f77,plain,(
    ! [X1] :
      ( ~ sQ6_eqProxy(k9_subset_1(sK0,sK2,sK3),X1)
      | ~ sQ6_eqProxy(X1,sK1) ) ),
    inference(resolution,[],[f69,f70])).

fof(f70,plain,(
    ~ sQ6_eqProxy(k9_subset_1(sK0,sK2,sK3),sK1) ),
    inference(resolution,[],[f68,f54])).

fof(f54,plain,(
    ~ sQ6_eqProxy(sK1,k9_subset_1(sK0,sK2,sK3)) ),
    inference(equality_proxy_replacement,[],[f35,f53])).

fof(f35,plain,(
    sK1 != k9_subset_1(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f68,plain,(
    ! [X0,X1] :
      ( sQ6_eqProxy(X1,X0)
      | ~ sQ6_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f53])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( sQ6_eqProxy(X0,X2)
      | ~ sQ6_eqProxy(X1,X2)
      | ~ sQ6_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f53])).

fof(f529,plain,
    ( spl7_1
    | ~ spl7_2 ),
    inference(avatar_contradiction_clause,[],[f522])).

fof(f522,plain,
    ( $false
    | spl7_1
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f31,f258,f518,f42])).

fof(f518,plain,
    ( ~ r2_hidden(sK5(sK2,sK3,sK1),sK0)
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f517,f238])).

fof(f517,plain,
    ( ~ r2_hidden(sK5(sK2,sK3,sK1),sK2)
    | ~ r2_hidden(sK5(sK2,sK3,sK1),sK0)
    | spl7_1 ),
    inference(subsumption_resolution,[],[f243,f258])).

fof(f243,plain,
    ( ~ r2_hidden(sK5(sK2,sK3,sK1),sK3)
    | ~ r2_hidden(sK5(sK2,sK3,sK1),sK2)
    | ~ r2_hidden(sK5(sK2,sK3,sK1),sK0)
    | spl7_1 ),
    inference(resolution,[],[f233,f73])).

fof(f73,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK3)
      | ~ r2_hidden(X0,sK2)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f72,f34])).

fof(f34,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK0)
      | ~ r2_hidden(X4,sK3)
      | ~ r2_hidden(X4,sK2)
      | r2_hidden(X4,sK1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f233,plain,
    ( ~ r2_hidden(sK5(sK2,sK3,sK1),sK1)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f232])).

fof(f258,plain,
    ( r2_hidden(sK5(sK2,sK3,sK1),sK3)
    | spl7_1 ),
    inference(subsumption_resolution,[],[f88,f233])).

fof(f88,plain,
    ( r2_hidden(sK5(sK2,sK3,sK1),sK3)
    | r2_hidden(sK5(sK2,sK3,sK1),sK1) ),
    inference(resolution,[],[f85,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( sQ6_eqProxy(k3_xboole_0(X0,X1),X2)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f48,f53])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK5(X0,X1,X2),X1)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f239,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f87,f236,f232])).

fof(f87,plain,
    ( r2_hidden(sK5(sK2,sK3,sK1),sK2)
    | r2_hidden(sK5(sK2,sK3,sK1),sK1) ),
    inference(resolution,[],[f85,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( sQ6_eqProxy(k3_xboole_0(X0,X1),X2)
      | r2_hidden(sK5(X0,X1,X2),X0)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f47,f53])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK5(X0,X1,X2),X0)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:13:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (2459)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.47  % (2449)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.47  % (2447)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (2451)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.48  % (2447)Refutation not found, incomplete strategy% (2447)------------------------------
% 0.20/0.48  % (2447)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (2465)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.48  % (2455)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.48  % (2447)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (2447)Memory used [KB]: 10618
% 0.20/0.48  % (2447)Time elapsed: 0.064 s
% 0.20/0.48  % (2447)------------------------------
% 0.20/0.48  % (2447)------------------------------
% 0.20/0.49  % (2460)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (2457)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.50  % (2457)Refutation not found, incomplete strategy% (2457)------------------------------
% 0.20/0.50  % (2457)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (2457)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (2457)Memory used [KB]: 10618
% 0.20/0.50  % (2457)Time elapsed: 0.098 s
% 0.20/0.50  % (2457)------------------------------
% 0.20/0.50  % (2457)------------------------------
% 0.20/0.50  % (2446)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (2453)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.50  % (2450)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.50  % (2452)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.51  % (2461)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.51  % (2466)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.51  % (2463)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.51  % (2464)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.51  % (2462)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.51  % (2448)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.51  % (2454)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.52  % (2458)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.29/0.52  % (2451)Refutation found. Thanks to Tanya!
% 1.29/0.52  % SZS status Theorem for theBenchmark
% 1.29/0.53  % (2456)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 1.29/0.53  % SZS output start Proof for theBenchmark
% 1.29/0.53  fof(f585,plain,(
% 1.29/0.53    $false),
% 1.29/0.53    inference(avatar_sat_refutation,[],[f239,f529,f564,f584])).
% 1.29/0.53  fof(f584,plain,(
% 1.29/0.53    ~spl7_1 | spl7_2),
% 1.29/0.53    inference(avatar_contradiction_clause,[],[f578])).
% 1.29/0.53  fof(f578,plain,(
% 1.29/0.53    $false | (~spl7_1 | spl7_2)),
% 1.29/0.53    inference(unit_resulting_resolution,[],[f29,f234,f577,f42])).
% 1.29/0.53  fof(f42,plain,(
% 1.29/0.53    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.29/0.53    inference(cnf_transformation,[],[f11])).
% 1.29/0.53  fof(f11,plain,(
% 1.29/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.29/0.53    inference(ennf_transformation,[],[f4])).
% 1.29/0.53  fof(f4,axiom,(
% 1.29/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.29/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 1.29/0.53  fof(f577,plain,(
% 1.29/0.53    ~r2_hidden(sK5(sK2,sK3,sK1),sK0) | (~spl7_1 | spl7_2)),
% 1.29/0.53    inference(subsumption_resolution,[],[f570,f234])).
% 1.29/0.53  fof(f570,plain,(
% 1.29/0.53    ~r2_hidden(sK5(sK2,sK3,sK1),sK1) | ~r2_hidden(sK5(sK2,sK3,sK1),sK0) | spl7_2),
% 1.29/0.53    inference(resolution,[],[f237,f75])).
% 1.29/0.53  fof(f75,plain,(
% 1.29/0.53    ( ! [X2] : (r2_hidden(X2,sK2) | ~r2_hidden(X2,sK1) | ~r2_hidden(X2,sK0)) )),
% 1.29/0.53    inference(resolution,[],[f72,f32])).
% 1.29/0.53  fof(f32,plain,(
% 1.29/0.53    ( ! [X4] : (~m1_subset_1(X4,sK0) | ~r2_hidden(X4,sK1) | r2_hidden(X4,sK2)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f18])).
% 1.29/0.53  fof(f18,plain,(
% 1.29/0.53    ((sK1 != k9_subset_1(sK0,sK2,sK3) & ! [X4] : (((r2_hidden(X4,sK1) | ~r2_hidden(X4,sK3) | ~r2_hidden(X4,sK2)) & ((r2_hidden(X4,sK3) & r2_hidden(X4,sK2)) | ~r2_hidden(X4,sK1))) | ~m1_subset_1(X4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.29/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f17,f16,f15])).
% 1.29/0.53  fof(f15,plain,(
% 1.29/0.53    ? [X0,X1] : (? [X2] : (? [X3] : (k9_subset_1(X0,X2,X3) != X1 & ! [X4] : (((r2_hidden(X4,X1) | ~r2_hidden(X4,X3) | ~r2_hidden(X4,X2)) & ((r2_hidden(X4,X3) & r2_hidden(X4,X2)) | ~r2_hidden(X4,X1))) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (? [X3] : (sK1 != k9_subset_1(sK0,X2,X3) & ! [X4] : (((r2_hidden(X4,sK1) | ~r2_hidden(X4,X3) | ~r2_hidden(X4,X2)) & ((r2_hidden(X4,X3) & r2_hidden(X4,X2)) | ~r2_hidden(X4,sK1))) | ~m1_subset_1(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.29/0.53    introduced(choice_axiom,[])).
% 1.29/0.53  fof(f16,plain,(
% 1.29/0.53    ? [X2] : (? [X3] : (sK1 != k9_subset_1(sK0,X2,X3) & ! [X4] : (((r2_hidden(X4,sK1) | ~r2_hidden(X4,X3) | ~r2_hidden(X4,X2)) & ((r2_hidden(X4,X3) & r2_hidden(X4,X2)) | ~r2_hidden(X4,sK1))) | ~m1_subset_1(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (? [X3] : (sK1 != k9_subset_1(sK0,sK2,X3) & ! [X4] : (((r2_hidden(X4,sK1) | ~r2_hidden(X4,X3) | ~r2_hidden(X4,sK2)) & ((r2_hidden(X4,X3) & r2_hidden(X4,sK2)) | ~r2_hidden(X4,sK1))) | ~m1_subset_1(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 1.29/0.53    introduced(choice_axiom,[])).
% 1.29/0.53  fof(f17,plain,(
% 1.29/0.53    ? [X3] : (sK1 != k9_subset_1(sK0,sK2,X3) & ! [X4] : (((r2_hidden(X4,sK1) | ~r2_hidden(X4,X3) | ~r2_hidden(X4,sK2)) & ((r2_hidden(X4,X3) & r2_hidden(X4,sK2)) | ~r2_hidden(X4,sK1))) | ~m1_subset_1(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(sK0))) => (sK1 != k9_subset_1(sK0,sK2,sK3) & ! [X4] : (((r2_hidden(X4,sK1) | ~r2_hidden(X4,sK3) | ~r2_hidden(X4,sK2)) & ((r2_hidden(X4,sK3) & r2_hidden(X4,sK2)) | ~r2_hidden(X4,sK1))) | ~m1_subset_1(X4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(sK0)))),
% 1.29/0.53    introduced(choice_axiom,[])).
% 1.29/0.53  fof(f14,plain,(
% 1.29/0.53    ? [X0,X1] : (? [X2] : (? [X3] : (k9_subset_1(X0,X2,X3) != X1 & ! [X4] : (((r2_hidden(X4,X1) | ~r2_hidden(X4,X3) | ~r2_hidden(X4,X2)) & ((r2_hidden(X4,X3) & r2_hidden(X4,X2)) | ~r2_hidden(X4,X1))) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.29/0.53    inference(flattening,[],[f13])).
% 1.29/0.53  fof(f13,plain,(
% 1.29/0.53    ? [X0,X1] : (? [X2] : (? [X3] : (k9_subset_1(X0,X2,X3) != X1 & ! [X4] : (((r2_hidden(X4,X1) | (~r2_hidden(X4,X3) | ~r2_hidden(X4,X2))) & ((r2_hidden(X4,X3) & r2_hidden(X4,X2)) | ~r2_hidden(X4,X1))) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.29/0.53    inference(nnf_transformation,[],[f9])).
% 1.29/0.53  fof(f9,plain,(
% 1.29/0.53    ? [X0,X1] : (? [X2] : (? [X3] : (k9_subset_1(X0,X2,X3) != X1 & ! [X4] : ((r2_hidden(X4,X1) <=> (r2_hidden(X4,X3) & r2_hidden(X4,X2))) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.29/0.53    inference(flattening,[],[f8])).
% 1.29/0.53  fof(f8,plain,(
% 1.29/0.53    ? [X0,X1] : (? [X2] : (? [X3] : ((k9_subset_1(X0,X2,X3) != X1 & ! [X4] : ((r2_hidden(X4,X1) <=> (r2_hidden(X4,X3) & r2_hidden(X4,X2))) | ~m1_subset_1(X4,X0))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.29/0.53    inference(ennf_transformation,[],[f7])).
% 1.29/0.53  fof(f7,negated_conjecture,(
% 1.29/0.53    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,X1) <=> (r2_hidden(X4,X3) & r2_hidden(X4,X2)))) => k9_subset_1(X0,X2,X3) = X1))))),
% 1.29/0.53    inference(negated_conjecture,[],[f6])).
% 1.29/0.53  fof(f6,conjecture,(
% 1.29/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,X1) <=> (r2_hidden(X4,X3) & r2_hidden(X4,X2)))) => k9_subset_1(X0,X2,X3) = X1))))),
% 1.29/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_subset_1)).
% 1.29/0.53  fof(f72,plain,(
% 1.29/0.53    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) )),
% 1.29/0.53    inference(subsumption_resolution,[],[f39,f36])).
% 1.29/0.53  fof(f36,plain,(
% 1.29/0.53    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f22])).
% 1.29/0.53  fof(f22,plain,(
% 1.29/0.53    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.29/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f21])).
% 1.29/0.53  fof(f21,plain,(
% 1.29/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 1.29/0.53    introduced(choice_axiom,[])).
% 1.29/0.53  fof(f20,plain,(
% 1.29/0.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.29/0.53    inference(rectify,[],[f19])).
% 1.29/0.53  fof(f19,plain,(
% 1.29/0.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.29/0.53    inference(nnf_transformation,[],[f1])).
% 1.29/0.53  fof(f1,axiom,(
% 1.29/0.53    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.29/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.29/0.53  fof(f39,plain,(
% 1.29/0.53    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f23])).
% 1.29/0.53  fof(f23,plain,(
% 1.29/0.53    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.29/0.53    inference(nnf_transformation,[],[f10])).
% 1.29/0.53  fof(f10,plain,(
% 1.29/0.53    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.29/0.53    inference(ennf_transformation,[],[f3])).
% 1.29/0.53  fof(f3,axiom,(
% 1.29/0.53    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.29/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.29/0.53  fof(f237,plain,(
% 1.29/0.53    ~r2_hidden(sK5(sK2,sK3,sK1),sK2) | spl7_2),
% 1.29/0.53    inference(avatar_component_clause,[],[f236])).
% 1.29/0.53  fof(f236,plain,(
% 1.29/0.53    spl7_2 <=> r2_hidden(sK5(sK2,sK3,sK1),sK2)),
% 1.29/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.29/0.53  fof(f234,plain,(
% 1.29/0.53    r2_hidden(sK5(sK2,sK3,sK1),sK1) | ~spl7_1),
% 1.29/0.53    inference(avatar_component_clause,[],[f232])).
% 1.29/0.53  fof(f232,plain,(
% 1.29/0.53    spl7_1 <=> r2_hidden(sK5(sK2,sK3,sK1),sK1)),
% 1.29/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.29/0.53  fof(f29,plain,(
% 1.29/0.53    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.29/0.53    inference(cnf_transformation,[],[f18])).
% 1.29/0.53  fof(f564,plain,(
% 1.29/0.53    ~spl7_1 | ~spl7_2),
% 1.29/0.53    inference(avatar_contradiction_clause,[],[f557])).
% 1.29/0.53  fof(f557,plain,(
% 1.29/0.53    $false | (~spl7_1 | ~spl7_2)),
% 1.29/0.53    inference(unit_resulting_resolution,[],[f29,f234,f555,f42])).
% 1.29/0.53  fof(f555,plain,(
% 1.29/0.53    ~r2_hidden(sK5(sK2,sK3,sK1),sK0) | (~spl7_1 | ~spl7_2)),
% 1.29/0.53    inference(subsumption_resolution,[],[f548,f234])).
% 1.29/0.53  fof(f548,plain,(
% 1.29/0.53    ~r2_hidden(sK5(sK2,sK3,sK1),sK1) | ~r2_hidden(sK5(sK2,sK3,sK1),sK0) | (~spl7_1 | ~spl7_2)),
% 1.29/0.53    inference(resolution,[],[f545,f74])).
% 1.29/0.53  fof(f74,plain,(
% 1.29/0.53    ( ! [X1] : (r2_hidden(X1,sK3) | ~r2_hidden(X1,sK1) | ~r2_hidden(X1,sK0)) )),
% 1.29/0.53    inference(resolution,[],[f72,f33])).
% 1.29/0.53  fof(f33,plain,(
% 1.29/0.53    ( ! [X4] : (~m1_subset_1(X4,sK0) | ~r2_hidden(X4,sK1) | r2_hidden(X4,sK3)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f18])).
% 1.29/0.53  fof(f545,plain,(
% 1.29/0.53    ~r2_hidden(sK5(sK2,sK3,sK1),sK3) | (~spl7_1 | ~spl7_2)),
% 1.29/0.53    inference(subsumption_resolution,[],[f532,f234])).
% 1.29/0.53  fof(f532,plain,(
% 1.29/0.53    ~r2_hidden(sK5(sK2,sK3,sK1),sK3) | ~r2_hidden(sK5(sK2,sK3,sK1),sK1) | ~spl7_2),
% 1.29/0.53    inference(subsumption_resolution,[],[f86,f238])).
% 1.29/0.53  fof(f238,plain,(
% 1.29/0.53    r2_hidden(sK5(sK2,sK3,sK1),sK2) | ~spl7_2),
% 1.29/0.53    inference(avatar_component_clause,[],[f236])).
% 1.29/0.53  fof(f86,plain,(
% 1.29/0.53    ~r2_hidden(sK5(sK2,sK3,sK1),sK3) | ~r2_hidden(sK5(sK2,sK3,sK1),sK2) | ~r2_hidden(sK5(sK2,sK3,sK1),sK1)),
% 1.29/0.53    inference(resolution,[],[f85,f56])).
% 1.29/0.53  fof(f56,plain,(
% 1.29/0.53    ( ! [X2,X0,X1] : (sQ6_eqProxy(k3_xboole_0(X0,X1),X2) | ~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) )),
% 1.29/0.53    inference(equality_proxy_replacement,[],[f49,f53])).
% 1.29/0.53  fof(f53,plain,(
% 1.29/0.53    ! [X1,X0] : (sQ6_eqProxy(X0,X1) <=> X0 = X1)),
% 1.29/0.53    introduced(equality_proxy_definition,[new_symbols(naming,[sQ6_eqProxy])])).
% 1.29/0.53  fof(f49,plain,(
% 1.29/0.53    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f28])).
% 1.29/0.53  fof(f28,plain,(
% 1.29/0.53    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.29/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f27])).
% 1.29/0.53  fof(f27,plain,(
% 1.29/0.53    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.29/0.53    introduced(choice_axiom,[])).
% 1.29/0.53  fof(f26,plain,(
% 1.29/0.53    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.29/0.53    inference(rectify,[],[f25])).
% 1.29/0.53  fof(f25,plain,(
% 1.29/0.53    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.29/0.53    inference(flattening,[],[f24])).
% 1.29/0.53  fof(f24,plain,(
% 1.29/0.53    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.29/0.53    inference(nnf_transformation,[],[f2])).
% 1.29/0.53  fof(f2,axiom,(
% 1.29/0.53    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.29/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.29/0.53  fof(f85,plain,(
% 1.29/0.53    ~sQ6_eqProxy(k3_xboole_0(sK2,sK3),sK1)),
% 1.29/0.53    inference(subsumption_resolution,[],[f81,f31])).
% 1.29/0.53  fof(f31,plain,(
% 1.29/0.53    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 1.29/0.53    inference(cnf_transformation,[],[f18])).
% 1.29/0.53  fof(f81,plain,(
% 1.29/0.53    ~sQ6_eqProxy(k3_xboole_0(sK2,sK3),sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 1.29/0.53    inference(resolution,[],[f77,f55])).
% 1.29/0.53  fof(f55,plain,(
% 1.29/0.53    ( ! [X2,X0,X1] : (sQ6_eqProxy(k9_subset_1(X0,X1,X2),k3_xboole_0(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.29/0.53    inference(equality_proxy_replacement,[],[f43,f53])).
% 1.29/0.53  fof(f43,plain,(
% 1.29/0.53    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.29/0.53    inference(cnf_transformation,[],[f12])).
% 1.29/0.53  fof(f12,plain,(
% 1.29/0.53    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.29/0.53    inference(ennf_transformation,[],[f5])).
% 1.29/0.53  fof(f5,axiom,(
% 1.29/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.29/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.29/0.53  fof(f77,plain,(
% 1.29/0.53    ( ! [X1] : (~sQ6_eqProxy(k9_subset_1(sK0,sK2,sK3),X1) | ~sQ6_eqProxy(X1,sK1)) )),
% 1.29/0.53    inference(resolution,[],[f69,f70])).
% 1.29/0.53  fof(f70,plain,(
% 1.29/0.53    ~sQ6_eqProxy(k9_subset_1(sK0,sK2,sK3),sK1)),
% 1.29/0.53    inference(resolution,[],[f68,f54])).
% 1.29/0.53  fof(f54,plain,(
% 1.29/0.53    ~sQ6_eqProxy(sK1,k9_subset_1(sK0,sK2,sK3))),
% 1.29/0.53    inference(equality_proxy_replacement,[],[f35,f53])).
% 1.29/0.53  fof(f35,plain,(
% 1.29/0.53    sK1 != k9_subset_1(sK0,sK2,sK3)),
% 1.29/0.53    inference(cnf_transformation,[],[f18])).
% 1.29/0.53  fof(f68,plain,(
% 1.29/0.53    ( ! [X0,X1] : (sQ6_eqProxy(X1,X0) | ~sQ6_eqProxy(X0,X1)) )),
% 1.29/0.53    inference(equality_proxy_axiom,[],[f53])).
% 1.29/0.53  fof(f69,plain,(
% 1.29/0.53    ( ! [X2,X0,X1] : (sQ6_eqProxy(X0,X2) | ~sQ6_eqProxy(X1,X2) | ~sQ6_eqProxy(X0,X1)) )),
% 1.29/0.53    inference(equality_proxy_axiom,[],[f53])).
% 1.29/0.53  fof(f529,plain,(
% 1.29/0.53    spl7_1 | ~spl7_2),
% 1.29/0.53    inference(avatar_contradiction_clause,[],[f522])).
% 1.29/0.53  fof(f522,plain,(
% 1.29/0.53    $false | (spl7_1 | ~spl7_2)),
% 1.29/0.53    inference(unit_resulting_resolution,[],[f31,f258,f518,f42])).
% 1.29/0.53  fof(f518,plain,(
% 1.29/0.53    ~r2_hidden(sK5(sK2,sK3,sK1),sK0) | (spl7_1 | ~spl7_2)),
% 1.29/0.53    inference(subsumption_resolution,[],[f517,f238])).
% 1.29/0.53  fof(f517,plain,(
% 1.29/0.53    ~r2_hidden(sK5(sK2,sK3,sK1),sK2) | ~r2_hidden(sK5(sK2,sK3,sK1),sK0) | spl7_1),
% 1.29/0.53    inference(subsumption_resolution,[],[f243,f258])).
% 1.29/0.53  fof(f243,plain,(
% 1.29/0.53    ~r2_hidden(sK5(sK2,sK3,sK1),sK3) | ~r2_hidden(sK5(sK2,sK3,sK1),sK2) | ~r2_hidden(sK5(sK2,sK3,sK1),sK0) | spl7_1),
% 1.29/0.53    inference(resolution,[],[f233,f73])).
% 1.29/0.53  fof(f73,plain,(
% 1.29/0.53    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK3) | ~r2_hidden(X0,sK2) | ~r2_hidden(X0,sK0)) )),
% 1.29/0.53    inference(resolution,[],[f72,f34])).
% 1.29/0.53  fof(f34,plain,(
% 1.29/0.53    ( ! [X4] : (~m1_subset_1(X4,sK0) | ~r2_hidden(X4,sK3) | ~r2_hidden(X4,sK2) | r2_hidden(X4,sK1)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f18])).
% 1.29/0.53  fof(f233,plain,(
% 1.29/0.53    ~r2_hidden(sK5(sK2,sK3,sK1),sK1) | spl7_1),
% 1.29/0.53    inference(avatar_component_clause,[],[f232])).
% 1.29/0.53  fof(f258,plain,(
% 1.29/0.53    r2_hidden(sK5(sK2,sK3,sK1),sK3) | spl7_1),
% 1.29/0.53    inference(subsumption_resolution,[],[f88,f233])).
% 1.29/0.53  fof(f88,plain,(
% 1.29/0.53    r2_hidden(sK5(sK2,sK3,sK1),sK3) | r2_hidden(sK5(sK2,sK3,sK1),sK1)),
% 1.29/0.53    inference(resolution,[],[f85,f57])).
% 1.29/0.53  fof(f57,plain,(
% 1.29/0.53    ( ! [X2,X0,X1] : (sQ6_eqProxy(k3_xboole_0(X0,X1),X2) | r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X2)) )),
% 1.29/0.53    inference(equality_proxy_replacement,[],[f48,f53])).
% 1.29/0.53  fof(f48,plain,(
% 1.29/0.53    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X2)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f28])).
% 1.29/0.53  fof(f239,plain,(
% 1.29/0.53    spl7_1 | spl7_2),
% 1.29/0.53    inference(avatar_split_clause,[],[f87,f236,f232])).
% 1.29/0.53  fof(f87,plain,(
% 1.29/0.53    r2_hidden(sK5(sK2,sK3,sK1),sK2) | r2_hidden(sK5(sK2,sK3,sK1),sK1)),
% 1.29/0.53    inference(resolution,[],[f85,f58])).
% 1.29/0.53  fof(f58,plain,(
% 1.29/0.53    ( ! [X2,X0,X1] : (sQ6_eqProxy(k3_xboole_0(X0,X1),X2) | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2)) )),
% 1.29/0.53    inference(equality_proxy_replacement,[],[f47,f53])).
% 1.29/0.53  fof(f47,plain,(
% 1.29/0.53    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f28])).
% 1.29/0.53  % SZS output end Proof for theBenchmark
% 1.29/0.53  % (2451)------------------------------
% 1.29/0.53  % (2451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % (2451)Termination reason: Refutation
% 1.29/0.53  
% 1.29/0.53  % (2451)Memory used [KB]: 6396
% 1.29/0.53  % (2451)Time elapsed: 0.115 s
% 1.29/0.53  % (2451)------------------------------
% 1.29/0.53  % (2451)------------------------------
% 1.29/0.53  % (2445)Success in time 0.172 s
%------------------------------------------------------------------------------
