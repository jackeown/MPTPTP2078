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
% DateTime   : Thu Dec  3 12:56:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 170 expanded)
%              Number of leaves         :   15 (  52 expanded)
%              Depth                    :   13
%              Number of atoms          :  291 ( 764 expanded)
%              Number of equality atoms :   47 ( 131 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f148,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f137,f147])).

fof(f147,plain,(
    ~ spl12_3 ),
    inference(avatar_contradiction_clause,[],[f146])).

fof(f146,plain,
    ( $false
    | ~ spl12_3 ),
    inference(subsumption_resolution,[],[f143,f33])).

fof(f33,plain,(
    r2_hidden(sK0,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X5,sK2)
        | ~ r2_hidden(X4,sK1)
        | k4_tarski(X4,X5) != sK0 )
    & r2_hidden(sK0,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4,X5] :
            ( ~ r2_hidden(X5,X2)
            | ~ r2_hidden(X4,X1)
            | k4_tarski(X4,X5) != X0 )
        & r2_hidden(X0,X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
   => ( ! [X5,X4] :
          ( ~ r2_hidden(X5,sK2)
          | ~ r2_hidden(X4,sK1)
          | k4_tarski(X4,X5) != sK0 )
      & r2_hidden(sK0,sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4,X5] :
          ( ~ r2_hidden(X5,X2)
          | ~ r2_hidden(X4,X1)
          | k4_tarski(X4,X5) != X0 )
      & r2_hidden(X0,X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4,X5] :
          ( ~ r2_hidden(X5,X2)
          | ~ r2_hidden(X4,X1)
          | k4_tarski(X4,X5) != X0 )
      & r2_hidden(X0,X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
       => ~ ( ! [X4,X5] :
                ~ ( r2_hidden(X5,X2)
                  & r2_hidden(X4,X1)
                  & k4_tarski(X4,X5) = X0 )
            & r2_hidden(X0,X3) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ~ ( ! [X4,X5] :
              ~ ( r2_hidden(X5,X2)
                & r2_hidden(X4,X1)
                & k4_tarski(X4,X5) = X0 )
          & r2_hidden(X0,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_relset_1)).

fof(f143,plain,
    ( ~ r2_hidden(sK0,sK3)
    | ~ spl12_3 ),
    inference(resolution,[],[f136,f58])).

fof(f58,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[],[f39,f32])).

fof(f32,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f136,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,k2_zfmisc_1(sK1,sK2))
        | ~ r2_hidden(sK0,X2) )
    | ~ spl12_3 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl12_3
  <=> ! [X2] :
        ( ~ r2_hidden(sK0,X2)
        | ~ r1_tarski(X2,k2_zfmisc_1(sK1,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f137,plain,
    ( spl12_3
    | spl12_3
    | spl12_3 ),
    inference(avatar_split_clause,[],[f133,f135,f135,f135])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(sK1,sK2))
      | ~ r2_hidden(sK0,X0)
      | ~ r2_hidden(sK0,X1)
      | ~ r1_tarski(X1,k2_zfmisc_1(sK1,sK2))
      | ~ r2_hidden(sK0,X2)
      | ~ r1_tarski(X2,k2_zfmisc_1(sK1,sK2)) ) ),
    inference(subsumption_resolution,[],[f132,f116])).

fof(f116,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(resolution,[],[f99,f60])).

fof(f60,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f59,f56])).

fof(f56,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(resolution,[],[f36,f33])).

fof(f36,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f59,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[],[f35,f32])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f99,plain,(
    ! [X4,X5] :
      ( v1_xboole_0(k2_zfmisc_1(X4,X5))
      | ~ v1_xboole_0(X4) ) ),
    inference(resolution,[],[f70,f37])).

fof(f37,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | ~ v1_xboole_0(X1) ) ),
    inference(resolution,[],[f55,f36])).

fof(f55,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK8(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK8(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK5(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( sK5(X0,X1,X2) = k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2))
              & r2_hidden(sK7(X0,X1,X2),X1)
              & r2_hidden(sK6(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK8(X0,X1,X8),sK9(X0,X1,X8)) = X8
                & r2_hidden(sK9(X0,X1,X8),X1)
                & r2_hidden(sK8(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f24,f27,f26,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != X3
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k4_tarski(X6,X7) = X3
                & r2_hidden(X7,X1)
                & r2_hidden(X6,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k4_tarski(X4,X5) != sK5(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK5(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK5(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK5(X0,X1,X2) = k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2))
        & r2_hidden(sK7(X0,X1,X2),X1)
        & r2_hidden(sK6(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK8(X0,X1,X8),sK9(X0,X1,X8)) = X8
        & r2_hidden(sK9(X0,X1,X8),X1)
        & r2_hidden(sK8(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k4_tarski(X6,X7) = X3
                  & r2_hidden(X7,X1)
                  & r2_hidden(X6,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ? [X11,X12] :
                  ( k4_tarski(X11,X12) = X8
                  & r2_hidden(X12,X1)
                  & r2_hidden(X11,X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) ) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(sK1,sK2))
      | ~ r2_hidden(sK0,X0)
      | ~ r2_hidden(sK0,X1)
      | ~ r1_tarski(X1,k2_zfmisc_1(sK1,sK2))
      | ~ r2_hidden(sK0,X2)
      | v1_xboole_0(sK1)
      | ~ r1_tarski(X2,k2_zfmisc_1(sK1,sK2)) ) ),
    inference(resolution,[],[f127,f74])).

fof(f74,plain,(
    ! [X10,X8,X11,X9] :
      ( r2_hidden(sK10(X9,X10,X11),X9)
      | ~ r2_hidden(X11,X8)
      | v1_xboole_0(X9)
      | ~ r1_tarski(X8,k2_zfmisc_1(X9,X10)) ) ),
    inference(resolution,[],[f48,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK10(X0,X1,X3),X0)
      | ~ r1_tarski(X2,k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X3,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k4_tarski(sK10(X0,X1,X3),sK11(X0,X1,X3)) = X3
        & m1_subset_1(sK11(X0,X1,X3),X1)
        & m1_subset_1(sK10(X0,X1,X3),X0) )
      | ~ r1_tarski(X2,k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X3,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f16,f30,f29])).

fof(f29,plain,(
    ! [X3,X1,X0] :
      ( ? [X4] :
          ( ? [X5] :
              ( k4_tarski(X4,X5) = X3
              & m1_subset_1(X5,X1) )
          & m1_subset_1(X4,X0) )
     => ( ? [X5] :
            ( k4_tarski(sK10(X0,X1,X3),X5) = X3
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK10(X0,X1,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X3,X1,X0] :
      ( ? [X5] :
          ( k4_tarski(sK10(X0,X1,X3),X5) = X3
          & m1_subset_1(X5,X1) )
     => ( k4_tarski(sK10(X0,X1,X3),sK11(X0,X1,X3)) = X3
        & m1_subset_1(sK11(X0,X1,X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ? [X5] :
              ( k4_tarski(X4,X5) = X3
              & m1_subset_1(X5,X1) )
          & m1_subset_1(X4,X0) )
      | ~ r1_tarski(X2,k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X3,X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4] :
            ( m1_subset_1(X4,X0)
           => ! [X5] :
                ( m1_subset_1(X5,X1)
               => k4_tarski(X4,X5) != X3 ) )
        & r1_tarski(X2,k2_zfmisc_1(X0,X1))
        & r2_hidden(X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_subset_1)).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK10(X0,sK2,sK0),sK1)
      | ~ r1_tarski(X1,k2_zfmisc_1(X0,sK2))
      | ~ r2_hidden(sK0,X1)
      | ~ r2_hidden(sK0,X2)
      | ~ r1_tarski(X2,k2_zfmisc_1(X0,sK2)) ) ),
    inference(subsumption_resolution,[],[f126,f84])).

fof(f84,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(resolution,[],[f76,f60])).

fof(f76,plain,(
    ! [X4,X5] :
      ( v1_xboole_0(k2_zfmisc_1(X5,X4))
      | ~ v1_xboole_0(X4) ) ),
    inference(resolution,[],[f69,f37])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(resolution,[],[f54,f36])).

fof(f54,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK9(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK9(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK10(X0,sK2,sK0),sK1)
      | ~ r1_tarski(X1,k2_zfmisc_1(X0,sK2))
      | ~ r2_hidden(sK0,X1)
      | ~ r2_hidden(sK0,X2)
      | v1_xboole_0(sK2)
      | ~ r1_tarski(X2,k2_zfmisc_1(X0,sK2)) ) ),
    inference(resolution,[],[f106,f81])).

fof(f81,plain,(
    ! [X10,X8,X11,X9] :
      ( r2_hidden(sK11(X9,X10,X11),X10)
      | ~ r2_hidden(X11,X8)
      | v1_xboole_0(X10)
      | ~ r1_tarski(X8,k2_zfmisc_1(X9,X10)) ) ),
    inference(resolution,[],[f49,f38])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK11(X0,X1,X3),X1)
      | ~ r1_tarski(X2,k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X3,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK11(X0,X1,sK0),sK2)
      | ~ r2_hidden(sK10(X0,X1,sK0),sK1)
      | ~ r1_tarski(X2,k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(sK0,X2) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X6,X8,X7,X9] :
      ( sK0 != X8
      | ~ r2_hidden(sK10(X6,X7,X8),sK1)
      | ~ r2_hidden(sK11(X6,X7,X8),sK2)
      | ~ r1_tarski(X9,k2_zfmisc_1(X6,X7))
      | ~ r2_hidden(X8,X9) ) ),
    inference(superposition,[],[f34,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(sK10(X0,X1,X3),sK11(X0,X1,X3)) = X3
      | ~ r1_tarski(X2,k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X3,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f34,plain,(
    ! [X4,X5] :
      ( k4_tarski(X4,X5) != sK0
      | ~ r2_hidden(X4,sK1)
      | ~ r2_hidden(X5,sK2) ) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:39:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (20233)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (20223)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.47  % (20224)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.47  % (20232)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (20225)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (20220)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (20239)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.48  % (20222)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (20222)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f148,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f137,f147])).
% 0.21/0.49  fof(f147,plain,(
% 0.21/0.49    ~spl12_3),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f146])).
% 0.21/0.49  fof(f146,plain,(
% 0.21/0.49    $false | ~spl12_3),
% 0.21/0.49    inference(subsumption_resolution,[],[f143,f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    r2_hidden(sK0,sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X4,X5] : (~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK1) | k4_tarski(X4,X5) != sK0) & r2_hidden(sK0,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : (! [X4,X5] : (~r2_hidden(X5,X2) | ~r2_hidden(X4,X1) | k4_tarski(X4,X5) != X0) & r2_hidden(X0,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) => (! [X5,X4] : (~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK1) | k4_tarski(X4,X5) != sK0) & r2_hidden(sK0,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : (! [X4,X5] : (~r2_hidden(X5,X2) | ~r2_hidden(X4,X1) | k4_tarski(X4,X5) != X0) & r2_hidden(X0,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.21/0.49    inference(flattening,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : ((! [X4,X5] : (~r2_hidden(X5,X2) | ~r2_hidden(X4,X1) | k4_tarski(X4,X5) != X0) & r2_hidden(X0,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ~(! [X4,X5] : ~(r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) & r2_hidden(X0,X3)))),
% 0.21/0.49    inference(negated_conjecture,[],[f7])).
% 0.21/0.49  fof(f7,conjecture,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ~(! [X4,X5] : ~(r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) & r2_hidden(X0,X3)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_relset_1)).
% 0.21/0.49  fof(f143,plain,(
% 0.21/0.49    ~r2_hidden(sK0,sK3) | ~spl12_3),
% 0.21/0.49    inference(resolution,[],[f136,f58])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    r1_tarski(sK3,k2_zfmisc_1(sK1,sK2))),
% 0.21/0.49    inference(resolution,[],[f39,f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.21/0.49    inference(unused_predicate_definition_removal,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.49  fof(f136,plain,(
% 0.21/0.49    ( ! [X2] : (~r1_tarski(X2,k2_zfmisc_1(sK1,sK2)) | ~r2_hidden(sK0,X2)) ) | ~spl12_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f135])).
% 0.21/0.49  fof(f135,plain,(
% 0.21/0.49    spl12_3 <=> ! [X2] : (~r2_hidden(sK0,X2) | ~r1_tarski(X2,k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    spl12_3 | spl12_3 | spl12_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f133,f135,f135,f135])).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(sK1,sK2)) | ~r2_hidden(sK0,X0) | ~r2_hidden(sK0,X1) | ~r1_tarski(X1,k2_zfmisc_1(sK1,sK2)) | ~r2_hidden(sK0,X2) | ~r1_tarski(X2,k2_zfmisc_1(sK1,sK2))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f132,f116])).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    ~v1_xboole_0(sK1)),
% 0.21/0.49    inference(resolution,[],[f99,f60])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ~v1_xboole_0(k2_zfmisc_1(sK1,sK2))),
% 0.21/0.49    inference(subsumption_resolution,[],[f59,f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ~v1_xboole_0(sK3)),
% 0.21/0.49    inference(resolution,[],[f36,f33])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.49    inference(rectify,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.49    inference(nnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    v1_xboole_0(sK3) | ~v1_xboole_0(k2_zfmisc_1(sK1,sK2))),
% 0.21/0.49    inference(resolution,[],[f35,f32])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    ( ! [X4,X5] : (v1_xboole_0(k2_zfmisc_1(X4,X5)) | ~v1_xboole_0(X4)) )),
% 0.21/0.49    inference(resolution,[],[f70,f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | ~v1_xboole_0(X1)) )),
% 0.21/0.49    inference(resolution,[],[f55,f36])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X0,X8,X1] : (r2_hidden(sK8(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.49    inference(equality_resolution,[],[f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X2,X0,X8,X1] : (r2_hidden(sK8(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK5(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((sK5(X0,X1,X2) = k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)) & r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK8(X0,X1,X8),sK9(X0,X1,X8)) = X8 & r2_hidden(sK9(X0,X1,X8),X1) & r2_hidden(sK8(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f24,f27,f26,f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK5(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK5(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X2,X1,X0] : (? [X7,X6] : (k4_tarski(X6,X7) = sK5(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (sK5(X0,X1,X2) = k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)) & r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),X0)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK8(X0,X1,X8),sK9(X0,X1,X8)) = X8 & r2_hidden(sK9(X0,X1,X8),X1) & r2_hidden(sK8(X0,X1,X8),X0)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.21/0.49    inference(rectify,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.21/0.49    inference(nnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(sK1,sK2)) | ~r2_hidden(sK0,X0) | ~r2_hidden(sK0,X1) | ~r1_tarski(X1,k2_zfmisc_1(sK1,sK2)) | ~r2_hidden(sK0,X2) | v1_xboole_0(sK1) | ~r1_tarski(X2,k2_zfmisc_1(sK1,sK2))) )),
% 0.21/0.49    inference(resolution,[],[f127,f74])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    ( ! [X10,X8,X11,X9] : (r2_hidden(sK10(X9,X10,X11),X9) | ~r2_hidden(X11,X8) | v1_xboole_0(X9) | ~r1_tarski(X8,k2_zfmisc_1(X9,X10))) )),
% 0.21/0.49    inference(resolution,[],[f48,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK10(X0,X1,X3),X0) | ~r1_tarski(X2,k2_zfmisc_1(X0,X1)) | ~r2_hidden(X3,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (((k4_tarski(sK10(X0,X1,X3),sK11(X0,X1,X3)) = X3 & m1_subset_1(sK11(X0,X1,X3),X1)) & m1_subset_1(sK10(X0,X1,X3),X0)) | ~r1_tarski(X2,k2_zfmisc_1(X0,X1)) | ~r2_hidden(X3,X2))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f16,f30,f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X3,X1,X0] : (? [X4] : (? [X5] : (k4_tarski(X4,X5) = X3 & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0)) => (? [X5] : (k4_tarski(sK10(X0,X1,X3),X5) = X3 & m1_subset_1(X5,X1)) & m1_subset_1(sK10(X0,X1,X3),X0)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X3,X1,X0] : (? [X5] : (k4_tarski(sK10(X0,X1,X3),X5) = X3 & m1_subset_1(X5,X1)) => (k4_tarski(sK10(X0,X1,X3),sK11(X0,X1,X3)) = X3 & m1_subset_1(sK11(X0,X1,X3),X1)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (? [X4] : (? [X5] : (k4_tarski(X4,X5) = X3 & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0)) | ~r1_tarski(X2,k2_zfmisc_1(X0,X1)) | ~r2_hidden(X3,X2))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ~(! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X1) => k4_tarski(X4,X5) != X3)) & r1_tarski(X2,k2_zfmisc_1(X0,X1)) & r2_hidden(X3,X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_subset_1)).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(sK10(X0,sK2,sK0),sK1) | ~r1_tarski(X1,k2_zfmisc_1(X0,sK2)) | ~r2_hidden(sK0,X1) | ~r2_hidden(sK0,X2) | ~r1_tarski(X2,k2_zfmisc_1(X0,sK2))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f126,f84])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    ~v1_xboole_0(sK2)),
% 0.21/0.49    inference(resolution,[],[f76,f60])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    ( ! [X4,X5] : (v1_xboole_0(k2_zfmisc_1(X5,X4)) | ~v1_xboole_0(X4)) )),
% 0.21/0.49    inference(resolution,[],[f69,f37])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | ~v1_xboole_0(X2)) )),
% 0.21/0.49    inference(resolution,[],[f54,f36])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0,X8,X1] : (r2_hidden(sK9(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.49    inference(equality_resolution,[],[f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X2,X0,X8,X1] : (r2_hidden(sK9(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(sK10(X0,sK2,sK0),sK1) | ~r1_tarski(X1,k2_zfmisc_1(X0,sK2)) | ~r2_hidden(sK0,X1) | ~r2_hidden(sK0,X2) | v1_xboole_0(sK2) | ~r1_tarski(X2,k2_zfmisc_1(X0,sK2))) )),
% 0.21/0.49    inference(resolution,[],[f106,f81])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    ( ! [X10,X8,X11,X9] : (r2_hidden(sK11(X9,X10,X11),X10) | ~r2_hidden(X11,X8) | v1_xboole_0(X10) | ~r1_tarski(X8,k2_zfmisc_1(X9,X10))) )),
% 0.21/0.49    inference(resolution,[],[f49,f38])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK11(X0,X1,X3),X1) | ~r1_tarski(X2,k2_zfmisc_1(X0,X1)) | ~r2_hidden(X3,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(sK11(X0,X1,sK0),sK2) | ~r2_hidden(sK10(X0,X1,sK0),sK1) | ~r1_tarski(X2,k2_zfmisc_1(X0,X1)) | ~r2_hidden(sK0,X2)) )),
% 0.21/0.49    inference(equality_resolution,[],[f90])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    ( ! [X6,X8,X7,X9] : (sK0 != X8 | ~r2_hidden(sK10(X6,X7,X8),sK1) | ~r2_hidden(sK11(X6,X7,X8),sK2) | ~r1_tarski(X9,k2_zfmisc_1(X6,X7)) | ~r2_hidden(X8,X9)) )),
% 0.21/0.49    inference(superposition,[],[f34,f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k4_tarski(sK10(X0,X1,X3),sK11(X0,X1,X3)) = X3 | ~r1_tarski(X2,k2_zfmisc_1(X0,X1)) | ~r2_hidden(X3,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X4,X5] : (k4_tarski(X4,X5) != sK0 | ~r2_hidden(X4,sK1) | ~r2_hidden(X5,sK2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (20222)------------------------------
% 0.21/0.49  % (20222)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (20222)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (20222)Memory used [KB]: 10746
% 0.21/0.49  % (20222)Time elapsed: 0.073 s
% 0.21/0.49  % (20222)------------------------------
% 0.21/0.49  % (20222)------------------------------
% 0.21/0.49  % (20219)Success in time 0.134 s
%------------------------------------------------------------------------------
