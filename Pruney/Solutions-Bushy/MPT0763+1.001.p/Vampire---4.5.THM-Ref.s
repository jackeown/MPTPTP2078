%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0763+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:36 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 765 expanded)
%              Number of leaves         :   23 ( 285 expanded)
%              Depth                    :   16
%              Number of atoms          :  528 (4876 expanded)
%              Number of equality atoms :   81 ( 647 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f876,plain,(
    $false ),
    inference(subsumption_resolution,[],[f850,f198])).

fof(f198,plain,(
    r2_hidden(k4_tarski(sK6(sK1,sK2),sK6(sK1,sK2)),sK1) ),
    inference(unit_resulting_resolution,[],[f59,f129,f188,f66])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,X1)
      | ~ r1_relat_2(X0,X1)
      | r2_hidden(k4_tarski(X3,X3),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_relat_2(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK4(X0,X1)),X0)
              & r2_hidden(sK4(X0,X1),X1) ) )
          & ( ! [X3] :
                ( r2_hidden(k4_tarski(X3,X3),X0)
                | ~ r2_hidden(X3,X1) )
            | ~ r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k4_tarski(X2,X2),X0)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK4(X0,X1)),X0)
        & r2_hidden(sK4(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_relat_2(X0,X1)
            | ? [X2] :
                ( ~ r2_hidden(k4_tarski(X2,X2),X0)
                & r2_hidden(X2,X1) ) )
          & ( ! [X3] :
                ( r2_hidden(k4_tarski(X3,X3),X0)
                | ~ r2_hidden(X3,X1) )
            | ~ r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_relat_2(X0,X1)
            | ? [X2] :
                ( ~ r2_hidden(k4_tarski(X2,X2),X0)
                & r2_hidden(X2,X1) ) )
          & ( ! [X2] :
                ( r2_hidden(k4_tarski(X2,X2),X0)
                | ~ r2_hidden(X2,X1) )
            | ~ r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_relat_2(X0,X1)
        <=> ! [X2] :
              ( r2_hidden(k4_tarski(X2,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_relat_2(X0,X1)
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
             => r2_hidden(k4_tarski(X2,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_2)).

fof(f188,plain,(
    r2_hidden(sK6(sK1,sK2),sK0) ),
    inference(unit_resulting_resolution,[],[f149,f178,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f178,plain,(
    m1_subset_1(sK6(sK1,sK2),sK0) ),
    inference(unit_resulting_resolution,[],[f134,f138,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f138,plain,(
    r2_hidden(sK6(sK1,sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f59,f62,f61,f133,f69])).

fof(f69,plain,(
    ! [X4,X0,X1] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = X4
      | ~ r1_tarski(X4,X1)
      | ~ r1_wellord1(X0,X1)
      | r2_hidden(sK6(X0,X4),X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_wellord1(X0,X1)
            | ( ! [X3] :
                  ( ~ r1_xboole_0(k1_wellord1(X0,X3),sK5(X0,X1))
                  | ~ r2_hidden(X3,sK5(X0,X1)) )
              & k1_xboole_0 != sK5(X0,X1)
              & r1_tarski(sK5(X0,X1),X1) ) )
          & ( ! [X4] :
                ( ( r1_xboole_0(k1_wellord1(X0,sK6(X0,X4)),X4)
                  & r2_hidden(sK6(X0,X4),X4) )
                | k1_xboole_0 = X4
                | ~ r1_tarski(X4,X1) )
            | ~ r1_wellord1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f39,f41,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_xboole_0(k1_wellord1(X0,X3),X2)
              | ~ r2_hidden(X3,X2) )
          & k1_xboole_0 != X2
          & r1_tarski(X2,X1) )
     => ( ! [X3] :
            ( ~ r1_xboole_0(k1_wellord1(X0,X3),sK5(X0,X1))
            | ~ r2_hidden(X3,sK5(X0,X1)) )
        & k1_xboole_0 != sK5(X0,X1)
        & r1_tarski(sK5(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X4,X0] :
      ( ? [X5] :
          ( r1_xboole_0(k1_wellord1(X0,X5),X4)
          & r2_hidden(X5,X4) )
     => ( r1_xboole_0(k1_wellord1(X0,sK6(X0,X4)),X4)
        & r2_hidden(sK6(X0,X4),X4) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_wellord1(X0,X1)
            | ? [X2] :
                ( ! [X3] :
                    ( ~ r1_xboole_0(k1_wellord1(X0,X3),X2)
                    | ~ r2_hidden(X3,X2) )
                & k1_xboole_0 != X2
                & r1_tarski(X2,X1) ) )
          & ( ! [X4] :
                ( ? [X5] :
                    ( r1_xboole_0(k1_wellord1(X0,X5),X4)
                    & r2_hidden(X5,X4) )
                | k1_xboole_0 = X4
                | ~ r1_tarski(X4,X1) )
            | ~ r1_wellord1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_wellord1(X0,X1)
            | ? [X2] :
                ( ! [X3] :
                    ( ~ r1_xboole_0(k1_wellord1(X0,X3),X2)
                    | ~ r2_hidden(X3,X2) )
                & k1_xboole_0 != X2
                & r1_tarski(X2,X1) ) )
          & ( ! [X2] :
                ( ? [X3] :
                    ( r1_xboole_0(k1_wellord1(X0,X3),X2)
                    & r2_hidden(X3,X2) )
                | k1_xboole_0 = X2
                | ~ r1_tarski(X2,X1) )
            | ~ r1_wellord1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_wellord1(X0,X1)
        <=> ! [X2] :
              ( ? [X3] :
                  ( r1_xboole_0(k1_wellord1(X0,X3),X2)
                  & r2_hidden(X3,X2) )
              | k1_xboole_0 = X2
              | ~ r1_tarski(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_wellord1(X0,X1)
        <=> ! [X2] :
              ~ ( ! [X3] :
                    ~ ( r1_xboole_0(k1_wellord1(X0,X3),X2)
                      & r2_hidden(X3,X2) )
                & k1_xboole_0 != X2
                & r1_tarski(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_wellord1)).

fof(f133,plain,(
    r1_wellord1(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f59,f60,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_wellord1(X0,X1)
      | r1_wellord1(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_wellord1(X0,X1)
            | ~ r1_wellord1(X0,X1)
            | ~ r6_relat_2(X0,X1)
            | ~ r4_relat_2(X0,X1)
            | ~ r8_relat_2(X0,X1)
            | ~ r1_relat_2(X0,X1) )
          & ( ( r1_wellord1(X0,X1)
              & r6_relat_2(X0,X1)
              & r4_relat_2(X0,X1)
              & r8_relat_2(X0,X1)
              & r1_relat_2(X0,X1) )
            | ~ r2_wellord1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_wellord1(X0,X1)
            | ~ r1_wellord1(X0,X1)
            | ~ r6_relat_2(X0,X1)
            | ~ r4_relat_2(X0,X1)
            | ~ r8_relat_2(X0,X1)
            | ~ r1_relat_2(X0,X1) )
          & ( ( r1_wellord1(X0,X1)
              & r6_relat_2(X0,X1)
              & r4_relat_2(X0,X1)
              & r8_relat_2(X0,X1)
              & r1_relat_2(X0,X1) )
            | ~ r2_wellord1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_wellord1(X0,X1)
        <=> ( r1_wellord1(X0,X1)
            & r6_relat_2(X0,X1)
            & r4_relat_2(X0,X1)
            & r8_relat_2(X0,X1)
            & r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r2_wellord1(X0,X1)
        <=> ( r1_wellord1(X0,X1)
            & r6_relat_2(X0,X1)
            & r4_relat_2(X0,X1)
            & r8_relat_2(X0,X1)
            & r1_relat_2(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_wellord1)).

fof(f60,plain,(
    r2_wellord1(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ! [X3] :
        ( ( ~ r2_hidden(k4_tarski(X3,sK3(X3)),sK1)
          & r2_hidden(sK3(X3),sK2) )
        | ~ r2_hidden(X3,sK2) )
    & k1_xboole_0 != sK2
    & r1_tarski(sK2,sK0)
    & r2_wellord1(sK1,sK0)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f32,f31,f30])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ! [X3] :
                ( ? [X4] :
                    ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    & r2_hidden(X4,X2) )
                | ~ r2_hidden(X3,X2) )
            & k1_xboole_0 != X2
            & r1_tarski(X2,X0) )
        & r2_wellord1(X1,X0)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ! [X3] :
              ( ? [X4] :
                  ( ~ r2_hidden(k4_tarski(X3,X4),sK1)
                  & r2_hidden(X4,X2) )
              | ~ r2_hidden(X3,X2) )
          & k1_xboole_0 != X2
          & r1_tarski(X2,sK0) )
      & r2_wellord1(sK1,sK0)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X2] :
        ( ! [X3] :
            ( ? [X4] :
                ( ~ r2_hidden(k4_tarski(X3,X4),sK1)
                & r2_hidden(X4,X2) )
            | ~ r2_hidden(X3,X2) )
        & k1_xboole_0 != X2
        & r1_tarski(X2,sK0) )
   => ( ! [X3] :
          ( ? [X4] :
              ( ~ r2_hidden(k4_tarski(X3,X4),sK1)
              & r2_hidden(X4,sK2) )
          | ~ r2_hidden(X3,sK2) )
      & k1_xboole_0 != sK2
      & r1_tarski(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X3] :
      ( ? [X4] :
          ( ~ r2_hidden(k4_tarski(X3,X4),sK1)
          & r2_hidden(X4,sK2) )
     => ( ~ r2_hidden(k4_tarski(X3,sK3(X3)),sK1)
        & r2_hidden(sK3(X3),sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ? [X4] :
                  ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X2) )
              | ~ r2_hidden(X3,X2) )
          & k1_xboole_0 != X2
          & r1_tarski(X2,X0) )
      & r2_wellord1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ? [X4] :
                  ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X2) )
              | ~ r2_hidden(X3,X2) )
          & k1_xboole_0 != X2
          & r1_tarski(X2,X0) )
      & r2_wellord1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_wellord1(X1,X0)
         => ! [X2] :
              ~ ( ! [X3] :
                    ~ ( ! [X4] :
                          ( r2_hidden(X4,X2)
                         => r2_hidden(k4_tarski(X3,X4),X1) )
                      & r2_hidden(X3,X2) )
                & k1_xboole_0 != X2
                & r1_tarski(X2,X0) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_wellord1(X1,X0)
       => ! [X2] :
            ~ ( ! [X3] :
                  ~ ( ! [X4] :
                        ( r2_hidden(X4,X2)
                       => r2_hidden(k4_tarski(X3,X4),X1) )
                    & r2_hidden(X3,X2) )
              & k1_xboole_0 != X2
              & r1_tarski(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_wellord1)).

fof(f61,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f62,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f33])).

fof(f134,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f61,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f149,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(unit_resulting_resolution,[],[f134,f136,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f136,plain,(
    r2_hidden(sK10(sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f92,f135,f96])).

fof(f135,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(unit_resulting_resolution,[],[f62,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f92,plain,(
    ! [X0] : m1_subset_1(sK10(X0),X0) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] : m1_subset_1(sK10(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f6,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK10(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f6,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f129,plain,(
    r1_relat_2(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f59,f60,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_wellord1(X0,X1)
      | r1_relat_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f59,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f850,plain,(
    ~ r2_hidden(k4_tarski(sK6(sK1,sK2),sK6(sK1,sK2)),sK1) ),
    inference(backward_demodulation,[],[f174,f849])).

fof(f849,plain,(
    sK6(sK1,sK2) = sK3(sK6(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f848,f383])).

fof(f383,plain,(
    ~ r2_hidden(sK3(sK6(sK1,sK2)),k1_wellord1(sK1,sK6(sK1,sK2))) ),
    inference(unit_resulting_resolution,[],[f175,f139,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK11(X0,X1),X1)
          & r2_hidden(sK11(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f24,f56])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK11(X0,X1),X1)
        & r2_hidden(sK11(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f139,plain,(
    r1_xboole_0(k1_wellord1(sK1,sK6(sK1,sK2)),sK2) ),
    inference(unit_resulting_resolution,[],[f59,f62,f61,f133,f70])).

fof(f70,plain,(
    ! [X4,X0,X1] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = X4
      | ~ r1_tarski(X4,X1)
      | ~ r1_wellord1(X0,X1)
      | r1_xboole_0(k1_wellord1(X0,sK6(X0,X4)),X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f175,plain,(
    r2_hidden(sK3(sK6(sK1,sK2)),sK2) ),
    inference(unit_resulting_resolution,[],[f138,f63])).

fof(f63,plain,(
    ! [X3] :
      ( r2_hidden(sK3(X3),sK2)
      | ~ r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f848,plain,
    ( sK6(sK1,sK2) = sK3(sK6(sK1,sK2))
    | r2_hidden(sK3(sK6(sK1,sK2)),k1_wellord1(sK1,sK6(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f847,f272])).

fof(f272,plain,(
    r2_hidden(sK3(sK6(sK1,sK2)),sK0) ),
    inference(unit_resulting_resolution,[],[f175,f262])).

fof(f262,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | r2_hidden(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f261,f149])).

fof(f261,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | v1_xboole_0(sK0)
      | r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f141,f96])).

fof(f141,plain,(
    ! [X0] :
      ( m1_subset_1(X0,sK0)
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f134,f99])).

fof(f847,plain,
    ( ~ r2_hidden(sK3(sK6(sK1,sK2)),sK0)
    | sK6(sK1,sK2) = sK3(sK6(sK1,sK2))
    | r2_hidden(sK3(sK6(sK1,sK2)),k1_wellord1(sK1,sK6(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f837,f188])).

fof(f837,plain,
    ( ~ r2_hidden(sK6(sK1,sK2),sK0)
    | ~ r2_hidden(sK3(sK6(sK1,sK2)),sK0)
    | sK6(sK1,sK2) = sK3(sK6(sK1,sK2))
    | r2_hidden(sK3(sK6(sK1,sK2)),k1_wellord1(sK1,sK6(sK1,sK2))) ),
    inference(resolution,[],[f585,f174])).

fof(f585,plain,(
    ! [X2,X1] :
      ( r2_hidden(k4_tarski(X2,X1),sK1)
      | ~ r2_hidden(X2,sK0)
      | ~ r2_hidden(X1,sK0)
      | X1 = X2
      | r2_hidden(X1,k1_wellord1(sK1,X2)) ) ),
    inference(duplicate_literal_removal,[],[f569])).

fof(f569,plain,(
    ! [X2,X1] :
      ( r2_hidden(k4_tarski(X2,X1),sK1)
      | ~ r2_hidden(X2,sK0)
      | ~ r2_hidden(X1,sK0)
      | X1 = X2
      | X1 = X2
      | r2_hidden(X1,k1_wellord1(sK1,X2)) ) ),
    inference(resolution,[],[f380,f126])).

fof(f126,plain,(
    ! [X28,X29] :
      ( ~ r2_hidden(k4_tarski(X28,X29),sK1)
      | X28 = X29
      | r2_hidden(X28,k1_wellord1(sK1,X29)) ) ),
    inference(resolution,[],[f59,f101])).

fof(f101,plain,(
    ! [X4,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | r2_hidden(X4,k1_wellord1(X0,X1)) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ( ( ~ r2_hidden(k4_tarski(sK9(X0,X1,X2),X1),X0)
                | sK9(X0,X1,X2) = X1
                | ~ r2_hidden(sK9(X0,X1,X2),X2) )
              & ( ( r2_hidden(k4_tarski(sK9(X0,X1,X2),X1),X0)
                  & sK9(X0,X1,X2) != X1 )
                | r2_hidden(sK9(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f51,f52])).

fof(f52,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            | X1 = X3
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k4_tarski(X3,X1),X0)
              & X1 != X3 )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK9(X0,X1,X2),X1),X0)
          | sK9(X0,X1,X2) = X1
          | ~ r2_hidden(sK9(X0,X1,X2),X2) )
        & ( ( r2_hidden(k4_tarski(sK9(X0,X1,X2),X1),X0)
            & sK9(X0,X1,X2) != X1 )
          | r2_hidden(sK9(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).

fof(f380,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,X0),sK1)
      | r2_hidden(k4_tarski(X0,X1),sK1)
      | ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X1,sK0)
      | X0 = X1 ) ),
    inference(resolution,[],[f112,f132])).

fof(f132,plain,(
    r6_relat_2(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f59,f60,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_wellord1(X0,X1)
      | r6_relat_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f112,plain,(
    ! [X10,X11,X9] :
      ( ~ r6_relat_2(sK1,X11)
      | X9 = X10
      | ~ r2_hidden(X10,X11)
      | ~ r2_hidden(X9,X11)
      | r2_hidden(k4_tarski(X9,X10),sK1)
      | r2_hidden(k4_tarski(X10,X9),sK1) ) ),
    inference(resolution,[],[f59,f74])).

fof(f74,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X4,X5),X0)
      | X4 = X5
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ r6_relat_2(X0,X1)
      | r2_hidden(k4_tarski(X5,X4),X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r6_relat_2(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0)
              & ~ r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0)
              & sK7(X0,X1) != sK8(X0,X1)
              & r2_hidden(sK8(X0,X1),X1)
              & r2_hidden(sK7(X0,X1),X1) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X5,X4),X0)
                | r2_hidden(k4_tarski(X4,X5),X0)
                | X4 = X5
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X1) )
            | ~ r6_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f44,f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X3,X2),X0)
          & ~ r2_hidden(k4_tarski(X2,X3),X0)
          & X2 != X3
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0)
        & ~ r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0)
        & sK7(X0,X1) != sK8(X0,X1)
        & r2_hidden(sK8(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r6_relat_2(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                & ~ r2_hidden(k4_tarski(X2,X3),X0)
                & X2 != X3
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X5,X4),X0)
                | r2_hidden(k4_tarski(X4,X5),X0)
                | X4 = X5
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X1) )
            | ~ r6_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r6_relat_2(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                & ~ r2_hidden(k4_tarski(X2,X3),X0)
                & X2 != X3
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X3,X2),X0)
                | r2_hidden(k4_tarski(X2,X3),X0)
                | X2 = X3
                | ~ r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X1) )
            | ~ r6_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r6_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(k4_tarski(X2,X3),X0)
              | X2 = X3
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r6_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ~ ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                & ~ r2_hidden(k4_tarski(X2,X3),X0)
                & X2 != X3
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_2)).

fof(f174,plain,(
    ~ r2_hidden(k4_tarski(sK6(sK1,sK2),sK3(sK6(sK1,sK2))),sK1) ),
    inference(unit_resulting_resolution,[],[f138,f64])).

fof(f64,plain,(
    ! [X3] :
      ( ~ r2_hidden(k4_tarski(X3,sK3(X3)),sK1)
      | ~ r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f33])).

%------------------------------------------------------------------------------
