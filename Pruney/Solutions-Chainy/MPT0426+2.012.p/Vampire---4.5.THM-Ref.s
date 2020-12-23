%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:32 EST 2020

% Result     : Theorem 1.83s
% Output     : Refutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 256 expanded)
%              Number of leaves         :   24 (  78 expanded)
%              Depth                    :   13
%              Number of atoms          :  395 (1095 expanded)
%              Number of equality atoms :   69 ( 147 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f995,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f101,f106,f110,f198,f681,f706,f710,f860,f946,f994])).

fof(f994,plain,(
    ~ spl8_10 ),
    inference(avatar_contradiction_clause,[],[f974])).

fof(f974,plain,
    ( $false
    | ~ spl8_10 ),
    inference(unit_resulting_resolution,[],[f90,f855])).

fof(f855,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_tarski(sK3))
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f854])).

fof(f854,plain,
    ( spl8_10
  <=> ! [X0] : ~ r2_hidden(X0,k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f90,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK7(X0,X1) != X0
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( sK7(X0,X1) = X0
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f47,f48])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK7(X0,X1) != X0
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( sK7(X0,X1) = X0
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f946,plain,(
    spl8_11 ),
    inference(avatar_contradiction_clause,[],[f945])).

fof(f945,plain,
    ( $false
    | spl8_11 ),
    inference(subsumption_resolution,[],[f940,f941])).

fof(f941,plain,
    ( ~ r2_hidden(sK6(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | spl8_11 ),
    inference(unit_resulting_resolution,[],[f859,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f43,f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f859,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl8_11 ),
    inference(avatar_component_clause,[],[f857])).

fof(f857,plain,
    ( spl8_11
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f940,plain,
    ( r2_hidden(sK6(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | spl8_11 ),
    inference(unit_resulting_resolution,[],[f859,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK6(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f860,plain,
    ( spl8_10
    | ~ spl8_11
    | ~ spl8_3
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f852,f161,f103,f857,f854])).

fof(f103,plain,
    ( spl8_3
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f161,plain,
    ( spl8_7
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f852,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
        | ~ r2_hidden(X0,k1_tarski(sK3)) )
    | ~ spl8_3
    | ~ spl8_7 ),
    inference(superposition,[],[f750,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

fof(f750,plain,
    ( ! [X0] : ~ r1_tarski(k1_xboole_0,k4_xboole_0(X0,k1_tarski(sK3)))
    | ~ spl8_3
    | ~ spl8_7 ),
    inference(backward_demodulation,[],[f693,f163])).

fof(f163,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f161])).

fof(f693,plain,
    ( ! [X0] : ~ r1_tarski(sK2,k4_xboole_0(X0,k1_tarski(sK3)))
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f92,f105,f73])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f105,plain,
    ( r2_hidden(sK3,sK2)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f103])).

fof(f92,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2))) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f710,plain,
    ( spl8_7
    | spl8_8 ),
    inference(avatar_split_clause,[],[f709,f165,f161])).

fof(f165,plain,
    ( spl8_8
  <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f709,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f235,f54])).

fof(f54,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ( ( ~ r2_hidden(sK1,sK3)
        & r2_hidden(sK3,sK2) )
      | ~ r2_hidden(sK1,k8_setfam_1(sK0,sK2)) )
    & ( ! [X4] :
          ( r2_hidden(sK1,X4)
          | ~ r2_hidden(X4,sK2) )
      | r2_hidden(sK1,k8_setfam_1(sK0,sK2)) )
    & r2_hidden(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f31,f33,f32])).

fof(f32,plain,
    ( ? [X0,X1,X2] :
        ( ( ? [X3] :
              ( ~ r2_hidden(X1,X3)
              & r2_hidden(X3,X2) )
          | ~ r2_hidden(X1,k8_setfam_1(X0,X2)) )
        & ( ! [X4] :
              ( r2_hidden(X1,X4)
              | ~ r2_hidden(X4,X2) )
          | r2_hidden(X1,k8_setfam_1(X0,X2)) )
        & r2_hidden(X1,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ( ? [X3] :
            ( ~ r2_hidden(sK1,X3)
            & r2_hidden(X3,sK2) )
        | ~ r2_hidden(sK1,k8_setfam_1(sK0,sK2)) )
      & ( ! [X4] :
            ( r2_hidden(sK1,X4)
            | ~ r2_hidden(X4,sK2) )
        | r2_hidden(sK1,k8_setfam_1(sK0,sK2)) )
      & r2_hidden(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X3] :
        ( ~ r2_hidden(sK1,X3)
        & r2_hidden(X3,sK2) )
   => ( ~ r2_hidden(sK1,sK3)
      & r2_hidden(sK3,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( ( ? [X3] :
            ( ~ r2_hidden(X1,X3)
            & r2_hidden(X3,X2) )
        | ~ r2_hidden(X1,k8_setfam_1(X0,X2)) )
      & ( ! [X4] :
            ( r2_hidden(X1,X4)
            | ~ r2_hidden(X4,X2) )
        | r2_hidden(X1,k8_setfam_1(X0,X2)) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( ( ? [X3] :
            ( ~ r2_hidden(X1,X3)
            & r2_hidden(X3,X2) )
        | ~ r2_hidden(X1,k8_setfam_1(X0,X2)) )
      & ( ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) )
        | r2_hidden(X1,k8_setfam_1(X0,X2)) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ( ? [X3] :
            ( ~ r2_hidden(X1,X3)
            & r2_hidden(X3,X2) )
        | ~ r2_hidden(X1,k8_setfam_1(X0,X2)) )
      & ( ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) )
        | r2_hidden(X1,k8_setfam_1(X0,X2)) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,k8_setfam_1(X0,X2))
      <~> ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) ) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,k8_setfam_1(X0,X2))
      <~> ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) ) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( r2_hidden(X1,X0)
         => ( r2_hidden(X1,k8_setfam_1(X0,X2))
          <=> ! [X3] :
                ( r2_hidden(X3,X2)
               => r2_hidden(X1,X3) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( r2_hidden(X1,X0)
       => ( r2_hidden(X1,k8_setfam_1(X0,X2))
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
             => r2_hidden(X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_setfam_1)).

fof(f235,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(superposition,[],[f119,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f119,plain,(
    k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    inference(unit_resulting_resolution,[],[f54,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f706,plain,
    ( ~ spl8_1
    | spl8_2
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(avatar_contradiction_clause,[],[f705])).

fof(f705,plain,
    ( $false
    | ~ spl8_1
    | spl8_2
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f700,f692])).

fof(f692,plain,
    ( r1_tarski(k1_setfam_1(sK2),sK3)
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f105,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f700,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),sK3)
    | ~ spl8_1
    | spl8_2
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f100,f682,f73])).

fof(f682,plain,
    ( r2_hidden(sK1,k1_setfam_1(sK2))
    | ~ spl8_1
    | ~ spl8_8 ),
    inference(forward_demodulation,[],[f95,f167])).

fof(f167,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f165])).

fof(f95,plain,
    ( r2_hidden(sK1,k8_setfam_1(sK0,sK2))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl8_1
  <=> r2_hidden(sK1,k8_setfam_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f100,plain,
    ( ~ r2_hidden(sK1,sK3)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl8_2
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f681,plain,
    ( spl8_1
    | ~ spl8_4
    | spl8_7
    | ~ spl8_8 ),
    inference(avatar_contradiction_clause,[],[f680])).

fof(f680,plain,
    ( $false
    | spl8_1
    | ~ spl8_4
    | spl8_7
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f675,f631])).

fof(f631,plain,
    ( r2_hidden(sK1,sK5(sK2,k1_tarski(sK1)))
    | spl8_1
    | ~ spl8_4
    | spl8_7
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f267,f109])).

fof(f109,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK2)
        | r2_hidden(sK1,X4) )
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl8_4
  <=> ! [X4] :
        ( r2_hidden(sK1,X4)
        | ~ r2_hidden(X4,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f267,plain,
    ( r2_hidden(sK5(sK2,k1_tarski(sK1)),sK2)
    | spl8_1
    | spl8_7
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f203,f162,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ( ~ r1_tarski(X1,sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f25,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(X1,sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).

fof(f162,plain,
    ( k1_xboole_0 != sK2
    | spl8_7 ),
    inference(avatar_component_clause,[],[f161])).

fof(f203,plain,
    ( ~ r1_tarski(k1_tarski(sK1),k1_setfam_1(sK2))
    | spl8_1
    | ~ spl8_8 ),
    inference(backward_demodulation,[],[f125,f167])).

fof(f125,plain,
    ( ~ r1_tarski(k1_tarski(sK1),k8_setfam_1(sK0,sK2))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f90,f96,f73])).

fof(f96,plain,
    ( ~ r2_hidden(sK1,k8_setfam_1(sK0,sK2))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f94])).

fof(f675,plain,
    ( ~ r2_hidden(sK1,sK5(sK2,k1_tarski(sK1)))
    | spl8_1
    | spl8_7
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f269,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).

fof(f269,plain,
    ( ~ r1_tarski(k1_tarski(sK1),sK5(sK2,k1_tarski(sK1)))
    | spl8_1
    | spl8_7
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f203,f162,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X1,sK5(X0,X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f198,plain,
    ( spl8_1
    | ~ spl8_7 ),
    inference(avatar_contradiction_clause,[],[f197])).

fof(f197,plain,
    ( $false
    | spl8_1
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f196,f59])).

fof(f59,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f196,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl8_1
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f195,f55])).

fof(f55,plain,(
    r2_hidden(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f195,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl8_1
    | ~ spl8_7 ),
    inference(superposition,[],[f172,f88])).

fof(f88,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f172,plain,
    ( ~ r2_hidden(sK1,k8_setfam_1(sK0,k1_xboole_0))
    | spl8_1
    | ~ spl8_7 ),
    inference(backward_demodulation,[],[f96,f163])).

fof(f110,plain,
    ( spl8_1
    | spl8_4 ),
    inference(avatar_split_clause,[],[f56,f108,f94])).

fof(f56,plain,(
    ! [X4] :
      ( r2_hidden(sK1,X4)
      | ~ r2_hidden(X4,sK2)
      | r2_hidden(sK1,k8_setfam_1(sK0,sK2)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f106,plain,
    ( ~ spl8_1
    | spl8_3 ),
    inference(avatar_split_clause,[],[f57,f103,f94])).

fof(f57,plain,
    ( r2_hidden(sK3,sK2)
    | ~ r2_hidden(sK1,k8_setfam_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f34])).

fof(f101,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f58,f98,f94])).

fof(f58,plain,
    ( ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(sK1,k8_setfam_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:34:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (7461)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.50  % (7453)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (7439)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (7447)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (7462)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.51  % (7447)Refutation not found, incomplete strategy% (7447)------------------------------
% 0.20/0.51  % (7447)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (7447)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (7447)Memory used [KB]: 10746
% 0.20/0.51  % (7447)Time elapsed: 0.102 s
% 0.20/0.51  % (7447)------------------------------
% 0.20/0.51  % (7447)------------------------------
% 0.20/0.51  % (7446)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (7455)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.52  % (7455)Refutation not found, incomplete strategy% (7455)------------------------------
% 0.20/0.52  % (7455)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (7455)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (7455)Memory used [KB]: 10618
% 0.20/0.52  % (7455)Time elapsed: 0.117 s
% 0.20/0.52  % (7455)------------------------------
% 0.20/0.52  % (7455)------------------------------
% 0.20/0.52  % (7444)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (7440)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (7440)Refutation not found, incomplete strategy% (7440)------------------------------
% 0.20/0.53  % (7440)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (7440)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (7440)Memory used [KB]: 10874
% 0.20/0.53  % (7440)Time elapsed: 0.127 s
% 0.20/0.53  % (7440)------------------------------
% 0.20/0.53  % (7440)------------------------------
% 0.20/0.54  % (7464)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (7445)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (7441)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (7456)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (7443)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.54  % (7442)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.55  % (7452)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.55  % (7451)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  % (7448)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.55  % (7448)Refutation not found, incomplete strategy% (7448)------------------------------
% 0.20/0.55  % (7448)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (7448)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (7448)Memory used [KB]: 10618
% 0.20/0.55  % (7448)Time elapsed: 0.150 s
% 0.20/0.55  % (7448)------------------------------
% 0.20/0.55  % (7448)------------------------------
% 0.20/0.55  % (7467)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.55  % (7438)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.55  % (7460)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.56  % (7449)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.56  % (7460)Refutation not found, incomplete strategy% (7460)------------------------------
% 0.20/0.56  % (7460)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (7460)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (7460)Memory used [KB]: 10874
% 0.20/0.56  % (7460)Time elapsed: 0.141 s
% 0.20/0.56  % (7460)------------------------------
% 0.20/0.56  % (7460)------------------------------
% 0.20/0.56  % (7458)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.56  % (7459)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.57  % (7465)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.57  % (7457)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.57  % (7450)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.58  % (7466)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.58  % (7463)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.59  % (7454)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.83/0.60  % (7469)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 1.83/0.61  % (7464)Refutation found. Thanks to Tanya!
% 1.83/0.61  % SZS status Theorem for theBenchmark
% 1.94/0.62  % SZS output start Proof for theBenchmark
% 1.94/0.62  fof(f995,plain,(
% 1.94/0.62    $false),
% 1.94/0.62    inference(avatar_sat_refutation,[],[f101,f106,f110,f198,f681,f706,f710,f860,f946,f994])).
% 1.94/0.62  fof(f994,plain,(
% 1.94/0.62    ~spl8_10),
% 1.94/0.62    inference(avatar_contradiction_clause,[],[f974])).
% 1.94/0.62  fof(f974,plain,(
% 1.94/0.62    $false | ~spl8_10),
% 1.94/0.62    inference(unit_resulting_resolution,[],[f90,f855])).
% 1.94/0.62  fof(f855,plain,(
% 1.94/0.62    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK3))) ) | ~spl8_10),
% 1.94/0.62    inference(avatar_component_clause,[],[f854])).
% 1.94/0.62  fof(f854,plain,(
% 1.94/0.62    spl8_10 <=> ! [X0] : ~r2_hidden(X0,k1_tarski(sK3))),
% 1.94/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 1.94/0.62  fof(f90,plain,(
% 1.94/0.62    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 1.94/0.62    inference(equality_resolution,[],[f89])).
% 1.94/0.62  fof(f89,plain,(
% 1.94/0.62    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 1.94/0.62    inference(equality_resolution,[],[f77])).
% 1.94/0.62  fof(f77,plain,(
% 1.94/0.62    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.94/0.62    inference(cnf_transformation,[],[f49])).
% 1.94/0.62  fof(f49,plain,(
% 1.94/0.62    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK7(X0,X1) != X0 | ~r2_hidden(sK7(X0,X1),X1)) & (sK7(X0,X1) = X0 | r2_hidden(sK7(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.94/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f47,f48])).
% 1.94/0.62  fof(f48,plain,(
% 1.94/0.62    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK7(X0,X1) != X0 | ~r2_hidden(sK7(X0,X1),X1)) & (sK7(X0,X1) = X0 | r2_hidden(sK7(X0,X1),X1))))),
% 1.94/0.62    introduced(choice_axiom,[])).
% 1.94/0.62  fof(f47,plain,(
% 1.94/0.62    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.94/0.62    inference(rectify,[],[f46])).
% 1.94/0.62  fof(f46,plain,(
% 1.94/0.62    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.94/0.62    inference(nnf_transformation,[],[f3])).
% 1.94/0.62  fof(f3,axiom,(
% 1.94/0.62    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.94/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.94/0.62  fof(f946,plain,(
% 1.94/0.62    spl8_11),
% 1.94/0.62    inference(avatar_contradiction_clause,[],[f945])).
% 1.94/0.62  fof(f945,plain,(
% 1.94/0.62    $false | spl8_11),
% 1.94/0.62    inference(subsumption_resolution,[],[f940,f941])).
% 1.94/0.62  fof(f941,plain,(
% 1.94/0.62    ~r2_hidden(sK6(k1_xboole_0,k1_xboole_0),k1_xboole_0) | spl8_11),
% 1.94/0.62    inference(unit_resulting_resolution,[],[f859,f75])).
% 1.94/0.62  fof(f75,plain,(
% 1.94/0.62    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK6(X0,X1),X1)) )),
% 1.94/0.62    inference(cnf_transformation,[],[f45])).
% 1.94/0.62  fof(f45,plain,(
% 1.94/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.94/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f43,f44])).
% 1.94/0.62  fof(f44,plain,(
% 1.94/0.62    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 1.94/0.62    introduced(choice_axiom,[])).
% 1.94/0.62  fof(f43,plain,(
% 1.94/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.94/0.62    inference(rectify,[],[f42])).
% 1.94/0.62  fof(f42,plain,(
% 1.94/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.94/0.62    inference(nnf_transformation,[],[f26])).
% 1.94/0.62  fof(f26,plain,(
% 1.94/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.94/0.62    inference(ennf_transformation,[],[f2])).
% 1.94/0.62  fof(f2,axiom,(
% 1.94/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.94/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.94/0.62  fof(f859,plain,(
% 1.94/0.62    ~r1_tarski(k1_xboole_0,k1_xboole_0) | spl8_11),
% 1.94/0.62    inference(avatar_component_clause,[],[f857])).
% 1.94/0.62  fof(f857,plain,(
% 1.94/0.62    spl8_11 <=> r1_tarski(k1_xboole_0,k1_xboole_0)),
% 1.94/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 1.94/0.62  fof(f940,plain,(
% 1.94/0.62    r2_hidden(sK6(k1_xboole_0,k1_xboole_0),k1_xboole_0) | spl8_11),
% 1.94/0.62    inference(unit_resulting_resolution,[],[f859,f74])).
% 1.94/0.62  fof(f74,plain,(
% 1.94/0.62    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK6(X0,X1),X0)) )),
% 1.94/0.62    inference(cnf_transformation,[],[f45])).
% 1.94/0.62  fof(f860,plain,(
% 1.94/0.62    spl8_10 | ~spl8_11 | ~spl8_3 | ~spl8_7),
% 1.94/0.62    inference(avatar_split_clause,[],[f852,f161,f103,f857,f854])).
% 1.94/0.62  fof(f103,plain,(
% 1.94/0.62    spl8_3 <=> r2_hidden(sK3,sK2)),
% 1.94/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.94/0.62  fof(f161,plain,(
% 1.94/0.62    spl8_7 <=> k1_xboole_0 = sK2),
% 1.94/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 1.94/0.62  fof(f852,plain,(
% 1.94/0.62    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_xboole_0) | ~r2_hidden(X0,k1_tarski(sK3))) ) | (~spl8_3 | ~spl8_7)),
% 1.94/0.62    inference(superposition,[],[f750,f83])).
% 1.94/0.62  fof(f83,plain,(
% 1.94/0.62    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 | ~r2_hidden(X0,X1)) )),
% 1.94/0.62    inference(cnf_transformation,[],[f51])).
% 1.94/0.62  fof(f51,plain,(
% 1.94/0.62    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0))),
% 1.94/0.62    inference(nnf_transformation,[],[f4])).
% 1.94/0.62  fof(f4,axiom,(
% 1.94/0.62    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 <=> r2_hidden(X0,X1))),
% 1.94/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).
% 1.94/0.62  fof(f750,plain,(
% 1.94/0.62    ( ! [X0] : (~r1_tarski(k1_xboole_0,k4_xboole_0(X0,k1_tarski(sK3)))) ) | (~spl8_3 | ~spl8_7)),
% 1.94/0.62    inference(backward_demodulation,[],[f693,f163])).
% 1.94/0.62  fof(f163,plain,(
% 1.94/0.62    k1_xboole_0 = sK2 | ~spl8_7),
% 1.94/0.62    inference(avatar_component_clause,[],[f161])).
% 1.94/0.62  fof(f693,plain,(
% 1.94/0.62    ( ! [X0] : (~r1_tarski(sK2,k4_xboole_0(X0,k1_tarski(sK3)))) ) | ~spl8_3),
% 1.94/0.62    inference(unit_resulting_resolution,[],[f92,f105,f73])).
% 1.94/0.62  fof(f73,plain,(
% 1.94/0.62    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.94/0.62    inference(cnf_transformation,[],[f45])).
% 1.94/0.62  fof(f105,plain,(
% 1.94/0.62    r2_hidden(sK3,sK2) | ~spl8_3),
% 1.94/0.62    inference(avatar_component_clause,[],[f103])).
% 1.94/0.62  fof(f92,plain,(
% 1.94/0.62    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 1.94/0.62    inference(equality_resolution,[],[f86])).
% 1.94/0.62  fof(f86,plain,(
% 1.94/0.62    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 1.94/0.62    inference(cnf_transformation,[],[f53])).
% 1.94/0.62  fof(f53,plain,(
% 1.94/0.62    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 1.94/0.62    inference(flattening,[],[f52])).
% 1.94/0.62  fof(f52,plain,(
% 1.94/0.62    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 1.94/0.62    inference(nnf_transformation,[],[f6])).
% 1.94/0.62  fof(f6,axiom,(
% 1.94/0.62    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 1.94/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 1.94/0.62  fof(f710,plain,(
% 1.94/0.62    spl8_7 | spl8_8),
% 1.94/0.62    inference(avatar_split_clause,[],[f709,f165,f161])).
% 1.94/0.62  fof(f165,plain,(
% 1.94/0.62    spl8_8 <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 1.94/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 1.94/0.62  fof(f709,plain,(
% 1.94/0.62    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | k1_xboole_0 = sK2),
% 1.94/0.62    inference(subsumption_resolution,[],[f235,f54])).
% 1.94/0.62  fof(f54,plain,(
% 1.94/0.62    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.94/0.62    inference(cnf_transformation,[],[f34])).
% 1.94/0.62  fof(f34,plain,(
% 1.94/0.62    ((~r2_hidden(sK1,sK3) & r2_hidden(sK3,sK2)) | ~r2_hidden(sK1,k8_setfam_1(sK0,sK2))) & (! [X4] : (r2_hidden(sK1,X4) | ~r2_hidden(X4,sK2)) | r2_hidden(sK1,k8_setfam_1(sK0,sK2))) & r2_hidden(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.94/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f31,f33,f32])).
% 1.94/0.62  fof(f32,plain,(
% 1.94/0.62    ? [X0,X1,X2] : ((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X4] : (r2_hidden(X1,X4) | ~r2_hidden(X4,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) => ((? [X3] : (~r2_hidden(sK1,X3) & r2_hidden(X3,sK2)) | ~r2_hidden(sK1,k8_setfam_1(sK0,sK2))) & (! [X4] : (r2_hidden(sK1,X4) | ~r2_hidden(X4,sK2)) | r2_hidden(sK1,k8_setfam_1(sK0,sK2))) & r2_hidden(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 1.94/0.62    introduced(choice_axiom,[])).
% 1.94/0.62  fof(f33,plain,(
% 1.94/0.62    ? [X3] : (~r2_hidden(sK1,X3) & r2_hidden(X3,sK2)) => (~r2_hidden(sK1,sK3) & r2_hidden(sK3,sK2))),
% 1.94/0.62    introduced(choice_axiom,[])).
% 1.94/0.62  fof(f31,plain,(
% 1.94/0.62    ? [X0,X1,X2] : ((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X4] : (r2_hidden(X1,X4) | ~r2_hidden(X4,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.94/0.62    inference(rectify,[],[f30])).
% 1.94/0.62  fof(f30,plain,(
% 1.94/0.62    ? [X0,X1,X2] : ((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.94/0.62    inference(flattening,[],[f29])).
% 1.94/0.62  fof(f29,plain,(
% 1.94/0.62    ? [X0,X1,X2] : (((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2)))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.94/0.62    inference(nnf_transformation,[],[f18])).
% 1.94/0.62  fof(f18,plain,(
% 1.94/0.62    ? [X0,X1,X2] : ((r2_hidden(X1,k8_setfam_1(X0,X2)) <~> ! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.94/0.62    inference(flattening,[],[f17])).
% 1.94/0.62  fof(f17,plain,(
% 1.94/0.62    ? [X0,X1,X2] : (((r2_hidden(X1,k8_setfam_1(X0,X2)) <~> ! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2))) & r2_hidden(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.94/0.62    inference(ennf_transformation,[],[f16])).
% 1.94/0.62  fof(f16,negated_conjecture,(
% 1.94/0.62    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r2_hidden(X1,X0) => (r2_hidden(X1,k8_setfam_1(X0,X2)) <=> ! [X3] : (r2_hidden(X3,X2) => r2_hidden(X1,X3)))))),
% 1.94/0.62    inference(negated_conjecture,[],[f15])).
% 1.94/0.62  fof(f15,conjecture,(
% 1.94/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r2_hidden(X1,X0) => (r2_hidden(X1,k8_setfam_1(X0,X2)) <=> ! [X3] : (r2_hidden(X3,X2) => r2_hidden(X1,X3)))))),
% 1.94/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_setfam_1)).
% 1.94/0.62  fof(f235,plain,(
% 1.94/0.62    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.94/0.62    inference(superposition,[],[f119,f69])).
% 1.94/0.62  fof(f69,plain,(
% 1.94/0.62    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.94/0.62    inference(cnf_transformation,[],[f23])).
% 1.94/0.62  fof(f23,plain,(
% 1.94/0.62    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.94/0.62    inference(ennf_transformation,[],[f9])).
% 1.94/0.62  fof(f9,axiom,(
% 1.94/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 1.94/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).
% 1.94/0.62  fof(f119,plain,(
% 1.94/0.62    k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 1.94/0.62    inference(unit_resulting_resolution,[],[f54,f68])).
% 1.94/0.62  fof(f68,plain,(
% 1.94/0.62    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.94/0.62    inference(cnf_transformation,[],[f22])).
% 1.94/0.62  fof(f22,plain,(
% 1.94/0.62    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.94/0.62    inference(ennf_transformation,[],[f11])).
% 1.94/0.62  fof(f11,axiom,(
% 1.94/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 1.94/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).
% 1.94/0.62  fof(f706,plain,(
% 1.94/0.62    ~spl8_1 | spl8_2 | ~spl8_3 | ~spl8_8),
% 1.94/0.62    inference(avatar_contradiction_clause,[],[f705])).
% 1.94/0.62  fof(f705,plain,(
% 1.94/0.62    $false | (~spl8_1 | spl8_2 | ~spl8_3 | ~spl8_8)),
% 1.94/0.62    inference(subsumption_resolution,[],[f700,f692])).
% 1.94/0.62  fof(f692,plain,(
% 1.94/0.62    r1_tarski(k1_setfam_1(sK2),sK3) | ~spl8_3),
% 1.94/0.62    inference(unit_resulting_resolution,[],[f105,f66])).
% 1.94/0.62  fof(f66,plain,(
% 1.94/0.62    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 1.94/0.62    inference(cnf_transformation,[],[f20])).
% 1.94/0.62  fof(f20,plain,(
% 1.94/0.62    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 1.94/0.62    inference(ennf_transformation,[],[f12])).
% 1.94/0.62  fof(f12,axiom,(
% 1.94/0.62    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 1.94/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).
% 1.94/0.62  fof(f700,plain,(
% 1.94/0.62    ~r1_tarski(k1_setfam_1(sK2),sK3) | (~spl8_1 | spl8_2 | ~spl8_8)),
% 1.94/0.62    inference(unit_resulting_resolution,[],[f100,f682,f73])).
% 1.94/0.62  fof(f682,plain,(
% 1.94/0.62    r2_hidden(sK1,k1_setfam_1(sK2)) | (~spl8_1 | ~spl8_8)),
% 1.94/0.62    inference(forward_demodulation,[],[f95,f167])).
% 1.94/0.62  fof(f167,plain,(
% 1.94/0.62    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~spl8_8),
% 1.94/0.62    inference(avatar_component_clause,[],[f165])).
% 1.94/0.62  fof(f95,plain,(
% 1.94/0.62    r2_hidden(sK1,k8_setfam_1(sK0,sK2)) | ~spl8_1),
% 1.94/0.62    inference(avatar_component_clause,[],[f94])).
% 1.94/0.62  fof(f94,plain,(
% 1.94/0.62    spl8_1 <=> r2_hidden(sK1,k8_setfam_1(sK0,sK2))),
% 1.94/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.94/0.62  fof(f100,plain,(
% 1.94/0.62    ~r2_hidden(sK1,sK3) | spl8_2),
% 1.94/0.62    inference(avatar_component_clause,[],[f98])).
% 1.94/0.62  fof(f98,plain,(
% 1.94/0.62    spl8_2 <=> r2_hidden(sK1,sK3)),
% 1.94/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.94/0.62  fof(f681,plain,(
% 1.94/0.62    spl8_1 | ~spl8_4 | spl8_7 | ~spl8_8),
% 1.94/0.62    inference(avatar_contradiction_clause,[],[f680])).
% 1.94/0.62  fof(f680,plain,(
% 1.94/0.62    $false | (spl8_1 | ~spl8_4 | spl8_7 | ~spl8_8)),
% 1.94/0.62    inference(subsumption_resolution,[],[f675,f631])).
% 1.94/0.62  fof(f631,plain,(
% 1.94/0.62    r2_hidden(sK1,sK5(sK2,k1_tarski(sK1))) | (spl8_1 | ~spl8_4 | spl8_7 | ~spl8_8)),
% 1.94/0.62    inference(unit_resulting_resolution,[],[f267,f109])).
% 1.94/0.62  fof(f109,plain,(
% 1.94/0.62    ( ! [X4] : (~r2_hidden(X4,sK2) | r2_hidden(sK1,X4)) ) | ~spl8_4),
% 1.94/0.62    inference(avatar_component_clause,[],[f108])).
% 1.94/0.62  fof(f108,plain,(
% 1.94/0.62    spl8_4 <=> ! [X4] : (r2_hidden(sK1,X4) | ~r2_hidden(X4,sK2))),
% 1.94/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.94/0.62  fof(f267,plain,(
% 1.94/0.62    r2_hidden(sK5(sK2,k1_tarski(sK1)),sK2) | (spl8_1 | spl8_7 | ~spl8_8)),
% 1.94/0.62    inference(unit_resulting_resolution,[],[f203,f162,f71])).
% 1.94/0.62  fof(f71,plain,(
% 1.94/0.62    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | r2_hidden(sK5(X0,X1),X0)) )),
% 1.94/0.62    inference(cnf_transformation,[],[f41])).
% 1.94/0.62  fof(f41,plain,(
% 1.94/0.62    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | (~r1_tarski(X1,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),X0)))),
% 1.94/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f25,f40])).
% 1.94/0.62  fof(f40,plain,(
% 1.94/0.62    ! [X1,X0] : (? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)) => (~r1_tarski(X1,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),X0)))),
% 1.94/0.62    introduced(choice_axiom,[])).
% 1.94/0.62  fof(f25,plain,(
% 1.94/0.62    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 1.94/0.62    inference(flattening,[],[f24])).
% 1.94/0.62  fof(f24,plain,(
% 1.94/0.62    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 1.94/0.62    inference(ennf_transformation,[],[f14])).
% 1.94/0.62  fof(f14,axiom,(
% 1.94/0.62    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 1.94/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).
% 1.94/0.62  fof(f162,plain,(
% 1.94/0.62    k1_xboole_0 != sK2 | spl8_7),
% 1.94/0.62    inference(avatar_component_clause,[],[f161])).
% 1.94/0.62  fof(f203,plain,(
% 1.94/0.62    ~r1_tarski(k1_tarski(sK1),k1_setfam_1(sK2)) | (spl8_1 | ~spl8_8)),
% 1.94/0.62    inference(backward_demodulation,[],[f125,f167])).
% 1.94/0.62  fof(f125,plain,(
% 1.94/0.62    ~r1_tarski(k1_tarski(sK1),k8_setfam_1(sK0,sK2)) | spl8_1),
% 1.94/0.62    inference(unit_resulting_resolution,[],[f90,f96,f73])).
% 1.94/0.62  fof(f96,plain,(
% 1.94/0.62    ~r2_hidden(sK1,k8_setfam_1(sK0,sK2)) | spl8_1),
% 1.94/0.62    inference(avatar_component_clause,[],[f94])).
% 1.94/0.62  fof(f675,plain,(
% 1.94/0.62    ~r2_hidden(sK1,sK5(sK2,k1_tarski(sK1))) | (spl8_1 | spl8_7 | ~spl8_8)),
% 1.94/0.62    inference(unit_resulting_resolution,[],[f269,f81])).
% 1.94/0.62  fof(f81,plain,(
% 1.94/0.62    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.94/0.62    inference(cnf_transformation,[],[f50])).
% 1.94/0.62  fof(f50,plain,(
% 1.94/0.62    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.94/0.62    inference(nnf_transformation,[],[f5])).
% 1.94/0.62  fof(f5,axiom,(
% 1.94/0.62    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.94/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).
% 1.94/0.62  fof(f269,plain,(
% 1.94/0.62    ~r1_tarski(k1_tarski(sK1),sK5(sK2,k1_tarski(sK1))) | (spl8_1 | spl8_7 | ~spl8_8)),
% 1.94/0.62    inference(unit_resulting_resolution,[],[f203,f162,f72])).
% 1.94/0.62  fof(f72,plain,(
% 1.94/0.62    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X1,sK5(X0,X1))) )),
% 1.94/0.62    inference(cnf_transformation,[],[f41])).
% 1.94/0.62  fof(f198,plain,(
% 1.94/0.62    spl8_1 | ~spl8_7),
% 1.94/0.62    inference(avatar_contradiction_clause,[],[f197])).
% 1.94/0.62  fof(f197,plain,(
% 1.94/0.62    $false | (spl8_1 | ~spl8_7)),
% 1.94/0.62    inference(subsumption_resolution,[],[f196,f59])).
% 1.94/0.62  fof(f59,plain,(
% 1.94/0.62    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.94/0.62    inference(cnf_transformation,[],[f8])).
% 1.94/0.62  fof(f8,axiom,(
% 1.94/0.62    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.94/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.94/0.62  fof(f196,plain,(
% 1.94/0.62    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | (spl8_1 | ~spl8_7)),
% 1.94/0.62    inference(subsumption_resolution,[],[f195,f55])).
% 1.94/0.62  fof(f55,plain,(
% 1.94/0.62    r2_hidden(sK1,sK0)),
% 1.94/0.62    inference(cnf_transformation,[],[f34])).
% 1.94/0.62  fof(f195,plain,(
% 1.94/0.62    ~r2_hidden(sK1,sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | (spl8_1 | ~spl8_7)),
% 1.94/0.62    inference(superposition,[],[f172,f88])).
% 1.94/0.62  fof(f88,plain,(
% 1.94/0.62    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.94/0.62    inference(equality_resolution,[],[f70])).
% 1.94/0.62  fof(f70,plain,(
% 1.94/0.62    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.94/0.62    inference(cnf_transformation,[],[f23])).
% 1.94/0.62  fof(f172,plain,(
% 1.94/0.62    ~r2_hidden(sK1,k8_setfam_1(sK0,k1_xboole_0)) | (spl8_1 | ~spl8_7)),
% 1.94/0.62    inference(backward_demodulation,[],[f96,f163])).
% 1.94/0.62  fof(f110,plain,(
% 1.94/0.62    spl8_1 | spl8_4),
% 1.94/0.62    inference(avatar_split_clause,[],[f56,f108,f94])).
% 1.94/0.62  fof(f56,plain,(
% 1.94/0.62    ( ! [X4] : (r2_hidden(sK1,X4) | ~r2_hidden(X4,sK2) | r2_hidden(sK1,k8_setfam_1(sK0,sK2))) )),
% 1.94/0.62    inference(cnf_transformation,[],[f34])).
% 1.94/0.62  fof(f106,plain,(
% 1.94/0.62    ~spl8_1 | spl8_3),
% 1.94/0.62    inference(avatar_split_clause,[],[f57,f103,f94])).
% 1.94/0.62  fof(f57,plain,(
% 1.94/0.62    r2_hidden(sK3,sK2) | ~r2_hidden(sK1,k8_setfam_1(sK0,sK2))),
% 1.94/0.62    inference(cnf_transformation,[],[f34])).
% 1.94/0.62  fof(f101,plain,(
% 1.94/0.62    ~spl8_1 | ~spl8_2),
% 1.94/0.62    inference(avatar_split_clause,[],[f58,f98,f94])).
% 1.94/0.62  fof(f58,plain,(
% 1.94/0.62    ~r2_hidden(sK1,sK3) | ~r2_hidden(sK1,k8_setfam_1(sK0,sK2))),
% 1.94/0.62    inference(cnf_transformation,[],[f34])).
% 1.94/0.62  % SZS output end Proof for theBenchmark
% 1.94/0.62  % (7464)------------------------------
% 1.94/0.62  % (7464)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.94/0.62  % (7464)Termination reason: Refutation
% 1.94/0.62  
% 1.94/0.62  % (7464)Memory used [KB]: 11257
% 1.94/0.62  % (7464)Time elapsed: 0.193 s
% 1.94/0.62  % (7464)------------------------------
% 1.94/0.62  % (7464)------------------------------
% 1.94/0.62  % (7437)Success in time 0.261 s
%------------------------------------------------------------------------------
