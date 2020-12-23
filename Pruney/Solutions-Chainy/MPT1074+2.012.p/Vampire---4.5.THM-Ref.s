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
% DateTime   : Thu Dec  3 13:08:06 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 306 expanded)
%              Number of leaves         :   22 ( 102 expanded)
%              Depth                    :   25
%              Number of atoms          :  440 (1899 expanded)
%              Number of equality atoms :   54 (  71 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f615,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f117,f587,f276])).

fof(f276,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,k1_xboole_0)
      | r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f173,f61])).

fof(f61,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f173,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_tarski(X7,sK8(X6,X8))
      | r1_tarski(X6,X8)
      | ~ r1_tarski(X6,X7) ) ),
    inference(resolution,[],[f101,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK8(X0,X1),X2)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f63,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK8(X0,X1),X1)
          & r2_hidden(sK8(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f41,f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK8(X0,X1),X1)
        & r2_hidden(sK8(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f587,plain,(
    r1_tarski(k2_relat_1(sK7),k1_xboole_0) ),
    inference(backward_demodulation,[],[f187,f557])).

fof(f557,plain,(
    k1_xboole_0 = sK6 ),
    inference(resolution,[],[f556,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f556,plain,(
    sP0(sK5,sK6) ),
    inference(subsumption_resolution,[],[f555,f98])).

fof(f98,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f97])).

fof(f97,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f65,f64])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK8(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f555,plain,
    ( ~ r1_tarski(sK5,sK5)
    | sP0(sK5,sK6) ),
    inference(superposition,[],[f553,f213])).

fof(f213,plain,
    ( sK5 = k1_relat_1(sK7)
    | sP0(sK5,sK6) ),
    inference(subsumption_resolution,[],[f210,f57])).

fof(f57,plain,(
    v1_funct_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),sK4)
    & ! [X4] :
        ( r2_hidden(k3_funct_2(sK5,sK6,sK7,X4),sK4)
        | ~ m1_subset_1(X4,sK5) )
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_2(sK7,sK5,sK6)
    & v1_funct_1(sK7)
    & ~ v1_xboole_0(sK6)
    & ~ v1_xboole_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f16,f38,f37,f36])).

fof(f36,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
                & ! [X4] :
                    ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                    | ~ m1_subset_1(X4,X1) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_2(X3,X1,X2)
                & v1_funct_1(X3) )
            & ~ v1_xboole_0(X2) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(sK5,X2,X3),sK4)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(sK5,X2,X3,X4),sK4)
                  | ~ m1_subset_1(X4,sK5) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X2)))
              & v1_funct_2(X3,sK5,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k2_relset_1(sK5,X2,X3),sK4)
            & ! [X4] :
                ( r2_hidden(k3_funct_2(sK5,X2,X3,X4),sK4)
                | ~ m1_subset_1(X4,sK5) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X2)))
            & v1_funct_2(X3,sK5,X2)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k2_relset_1(sK5,sK6,X3),sK4)
          & ! [X4] :
              ( r2_hidden(k3_funct_2(sK5,sK6,X3,X4),sK4)
              | ~ m1_subset_1(X4,sK5) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
          & v1_funct_2(X3,sK5,sK6)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k2_relset_1(sK5,sK6,X3),sK4)
        & ! [X4] :
            ( r2_hidden(k3_funct_2(sK5,sK6,X3,X4),sK4)
            | ~ m1_subset_1(X4,sK5) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
        & v1_funct_2(X3,sK5,sK6)
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),sK4)
      & ! [X4] :
          ( r2_hidden(k3_funct_2(sK5,sK6,sK7,X4),sK4)
          | ~ m1_subset_1(X4,sK5) )
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      & v1_funct_2(sK7,sK5,sK6)
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                  | ~ m1_subset_1(X4,X1) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                  | ~ m1_subset_1(X4,X1) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_2(X3,X1,X2)
                  & v1_funct_1(X3) )
               => ( ! [X4] :
                      ( m1_subset_1(X4,X1)
                     => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) )
                 => r1_tarski(k2_relset_1(X1,X2,X3),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_2(X3,X1,X2)
                & v1_funct_1(X3) )
             => ( ! [X4] :
                    ( m1_subset_1(X4,X1)
                   => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) )
               => r1_tarski(k2_relset_1(X1,X2,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_funct_2)).

fof(f210,plain,
    ( ~ v1_funct_2(sK7,sK5,sK6)
    | sP0(sK5,sK6)
    | sK5 = k1_relat_1(sK7) ),
    inference(resolution,[],[f126,f58])).

fof(f58,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f39])).

fof(f126,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X5,X3,X4)
      | sP0(X3,X4)
      | k1_relat_1(X5) = X3 ) ),
    inference(subsumption_resolution,[],[f124,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X2,X1,X0)
        & sP1(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f25,f32,f31,f30])).

fof(f31,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP2(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f124,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | ~ v1_funct_2(X5,X3,X4)
      | sP0(X3,X4)
      | ~ sP1(X3,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f75,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f553,plain,(
    ~ r1_tarski(k1_relat_1(sK7),sK5) ),
    inference(subsumption_resolution,[],[f551,f117])).

fof(f551,plain,
    ( ~ r1_tarski(k1_relat_1(sK7),sK5)
    | r1_tarski(k2_relat_1(sK7),sK4) ),
    inference(resolution,[],[f483,f234])).

fof(f234,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | r1_tarski(k2_relat_1(X2),X0) ) ),
    inference(resolution,[],[f178,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f178,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(X1))
      | ~ sP3(X1,X2,X0) ) ),
    inference(resolution,[],[f123,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(X2,X1,X0)
        & v1_funct_1(X2) )
      | ~ sP3(X0,X1,X2) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X1,X0,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ sP3(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X1,X0,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ sP3(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1)) ) ),
    inference(duplicate_literal_removal,[],[f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f72,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f483,plain,
    ( sP3(sK4,k1_relat_1(sK7),sK7)
    | ~ r1_tarski(k1_relat_1(sK7),sK5) ),
    inference(subsumption_resolution,[],[f482,f56])).

fof(f56,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f39])).

fof(f482,plain,
    ( sP3(sK4,k1_relat_1(sK7),sK7)
    | ~ r1_tarski(k1_relat_1(sK7),sK5)
    | ~ v1_funct_1(sK7) ),
    inference(subsumption_resolution,[],[f481,f99])).

fof(f99,plain,(
    v1_relat_1(sK7) ),
    inference(resolution,[],[f69,f58])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f481,plain,
    ( ~ v1_relat_1(sK7)
    | sP3(sK4,k1_relat_1(sK7),sK7)
    | ~ r1_tarski(k1_relat_1(sK7),sK5)
    | ~ v1_funct_1(sK7) ),
    inference(duplicate_literal_removal,[],[f478])).

fof(f478,plain,
    ( ~ v1_relat_1(sK7)
    | sP3(sK4,k1_relat_1(sK7),sK7)
    | ~ r1_tarski(k1_relat_1(sK7),sK5)
    | ~ v1_funct_1(sK7)
    | sP3(sK4,k1_relat_1(sK7),sK7) ),
    inference(resolution,[],[f230,f151])).

fof(f151,plain,
    ( ~ m1_subset_1(sK9(k1_relat_1(sK7),sK4,sK7),sK5)
    | sP3(sK4,k1_relat_1(sK7),sK7) ),
    inference(subsumption_resolution,[],[f150,f99])).

fof(f150,plain,
    ( ~ m1_subset_1(sK9(k1_relat_1(sK7),sK4,sK7),sK5)
    | sP3(sK4,k1_relat_1(sK7),sK7)
    | ~ v1_relat_1(sK7) ),
    inference(subsumption_resolution,[],[f146,f56])).

fof(f146,plain,
    ( ~ m1_subset_1(sK9(k1_relat_1(sK7),sK4,sK7),sK5)
    | sP3(sK4,k1_relat_1(sK7),sK7)
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7) ),
    inference(resolution,[],[f145,f91])).

fof(f91,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(k1_funct_1(X2,sK9(k1_relat_1(X2),X1,X2)),X1)
      | sP3(X1,k1_relat_1(X2),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( sP3(X1,X0,X2)
      | ~ r2_hidden(k1_funct_1(X2,sK9(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( sP3(X1,X0,X2)
      | ( ~ r2_hidden(k1_funct_1(X2,sK9(X0,X1,X2)),X1)
        & r2_hidden(sK9(X0,X1,X2),X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f35,f52])).

fof(f52,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(k1_funct_1(X2,sK9(X0,X1,X2)),X1)
        & r2_hidden(sK9(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( sP3(X1,X0,X2)
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_folding,[],[f27,f34])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( ! [X3] :
              ( r2_hidden(X3,X0)
             => r2_hidden(k1_funct_1(X2,X3),X1) )
          & k1_relat_1(X2) = X0 )
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

fof(f145,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK7,X0),sK4)
      | ~ m1_subset_1(X0,sK5) ) ),
    inference(subsumption_resolution,[],[f144,f54])).

fof(f54,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f39])).

fof(f144,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK7,X0),sK4)
      | ~ m1_subset_1(X0,sK5)
      | v1_xboole_0(sK5) ) ),
    inference(subsumption_resolution,[],[f143,f56])).

fof(f143,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK7,X0),sK4)
      | ~ m1_subset_1(X0,sK5)
      | ~ v1_funct_1(sK7)
      | v1_xboole_0(sK5) ) ),
    inference(subsumption_resolution,[],[f142,f57])).

fof(f142,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK7,X0),sK4)
      | ~ m1_subset_1(X0,sK5)
      | ~ v1_funct_2(sK7,sK5,sK6)
      | ~ v1_funct_1(sK7)
      | v1_xboole_0(sK5) ) ),
    inference(subsumption_resolution,[],[f141,f58])).

fof(f141,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK7,X0),sK4)
      | ~ m1_subset_1(X0,sK5)
      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      | ~ v1_funct_2(sK7,sK5,sK6)
      | ~ v1_funct_1(sK7)
      | v1_xboole_0(sK5) ) ),
    inference(duplicate_literal_removal,[],[f140])).

fof(f140,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK7,X0),sK4)
      | ~ m1_subset_1(X0,sK5)
      | ~ m1_subset_1(X0,sK5)
      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      | ~ v1_funct_2(sK7,sK5,sK6)
      | ~ v1_funct_1(sK7)
      | v1_xboole_0(sK5) ) ),
    inference(superposition,[],[f59,f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f59,plain,(
    ! [X4] :
      ( r2_hidden(k3_funct_2(sK5,sK6,sK7,X4),sK4)
      | ~ m1_subset_1(X4,sK5) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f230,plain,(
    ! [X8,X7,X9] :
      ( m1_subset_1(sK9(k1_relat_1(X7),X8,X7),X9)
      | ~ v1_relat_1(X7)
      | sP3(X8,k1_relat_1(X7),X7)
      | ~ r1_tarski(k1_relat_1(X7),X9)
      | ~ v1_funct_1(X7) ) ),
    inference(resolution,[],[f132,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK9(k1_relat_1(X1),X0,X1),X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | sP3(X0,k1_relat_1(X1),X1)
      | ~ r1_tarski(k1_relat_1(X1),X2) ) ),
    inference(resolution,[],[f92,f63])).

fof(f92,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK9(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | sP3(X1,k1_relat_1(X2),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( sP3(X1,X0,X2)
      | r2_hidden(sK9(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f187,plain,(
    r1_tarski(k2_relat_1(sK7),sK6) ),
    inference(resolution,[],[f177,f66])).

fof(f177,plain,(
    m1_subset_1(k2_relat_1(sK7),k1_zfmisc_1(sK6)) ),
    inference(resolution,[],[f123,f58])).

fof(f117,plain,(
    ~ r1_tarski(k2_relat_1(sK7),sK4) ),
    inference(subsumption_resolution,[],[f116,f58])).

fof(f116,plain,
    ( ~ r1_tarski(k2_relat_1(sK7),sK4)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(superposition,[],[f60,f71])).

fof(f60,plain,(
    ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),sK4) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:23:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (1352)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (1369)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.52  % (1345)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (1350)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (1340)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (1351)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (1342)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (1360)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.53  % (1366)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (1341)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (1344)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (1354)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.54  % (1363)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.54  % (1355)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (1343)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (1367)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (1347)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (1361)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % (1365)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (1358)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (1370)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (1346)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.54  % (1364)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.55  % (1362)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.55  % (1349)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.55  % (1348)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.55  % (1368)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.55  % (1356)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.55  % (1359)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.56  % (1353)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.58  % (1370)Refutation found. Thanks to Tanya!
% 0.20/0.58  % SZS status Theorem for theBenchmark
% 0.20/0.59  % SZS output start Proof for theBenchmark
% 0.20/0.59  fof(f615,plain,(
% 0.20/0.59    $false),
% 0.20/0.59    inference(unit_resulting_resolution,[],[f117,f587,f276])).
% 0.20/0.59  fof(f276,plain,(
% 0.20/0.59    ( ! [X2,X3] : (~r1_tarski(X2,k1_xboole_0) | r1_tarski(X2,X3)) )),
% 0.20/0.59    inference(resolution,[],[f173,f61])).
% 0.20/0.59  fof(f61,plain,(
% 0.20/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f2])).
% 0.20/0.59  fof(f2,axiom,(
% 0.20/0.59    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.59  fof(f173,plain,(
% 0.20/0.59    ( ! [X6,X8,X7] : (~r1_tarski(X7,sK8(X6,X8)) | r1_tarski(X6,X8) | ~r1_tarski(X6,X7)) )),
% 0.20/0.59    inference(resolution,[],[f101,f68])).
% 1.84/0.60  fof(f68,plain,(
% 1.84/0.60    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.84/0.60    inference(cnf_transformation,[],[f19])).
% 1.84/0.60  fof(f19,plain,(
% 1.84/0.60    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.84/0.60    inference(ennf_transformation,[],[f5])).
% 1.84/0.60  fof(f5,axiom,(
% 1.84/0.60    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.84/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.84/0.60  fof(f101,plain,(
% 1.84/0.60    ( ! [X2,X0,X1] : (r2_hidden(sK8(X0,X1),X2) | ~r1_tarski(X0,X2) | r1_tarski(X0,X1)) )),
% 1.84/0.60    inference(resolution,[],[f63,f64])).
% 1.84/0.60  fof(f64,plain,(
% 1.84/0.60    ( ! [X0,X1] : (r2_hidden(sK8(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.84/0.60    inference(cnf_transformation,[],[f43])).
% 1.84/0.60  fof(f43,plain,(
% 1.84/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK8(X0,X1),X1) & r2_hidden(sK8(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.84/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f41,f42])).
% 1.84/0.60  fof(f42,plain,(
% 1.84/0.60    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK8(X0,X1),X1) & r2_hidden(sK8(X0,X1),X0)))),
% 1.84/0.60    introduced(choice_axiom,[])).
% 1.84/0.60  fof(f41,plain,(
% 1.84/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.84/0.60    inference(rectify,[],[f40])).
% 1.84/0.60  fof(f40,plain,(
% 1.84/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.84/0.60    inference(nnf_transformation,[],[f18])).
% 1.84/0.60  fof(f18,plain,(
% 1.84/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.84/0.60    inference(ennf_transformation,[],[f1])).
% 1.84/0.60  fof(f1,axiom,(
% 1.84/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.84/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.84/0.60  fof(f63,plain,(
% 1.84/0.60    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 1.84/0.60    inference(cnf_transformation,[],[f43])).
% 1.84/0.60  fof(f587,plain,(
% 1.84/0.60    r1_tarski(k2_relat_1(sK7),k1_xboole_0)),
% 1.84/0.60    inference(backward_demodulation,[],[f187,f557])).
% 1.84/0.60  fof(f557,plain,(
% 1.84/0.60    k1_xboole_0 = sK6),
% 1.84/0.60    inference(resolution,[],[f556,f77])).
% 1.84/0.60  fof(f77,plain,(
% 1.84/0.60    ( ! [X0,X1] : (~sP0(X0,X1) | k1_xboole_0 = X1) )),
% 1.84/0.60    inference(cnf_transformation,[],[f49])).
% 1.84/0.60  fof(f49,plain,(
% 1.84/0.60    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 1.84/0.60    inference(nnf_transformation,[],[f30])).
% 1.84/0.60  fof(f30,plain,(
% 1.84/0.60    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 1.84/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.84/0.60  fof(f556,plain,(
% 1.84/0.60    sP0(sK5,sK6)),
% 1.84/0.60    inference(subsumption_resolution,[],[f555,f98])).
% 1.84/0.60  fof(f98,plain,(
% 1.84/0.60    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.84/0.60    inference(duplicate_literal_removal,[],[f97])).
% 1.84/0.60  fof(f97,plain,(
% 1.84/0.60    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 1.84/0.60    inference(resolution,[],[f65,f64])).
% 1.84/0.60  fof(f65,plain,(
% 1.84/0.60    ( ! [X0,X1] : (~r2_hidden(sK8(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.84/0.60    inference(cnf_transformation,[],[f43])).
% 1.84/0.60  fof(f555,plain,(
% 1.84/0.60    ~r1_tarski(sK5,sK5) | sP0(sK5,sK6)),
% 1.84/0.60    inference(superposition,[],[f553,f213])).
% 1.84/0.60  fof(f213,plain,(
% 1.84/0.60    sK5 = k1_relat_1(sK7) | sP0(sK5,sK6)),
% 1.84/0.60    inference(subsumption_resolution,[],[f210,f57])).
% 1.84/0.60  fof(f57,plain,(
% 1.84/0.60    v1_funct_2(sK7,sK5,sK6)),
% 1.84/0.60    inference(cnf_transformation,[],[f39])).
% 1.84/0.60  fof(f39,plain,(
% 1.84/0.60    ((~r1_tarski(k2_relset_1(sK5,sK6,sK7),sK4) & ! [X4] : (r2_hidden(k3_funct_2(sK5,sK6,sK7,X4),sK4) | ~m1_subset_1(X4,sK5)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK7,sK5,sK6) & v1_funct_1(sK7)) & ~v1_xboole_0(sK6)) & ~v1_xboole_0(sK5)),
% 1.84/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f16,f38,f37,f36])).
% 1.84/0.60  fof(f36,plain,(
% 1.84/0.60    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(sK5,X2,X3),sK4) & ! [X4] : (r2_hidden(k3_funct_2(sK5,X2,X3,X4),sK4) | ~m1_subset_1(X4,sK5)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X2))) & v1_funct_2(X3,sK5,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK5))),
% 1.84/0.60    introduced(choice_axiom,[])).
% 1.84/0.60  fof(f37,plain,(
% 1.84/0.60    ? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(sK5,X2,X3),sK4) & ! [X4] : (r2_hidden(k3_funct_2(sK5,X2,X3,X4),sK4) | ~m1_subset_1(X4,sK5)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X2))) & v1_funct_2(X3,sK5,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (~r1_tarski(k2_relset_1(sK5,sK6,X3),sK4) & ! [X4] : (r2_hidden(k3_funct_2(sK5,sK6,X3,X4),sK4) | ~m1_subset_1(X4,sK5)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(X3,sK5,sK6) & v1_funct_1(X3)) & ~v1_xboole_0(sK6))),
% 1.84/0.60    introduced(choice_axiom,[])).
% 1.84/0.60  fof(f38,plain,(
% 1.84/0.60    ? [X3] : (~r1_tarski(k2_relset_1(sK5,sK6,X3),sK4) & ! [X4] : (r2_hidden(k3_funct_2(sK5,sK6,X3,X4),sK4) | ~m1_subset_1(X4,sK5)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(X3,sK5,sK6) & v1_funct_1(X3)) => (~r1_tarski(k2_relset_1(sK5,sK6,sK7),sK4) & ! [X4] : (r2_hidden(k3_funct_2(sK5,sK6,sK7,X4),sK4) | ~m1_subset_1(X4,sK5)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK7,sK5,sK6) & v1_funct_1(sK7))),
% 1.84/0.60    introduced(choice_axiom,[])).
% 1.84/0.60  fof(f16,plain,(
% 1.84/0.60    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 1.84/0.60    inference(flattening,[],[f15])).
% 1.84/0.60  fof(f15,plain,(
% 1.84/0.60    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 1.84/0.60    inference(ennf_transformation,[],[f14])).
% 1.84/0.60  fof(f14,negated_conjecture,(
% 1.84/0.60    ~! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 1.84/0.60    inference(negated_conjecture,[],[f13])).
% 1.84/0.60  fof(f13,conjecture,(
% 1.84/0.60    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 1.84/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_funct_2)).
% 1.84/0.60  fof(f210,plain,(
% 1.84/0.60    ~v1_funct_2(sK7,sK5,sK6) | sP0(sK5,sK6) | sK5 = k1_relat_1(sK7)),
% 1.84/0.60    inference(resolution,[],[f126,f58])).
% 1.84/0.60  fof(f58,plain,(
% 1.84/0.60    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 1.84/0.60    inference(cnf_transformation,[],[f39])).
% 1.84/0.60  fof(f126,plain,(
% 1.84/0.60    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X5,X3,X4) | sP0(X3,X4) | k1_relat_1(X5) = X3) )),
% 1.84/0.60    inference(subsumption_resolution,[],[f124,f79])).
% 1.84/0.60  fof(f79,plain,(
% 1.84/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP1(X0,X2,X1)) )),
% 1.84/0.60    inference(cnf_transformation,[],[f33])).
% 1.84/0.60  fof(f33,plain,(
% 1.84/0.60    ! [X0,X1,X2] : ((sP2(X2,X1,X0) & sP1(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.84/0.60    inference(definition_folding,[],[f25,f32,f31,f30])).
% 1.84/0.60  fof(f31,plain,(
% 1.84/0.60    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 1.84/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.84/0.60  fof(f32,plain,(
% 1.84/0.60    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP2(X2,X1,X0))),
% 1.84/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.84/0.60  fof(f25,plain,(
% 1.84/0.60    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.84/0.60    inference(flattening,[],[f24])).
% 1.84/0.60  fof(f24,plain,(
% 1.84/0.60    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.84/0.60    inference(ennf_transformation,[],[f10])).
% 1.84/0.60  fof(f10,axiom,(
% 1.84/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.84/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.84/0.60  fof(f124,plain,(
% 1.84/0.60    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | ~v1_funct_2(X5,X3,X4) | sP0(X3,X4) | ~sP1(X3,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 1.84/0.60    inference(superposition,[],[f75,f70])).
% 1.84/0.60  fof(f70,plain,(
% 1.84/0.60    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.84/0.60    inference(cnf_transformation,[],[f21])).
% 1.84/0.60  fof(f21,plain,(
% 1.84/0.60    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.84/0.60    inference(ennf_transformation,[],[f8])).
% 1.84/0.60  fof(f8,axiom,(
% 1.84/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.84/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.84/0.60  fof(f75,plain,(
% 1.84/0.60    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP0(X0,X2) | ~sP1(X0,X1,X2)) )),
% 1.84/0.60    inference(cnf_transformation,[],[f48])).
% 1.84/0.60  fof(f48,plain,(
% 1.84/0.60    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP0(X0,X2) | ~sP1(X0,X1,X2))),
% 1.84/0.60    inference(rectify,[],[f47])).
% 1.84/0.60  fof(f47,plain,(
% 1.84/0.60    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 1.84/0.60    inference(nnf_transformation,[],[f31])).
% 1.84/0.60  fof(f553,plain,(
% 1.84/0.60    ~r1_tarski(k1_relat_1(sK7),sK5)),
% 1.84/0.60    inference(subsumption_resolution,[],[f551,f117])).
% 1.84/0.60  fof(f551,plain,(
% 1.84/0.60    ~r1_tarski(k1_relat_1(sK7),sK5) | r1_tarski(k2_relat_1(sK7),sK4)),
% 1.84/0.60    inference(resolution,[],[f483,f234])).
% 1.84/0.60  fof(f234,plain,(
% 1.84/0.60    ( ! [X2,X0,X1] : (~sP3(X0,X1,X2) | r1_tarski(k2_relat_1(X2),X0)) )),
% 1.84/0.60    inference(resolution,[],[f178,f66])).
% 1.84/0.60  fof(f66,plain,(
% 1.84/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.84/0.60    inference(cnf_transformation,[],[f44])).
% 1.84/0.60  fof(f44,plain,(
% 1.84/0.60    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.84/0.60    inference(nnf_transformation,[],[f4])).
% 1.84/0.60  fof(f4,axiom,(
% 1.84/0.60    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.84/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.84/0.60  fof(f178,plain,(
% 1.84/0.60    ( ! [X2,X0,X1] : (m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(X1)) | ~sP3(X1,X2,X0)) )),
% 1.84/0.60    inference(resolution,[],[f123,f83])).
% 1.84/0.60  fof(f83,plain,(
% 1.84/0.60    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~sP3(X0,X1,X2)) )),
% 1.84/0.60    inference(cnf_transformation,[],[f51])).
% 1.84/0.60  fof(f51,plain,(
% 1.84/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X2,X1,X0) & v1_funct_1(X2)) | ~sP3(X0,X1,X2))),
% 1.84/0.60    inference(rectify,[],[f50])).
% 1.84/0.60  fof(f50,plain,(
% 1.84/0.60    ! [X1,X0,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~sP3(X1,X0,X2))),
% 1.84/0.60    inference(nnf_transformation,[],[f34])).
% 1.84/0.60  fof(f34,plain,(
% 1.84/0.60    ! [X1,X0,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~sP3(X1,X0,X2))),
% 1.84/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 1.84/0.60  fof(f123,plain,(
% 1.84/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1))) )),
% 1.84/0.60    inference(duplicate_literal_removal,[],[f122])).
% 1.84/0.60  fof(f122,plain,(
% 1.84/0.60    ( ! [X2,X0,X1] : (m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.84/0.60    inference(superposition,[],[f72,f71])).
% 1.84/0.60  fof(f71,plain,(
% 1.84/0.60    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.84/0.60    inference(cnf_transformation,[],[f22])).
% 1.84/0.60  fof(f22,plain,(
% 1.84/0.60    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.84/0.60    inference(ennf_transformation,[],[f9])).
% 1.84/0.60  fof(f9,axiom,(
% 1.84/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.84/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.84/0.60  fof(f72,plain,(
% 1.84/0.60    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.84/0.60    inference(cnf_transformation,[],[f23])).
% 1.84/0.60  fof(f23,plain,(
% 1.84/0.60    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.84/0.60    inference(ennf_transformation,[],[f7])).
% 1.84/0.60  fof(f7,axiom,(
% 1.84/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 1.84/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 1.84/0.60  fof(f483,plain,(
% 1.84/0.60    sP3(sK4,k1_relat_1(sK7),sK7) | ~r1_tarski(k1_relat_1(sK7),sK5)),
% 1.84/0.60    inference(subsumption_resolution,[],[f482,f56])).
% 1.84/0.60  fof(f56,plain,(
% 1.84/0.60    v1_funct_1(sK7)),
% 1.84/0.60    inference(cnf_transformation,[],[f39])).
% 1.84/0.60  fof(f482,plain,(
% 1.84/0.60    sP3(sK4,k1_relat_1(sK7),sK7) | ~r1_tarski(k1_relat_1(sK7),sK5) | ~v1_funct_1(sK7)),
% 1.84/0.60    inference(subsumption_resolution,[],[f481,f99])).
% 1.84/0.60  fof(f99,plain,(
% 1.84/0.60    v1_relat_1(sK7)),
% 1.84/0.60    inference(resolution,[],[f69,f58])).
% 1.84/0.60  fof(f69,plain,(
% 1.84/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.84/0.60    inference(cnf_transformation,[],[f20])).
% 1.84/0.60  fof(f20,plain,(
% 1.84/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.84/0.60    inference(ennf_transformation,[],[f6])).
% 1.84/0.60  fof(f6,axiom,(
% 1.84/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.84/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.84/0.60  fof(f481,plain,(
% 1.84/0.60    ~v1_relat_1(sK7) | sP3(sK4,k1_relat_1(sK7),sK7) | ~r1_tarski(k1_relat_1(sK7),sK5) | ~v1_funct_1(sK7)),
% 1.84/0.60    inference(duplicate_literal_removal,[],[f478])).
% 1.84/0.60  fof(f478,plain,(
% 1.84/0.60    ~v1_relat_1(sK7) | sP3(sK4,k1_relat_1(sK7),sK7) | ~r1_tarski(k1_relat_1(sK7),sK5) | ~v1_funct_1(sK7) | sP3(sK4,k1_relat_1(sK7),sK7)),
% 1.84/0.60    inference(resolution,[],[f230,f151])).
% 1.84/0.60  fof(f151,plain,(
% 1.84/0.60    ~m1_subset_1(sK9(k1_relat_1(sK7),sK4,sK7),sK5) | sP3(sK4,k1_relat_1(sK7),sK7)),
% 1.84/0.60    inference(subsumption_resolution,[],[f150,f99])).
% 1.84/0.60  fof(f150,plain,(
% 1.84/0.60    ~m1_subset_1(sK9(k1_relat_1(sK7),sK4,sK7),sK5) | sP3(sK4,k1_relat_1(sK7),sK7) | ~v1_relat_1(sK7)),
% 1.84/0.60    inference(subsumption_resolution,[],[f146,f56])).
% 1.84/0.60  fof(f146,plain,(
% 1.84/0.60    ~m1_subset_1(sK9(k1_relat_1(sK7),sK4,sK7),sK5) | sP3(sK4,k1_relat_1(sK7),sK7) | ~v1_funct_1(sK7) | ~v1_relat_1(sK7)),
% 1.84/0.60    inference(resolution,[],[f145,f91])).
% 1.84/0.60  fof(f91,plain,(
% 1.84/0.60    ( ! [X2,X1] : (~r2_hidden(k1_funct_1(X2,sK9(k1_relat_1(X2),X1,X2)),X1) | sP3(X1,k1_relat_1(X2),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.84/0.60    inference(equality_resolution,[],[f85])).
% 1.84/0.60  fof(f85,plain,(
% 1.84/0.60    ( ! [X2,X0,X1] : (sP3(X1,X0,X2) | ~r2_hidden(k1_funct_1(X2,sK9(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.84/0.60    inference(cnf_transformation,[],[f53])).
% 1.84/0.60  fof(f53,plain,(
% 1.84/0.60    ! [X0,X1,X2] : (sP3(X1,X0,X2) | (~r2_hidden(k1_funct_1(X2,sK9(X0,X1,X2)),X1) & r2_hidden(sK9(X0,X1,X2),X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.84/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f35,f52])).
% 1.84/0.60  fof(f52,plain,(
% 1.84/0.60    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) => (~r2_hidden(k1_funct_1(X2,sK9(X0,X1,X2)),X1) & r2_hidden(sK9(X0,X1,X2),X0)))),
% 1.84/0.60    introduced(choice_axiom,[])).
% 1.84/0.60  fof(f35,plain,(
% 1.84/0.60    ! [X0,X1,X2] : (sP3(X1,X0,X2) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.84/0.60    inference(definition_folding,[],[f27,f34])).
% 1.84/0.60  fof(f27,plain,(
% 1.84/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.84/0.60    inference(flattening,[],[f26])).
% 1.84/0.60  fof(f26,plain,(
% 1.84/0.60    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.84/0.60    inference(ennf_transformation,[],[f12])).
% 1.84/0.60  fof(f12,axiom,(
% 1.84/0.60    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 1.84/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).
% 1.84/0.60  fof(f145,plain,(
% 1.84/0.60    ( ! [X0] : (r2_hidden(k1_funct_1(sK7,X0),sK4) | ~m1_subset_1(X0,sK5)) )),
% 1.84/0.60    inference(subsumption_resolution,[],[f144,f54])).
% 1.84/0.60  fof(f54,plain,(
% 1.84/0.60    ~v1_xboole_0(sK5)),
% 1.84/0.60    inference(cnf_transformation,[],[f39])).
% 1.84/0.60  fof(f144,plain,(
% 1.84/0.60    ( ! [X0] : (r2_hidden(k1_funct_1(sK7,X0),sK4) | ~m1_subset_1(X0,sK5) | v1_xboole_0(sK5)) )),
% 1.84/0.60    inference(subsumption_resolution,[],[f143,f56])).
% 1.84/0.60  fof(f143,plain,(
% 1.84/0.60    ( ! [X0] : (r2_hidden(k1_funct_1(sK7,X0),sK4) | ~m1_subset_1(X0,sK5) | ~v1_funct_1(sK7) | v1_xboole_0(sK5)) )),
% 1.84/0.60    inference(subsumption_resolution,[],[f142,f57])).
% 1.84/0.60  fof(f142,plain,(
% 1.84/0.60    ( ! [X0] : (r2_hidden(k1_funct_1(sK7,X0),sK4) | ~m1_subset_1(X0,sK5) | ~v1_funct_2(sK7,sK5,sK6) | ~v1_funct_1(sK7) | v1_xboole_0(sK5)) )),
% 1.84/0.60    inference(subsumption_resolution,[],[f141,f58])).
% 1.84/0.60  fof(f141,plain,(
% 1.84/0.60    ( ! [X0] : (r2_hidden(k1_funct_1(sK7,X0),sK4) | ~m1_subset_1(X0,sK5) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) | ~v1_funct_2(sK7,sK5,sK6) | ~v1_funct_1(sK7) | v1_xboole_0(sK5)) )),
% 1.84/0.60    inference(duplicate_literal_removal,[],[f140])).
% 1.84/0.60  fof(f140,plain,(
% 1.84/0.60    ( ! [X0] : (r2_hidden(k1_funct_1(sK7,X0),sK4) | ~m1_subset_1(X0,sK5) | ~m1_subset_1(X0,sK5) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) | ~v1_funct_2(sK7,sK5,sK6) | ~v1_funct_1(sK7) | v1_xboole_0(sK5)) )),
% 1.84/0.60    inference(superposition,[],[f59,f86])).
% 1.84/0.60  fof(f86,plain,(
% 1.84/0.60    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 1.84/0.60    inference(cnf_transformation,[],[f29])).
% 1.84/0.60  fof(f29,plain,(
% 1.84/0.60    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 1.84/0.60    inference(flattening,[],[f28])).
% 1.84/0.60  fof(f28,plain,(
% 1.84/0.60    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 1.84/0.60    inference(ennf_transformation,[],[f11])).
% 1.84/0.60  fof(f11,axiom,(
% 1.84/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 1.84/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 1.84/0.60  fof(f59,plain,(
% 1.84/0.60    ( ! [X4] : (r2_hidden(k3_funct_2(sK5,sK6,sK7,X4),sK4) | ~m1_subset_1(X4,sK5)) )),
% 1.84/0.60    inference(cnf_transformation,[],[f39])).
% 1.84/0.60  fof(f230,plain,(
% 1.84/0.60    ( ! [X8,X7,X9] : (m1_subset_1(sK9(k1_relat_1(X7),X8,X7),X9) | ~v1_relat_1(X7) | sP3(X8,k1_relat_1(X7),X7) | ~r1_tarski(k1_relat_1(X7),X9) | ~v1_funct_1(X7)) )),
% 1.84/0.60    inference(resolution,[],[f132,f62])).
% 1.84/0.60  fof(f62,plain,(
% 1.84/0.60    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 1.84/0.60    inference(cnf_transformation,[],[f17])).
% 1.84/0.60  fof(f17,plain,(
% 1.84/0.60    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.84/0.60    inference(ennf_transformation,[],[f3])).
% 1.84/0.60  fof(f3,axiom,(
% 1.84/0.60    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.84/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.84/0.60  fof(f132,plain,(
% 1.84/0.60    ( ! [X2,X0,X1] : (r2_hidden(sK9(k1_relat_1(X1),X0,X1),X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | sP3(X0,k1_relat_1(X1),X1) | ~r1_tarski(k1_relat_1(X1),X2)) )),
% 1.84/0.60    inference(resolution,[],[f92,f63])).
% 1.84/0.60  fof(f92,plain,(
% 1.84/0.60    ( ! [X2,X1] : (r2_hidden(sK9(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | sP3(X1,k1_relat_1(X2),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.84/0.60    inference(equality_resolution,[],[f84])).
% 1.84/0.60  fof(f84,plain,(
% 1.84/0.60    ( ! [X2,X0,X1] : (sP3(X1,X0,X2) | r2_hidden(sK9(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.84/0.60    inference(cnf_transformation,[],[f53])).
% 1.84/0.60  fof(f187,plain,(
% 1.84/0.60    r1_tarski(k2_relat_1(sK7),sK6)),
% 1.84/0.60    inference(resolution,[],[f177,f66])).
% 1.84/0.60  fof(f177,plain,(
% 1.84/0.60    m1_subset_1(k2_relat_1(sK7),k1_zfmisc_1(sK6))),
% 1.84/0.60    inference(resolution,[],[f123,f58])).
% 1.84/0.60  fof(f117,plain,(
% 1.84/0.60    ~r1_tarski(k2_relat_1(sK7),sK4)),
% 1.84/0.60    inference(subsumption_resolution,[],[f116,f58])).
% 1.84/0.60  fof(f116,plain,(
% 1.84/0.60    ~r1_tarski(k2_relat_1(sK7),sK4) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 1.84/0.60    inference(superposition,[],[f60,f71])).
% 1.84/0.60  fof(f60,plain,(
% 1.84/0.60    ~r1_tarski(k2_relset_1(sK5,sK6,sK7),sK4)),
% 1.84/0.60    inference(cnf_transformation,[],[f39])).
% 1.84/0.60  % SZS output end Proof for theBenchmark
% 1.84/0.60  % (1370)------------------------------
% 1.84/0.60  % (1370)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.60  % (1370)Termination reason: Refutation
% 1.84/0.60  
% 1.84/0.60  % (1370)Memory used [KB]: 2174
% 1.84/0.60  % (1370)Time elapsed: 0.180 s
% 1.84/0.60  % (1370)------------------------------
% 1.84/0.60  % (1370)------------------------------
% 1.84/0.60  % (1339)Success in time 0.239 s
%------------------------------------------------------------------------------
