%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:50 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 162 expanded)
%              Number of leaves         :   11 (  45 expanded)
%              Depth                    :   22
%              Number of atoms          :  236 ( 766 expanded)
%              Number of equality atoms :   13 (  19 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f176,plain,(
    $false ),
    inference(subsumption_resolution,[],[f175,f34])).

fof(f34,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),sK1)
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))
    & v3_setfam_1(sK3,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))
    & v3_setfam_1(sK2,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f13,f23,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
            & v3_setfam_1(X2,X0) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        & v3_setfam_1(X1,X0) )
   => ( ? [X2] :
          ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK1),sK2,X2),sK1)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK1)))
          & v3_setfam_1(X2,sK1) )
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))
      & v3_setfam_1(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X2] :
        ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK1),sK2,X2),sK1)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK1)))
        & v3_setfam_1(X2,sK1) )
   => ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),sK1)
      & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))
      & v3_setfam_1(sK3,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
          & v3_setfam_1(X2,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      & v3_setfam_1(X1,X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
          & v3_setfam_1(X2,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      & v3_setfam_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
          & v3_setfam_1(X1,X0) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
              & v3_setfam_1(X2,X0) )
           => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
              & v3_setfam_1(X1,X0) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
                  & v3_setfam_1(X2,X0) )
               => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
            & v3_setfam_1(X1,X0) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
                & v3_setfam_1(X2,X0) )
             => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_setfam_1)).

fof(f175,plain,(
    ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(subsumption_resolution,[],[f168,f33])).

fof(f33,plain,(
    v3_setfam_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f168,plain,
    ( ~ v3_setfam_1(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(resolution,[],[f167,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v3_setfam_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( v3_setfam_1(X1,X0)
          | r2_hidden(X0,X1) )
        & ( ~ r2_hidden(X0,X1)
          | ~ v3_setfam_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v3_setfam_1(X1,X0)
      <=> ~ r2_hidden(X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( v3_setfam_1(X1,X0)
      <=> ~ r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_setfam_1)).

fof(f167,plain,(
    r2_hidden(sK1,sK2) ),
    inference(subsumption_resolution,[],[f166,f36])).

fof(f36,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f166,plain,
    ( r2_hidden(sK1,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(subsumption_resolution,[],[f159,f35])).

fof(f35,plain,(
    v3_setfam_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f159,plain,
    ( r2_hidden(sK1,sK2)
    | ~ v3_setfam_1(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(resolution,[],[f158,f41])).

fof(f158,plain,
    ( r2_hidden(sK1,sK3)
    | r2_hidden(sK1,sK2) ),
    inference(resolution,[],[f120,f57])).

fof(f57,plain,(
    ! [X0,X1] : sP0(X1,X0,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f20])).

fof(f20,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ sP0(X1,X0,k4_xboole_0(sK3,sK2))
      | r2_hidden(sK1,X0)
      | r2_hidden(sK1,sK2) ) ),
    inference(resolution,[],[f111,f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
              & r2_hidden(sK4(X0,X1,X2),X1) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
            & r2_hidden(sK4(X0,X1,X2),X1) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f111,plain,
    ( r2_hidden(sK1,k4_xboole_0(sK3,sK2))
    | r2_hidden(sK1,sK2) ),
    inference(resolution,[],[f110,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | r2_hidden(X2,X0)
      | r2_hidden(X2,k4_xboole_0(X1,X0)) ) ),
    inference(superposition,[],[f53,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f110,plain,(
    r2_hidden(sK1,k2_xboole_0(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f108,f97])).

fof(f97,plain,(
    ~ v3_setfam_1(k2_xboole_0(sK2,sK3),sK1) ),
    inference(backward_demodulation,[],[f37,f95])).

fof(f95,plain,(
    k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3) = k2_xboole_0(sK2,sK3) ),
    inference(resolution,[],[f63,f36])).

fof(f63,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1)))
      | k4_subset_1(k1_zfmisc_1(sK1),sK2,X0) = k2_xboole_0(sK2,X0) ) ),
    inference(resolution,[],[f44,f34])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f37,plain,(
    ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f108,plain,
    ( r2_hidden(sK1,k2_xboole_0(sK2,sK3))
    | v3_setfam_1(k2_xboole_0(sK2,sK3),sK1) ),
    inference(resolution,[],[f106,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | r2_hidden(X0,X1)
      | v3_setfam_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f106,plain,(
    m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(subsumption_resolution,[],[f105,f34])).

fof(f105,plain,
    ( m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(subsumption_resolution,[],[f104,f36])).

fof(f104,plain,
    ( m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(superposition,[],[f43,f95])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:59:59 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.36  ipcrm: permission denied for id (810614784)
% 0.22/0.37  ipcrm: permission denied for id (813727747)
% 0.22/0.37  ipcrm: permission denied for id (810680324)
% 0.22/0.37  ipcrm: permission denied for id (813760517)
% 0.22/0.37  ipcrm: permission denied for id (817692678)
% 0.22/0.37  ipcrm: permission denied for id (810713096)
% 0.22/0.38  ipcrm: permission denied for id (813858825)
% 0.22/0.38  ipcrm: permission denied for id (813891594)
% 0.22/0.38  ipcrm: permission denied for id (813924363)
% 0.22/0.38  ipcrm: permission denied for id (813957132)
% 0.22/0.38  ipcrm: permission denied for id (810844173)
% 0.22/0.38  ipcrm: permission denied for id (810876942)
% 0.22/0.38  ipcrm: permission denied for id (810909711)
% 0.22/0.38  ipcrm: permission denied for id (813989904)
% 0.22/0.38  ipcrm: permission denied for id (816513041)
% 0.22/0.39  ipcrm: permission denied for id (816545810)
% 0.22/0.39  ipcrm: permission denied for id (814088211)
% 0.22/0.39  ipcrm: permission denied for id (814153749)
% 0.22/0.39  ipcrm: permission denied for id (814186518)
% 0.22/0.39  ipcrm: permission denied for id (811073559)
% 0.22/0.39  ipcrm: permission denied for id (816611352)
% 0.22/0.39  ipcrm: permission denied for id (811139097)
% 0.22/0.40  ipcrm: permission denied for id (814252058)
% 0.22/0.40  ipcrm: permission denied for id (814284827)
% 0.22/0.40  ipcrm: permission denied for id (816644124)
% 0.22/0.40  ipcrm: permission denied for id (814350365)
% 0.22/0.40  ipcrm: permission denied for id (811204638)
% 0.22/0.40  ipcrm: permission denied for id (811237407)
% 0.22/0.40  ipcrm: permission denied for id (811270176)
% 0.22/0.40  ipcrm: permission denied for id (814383137)
% 0.22/0.41  ipcrm: permission denied for id (816676898)
% 0.22/0.41  ipcrm: permission denied for id (811335715)
% 0.22/0.41  ipcrm: permission denied for id (811368484)
% 0.22/0.41  ipcrm: permission denied for id (811401253)
% 0.22/0.41  ipcrm: permission denied for id (811434022)
% 0.22/0.41  ipcrm: permission denied for id (817791015)
% 0.22/0.41  ipcrm: permission denied for id (816742440)
% 0.22/0.41  ipcrm: permission denied for id (816775209)
% 0.22/0.42  ipcrm: permission denied for id (814612522)
% 0.22/0.42  ipcrm: permission denied for id (814645291)
% 0.22/0.42  ipcrm: permission denied for id (814678060)
% 0.22/0.42  ipcrm: permission denied for id (811565101)
% 0.22/0.42  ipcrm: permission denied for id (814710830)
% 0.22/0.42  ipcrm: permission denied for id (816807983)
% 0.22/0.42  ipcrm: permission denied for id (811630640)
% 0.22/0.42  ipcrm: permission denied for id (817823793)
% 0.22/0.43  ipcrm: permission denied for id (814809138)
% 0.22/0.43  ipcrm: permission denied for id (811696179)
% 0.22/0.43  ipcrm: permission denied for id (817856564)
% 0.22/0.43  ipcrm: permission denied for id (811761717)
% 0.22/0.43  ipcrm: permission denied for id (814874678)
% 0.22/0.43  ipcrm: permission denied for id (811827255)
% 0.22/0.43  ipcrm: permission denied for id (814907448)
% 0.22/0.44  ipcrm: permission denied for id (811892793)
% 0.22/0.44  ipcrm: permission denied for id (814940218)
% 0.22/0.44  ipcrm: permission denied for id (811925563)
% 0.22/0.44  ipcrm: permission denied for id (816939069)
% 0.22/0.44  ipcrm: permission denied for id (817922110)
% 0.22/0.44  ipcrm: permission denied for id (817037376)
% 0.22/0.44  ipcrm: permission denied for id (815136833)
% 0.22/0.45  ipcrm: permission denied for id (815169602)
% 0.22/0.45  ipcrm: permission denied for id (817070147)
% 0.22/0.45  ipcrm: permission denied for id (812122180)
% 0.22/0.45  ipcrm: permission denied for id (812154950)
% 0.22/0.45  ipcrm: permission denied for id (812187719)
% 0.22/0.45  ipcrm: permission denied for id (812220488)
% 0.22/0.45  ipcrm: permission denied for id (812253257)
% 0.22/0.46  ipcrm: permission denied for id (812318795)
% 0.22/0.46  ipcrm: permission denied for id (815300684)
% 0.22/0.46  ipcrm: permission denied for id (817168461)
% 0.22/0.46  ipcrm: permission denied for id (815366222)
% 0.22/0.46  ipcrm: permission denied for id (815431760)
% 0.22/0.46  ipcrm: permission denied for id (818085969)
% 0.22/0.47  ipcrm: permission denied for id (812384338)
% 0.22/0.47  ipcrm: permission denied for id (812417107)
% 0.22/0.47  ipcrm: permission denied for id (815497300)
% 0.22/0.47  ipcrm: permission denied for id (815530069)
% 0.22/0.47  ipcrm: permission denied for id (815562838)
% 0.22/0.47  ipcrm: permission denied for id (812548183)
% 0.22/0.48  ipcrm: permission denied for id (815595608)
% 0.22/0.48  ipcrm: permission denied for id (817266777)
% 0.22/0.48  ipcrm: permission denied for id (812613722)
% 0.22/0.48  ipcrm: permission denied for id (818118747)
% 0.22/0.48  ipcrm: permission denied for id (817332316)
% 0.22/0.48  ipcrm: permission denied for id (812744797)
% 0.22/0.49  ipcrm: permission denied for id (815726686)
% 0.22/0.49  ipcrm: permission denied for id (817365087)
% 0.22/0.49  ipcrm: permission denied for id (812810336)
% 0.22/0.49  ipcrm: permission denied for id (812843105)
% 0.22/0.49  ipcrm: permission denied for id (812875874)
% 0.22/0.49  ipcrm: permission denied for id (812908643)
% 0.22/0.49  ipcrm: permission denied for id (812941412)
% 0.22/0.50  ipcrm: permission denied for id (812974181)
% 0.22/0.50  ipcrm: permission denied for id (813006950)
% 0.22/0.50  ipcrm: permission denied for id (817397863)
% 0.22/0.50  ipcrm: permission denied for id (815825000)
% 0.22/0.50  ipcrm: permission denied for id (813105257)
% 0.22/0.50  ipcrm: permission denied for id (817430634)
% 0.22/0.51  ipcrm: permission denied for id (813138027)
% 0.22/0.51  ipcrm: permission denied for id (815890540)
% 0.22/0.51  ipcrm: permission denied for id (813203565)
% 0.22/0.51  ipcrm: permission denied for id (817463406)
% 0.22/0.51  ipcrm: permission denied for id (813269104)
% 0.22/0.52  ipcrm: permission denied for id (816021618)
% 0.22/0.52  ipcrm: permission denied for id (813334643)
% 0.22/0.52  ipcrm: permission denied for id (816054388)
% 0.22/0.52  ipcrm: permission denied for id (816087157)
% 0.22/0.52  ipcrm: permission denied for id (813400182)
% 0.22/0.52  ipcrm: permission denied for id (816119927)
% 0.22/0.53  ipcrm: permission denied for id (816152696)
% 0.22/0.53  ipcrm: permission denied for id (816185465)
% 0.22/0.53  ipcrm: permission denied for id (816218234)
% 0.22/0.53  ipcrm: permission denied for id (817561723)
% 0.22/0.53  ipcrm: permission denied for id (816283772)
% 0.22/0.53  ipcrm: permission denied for id (818217085)
% 0.22/0.54  ipcrm: permission denied for id (816349310)
% 0.22/0.54  ipcrm: permission denied for id (813629567)
% 0.41/0.73  % (13976)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.41/0.73  % (13971)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.41/0.73  % (13992)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.41/0.74  % (13982)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.41/0.74  % (13971)Refutation found. Thanks to Tanya!
% 0.41/0.74  % SZS status Theorem for theBenchmark
% 0.41/0.74  % (13974)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.41/0.74  % (13987)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.41/0.75  % (13979)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.41/0.75  % (13990)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.41/0.75  % (13984)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.41/0.76  % SZS output start Proof for theBenchmark
% 0.41/0.76  fof(f176,plain,(
% 0.41/0.76    $false),
% 0.41/0.76    inference(subsumption_resolution,[],[f175,f34])).
% 0.41/0.76  fof(f34,plain,(
% 0.41/0.76    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 0.41/0.76    inference(cnf_transformation,[],[f24])).
% 0.41/0.76  fof(f24,plain,(
% 0.41/0.76    (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),sK1) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) & v3_setfam_1(sK3,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) & v3_setfam_1(sK2,sK1)),
% 0.41/0.76    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f13,f23,f22])).
% 0.41/0.76  fof(f22,plain,(
% 0.41/0.76    ? [X0,X1] : (? [X2] : (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X1,X0)) => (? [X2] : (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK1),sK2,X2),sK1) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK1))) & v3_setfam_1(X2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) & v3_setfam_1(sK2,sK1))),
% 0.41/0.76    introduced(choice_axiom,[])).
% 0.41/0.76  fof(f23,plain,(
% 0.41/0.76    ? [X2] : (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK1),sK2,X2),sK1) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK1))) & v3_setfam_1(X2,sK1)) => (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),sK1) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) & v3_setfam_1(sK3,sK1))),
% 0.41/0.76    introduced(choice_axiom,[])).
% 0.41/0.76  fof(f13,plain,(
% 0.41/0.76    ? [X0,X1] : (? [X2] : (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X1,X0))),
% 0.41/0.76    inference(flattening,[],[f12])).
% 0.41/0.76  fof(f12,plain,(
% 0.41/0.76    ? [X0,X1] : (? [X2] : (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) & (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X2,X0))) & (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X1,X0)))),
% 0.41/0.76    inference(ennf_transformation,[],[f11])).
% 0.41/0.77  fof(f11,plain,(
% 0.41/0.77    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X1,X0)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X2,X0)) => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0)))),
% 0.41/0.77    inference(pure_predicate_removal,[],[f10])).
% 0.41/0.77  fof(f10,negated_conjecture,(
% 0.41/0.77    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X1,X0)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X2,X0)) => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0))))),
% 0.41/0.77    inference(negated_conjecture,[],[f9])).
% 0.41/0.77  fof(f9,conjecture,(
% 0.41/0.77    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X1,X0)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X2,X0)) => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0))))),
% 0.41/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_setfam_1)).
% 0.41/0.77  fof(f175,plain,(
% 0.41/0.77    ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 0.41/0.77    inference(subsumption_resolution,[],[f168,f33])).
% 0.41/0.77  fof(f33,plain,(
% 0.41/0.77    v3_setfam_1(sK2,sK1)),
% 0.41/0.77    inference(cnf_transformation,[],[f24])).
% 0.41/0.77  fof(f168,plain,(
% 0.41/0.77    ~v3_setfam_1(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 0.41/0.77    inference(resolution,[],[f167,f41])).
% 0.41/0.77  fof(f41,plain,(
% 0.41/0.77    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v3_setfam_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.41/0.77    inference(cnf_transformation,[],[f25])).
% 0.41/0.77  fof(f25,plain,(
% 0.41/0.77    ! [X0,X1] : (((v3_setfam_1(X1,X0) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | ~v3_setfam_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.41/0.77    inference(nnf_transformation,[],[f14])).
% 0.41/0.77  fof(f14,plain,(
% 0.41/0.77    ! [X0,X1] : ((v3_setfam_1(X1,X0) <=> ~r2_hidden(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.41/0.77    inference(ennf_transformation,[],[f8])).
% 0.41/0.77  fof(f8,axiom,(
% 0.41/0.77    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (v3_setfam_1(X1,X0) <=> ~r2_hidden(X0,X1)))),
% 0.41/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_setfam_1)).
% 0.41/0.77  fof(f167,plain,(
% 0.41/0.77    r2_hidden(sK1,sK2)),
% 0.41/0.77    inference(subsumption_resolution,[],[f166,f36])).
% 0.41/0.77  fof(f36,plain,(
% 0.41/0.77    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 0.41/0.77    inference(cnf_transformation,[],[f24])).
% 0.41/0.77  fof(f166,plain,(
% 0.41/0.77    r2_hidden(sK1,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 0.41/0.77    inference(subsumption_resolution,[],[f159,f35])).
% 0.41/0.77  fof(f35,plain,(
% 0.41/0.77    v3_setfam_1(sK3,sK1)),
% 0.41/0.77    inference(cnf_transformation,[],[f24])).
% 0.41/0.77  fof(f159,plain,(
% 0.41/0.77    r2_hidden(sK1,sK2) | ~v3_setfam_1(sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 0.41/0.77    inference(resolution,[],[f158,f41])).
% 0.41/0.77  fof(f158,plain,(
% 0.41/0.77    r2_hidden(sK1,sK3) | r2_hidden(sK1,sK2)),
% 0.41/0.77    inference(resolution,[],[f120,f57])).
% 0.41/0.77  fof(f57,plain,(
% 0.41/0.77    ( ! [X0,X1] : (sP0(X1,X0,k4_xboole_0(X0,X1))) )),
% 0.41/0.77    inference(equality_resolution,[],[f51])).
% 0.41/0.77  fof(f51,plain,(
% 0.41/0.77    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.41/0.77    inference(cnf_transformation,[],[f31])).
% 0.41/0.77  fof(f31,plain,(
% 0.41/0.77    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2))),
% 0.41/0.77    inference(nnf_transformation,[],[f21])).
% 0.41/0.77  fof(f21,plain,(
% 0.41/0.77    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 0.41/0.77    inference(definition_folding,[],[f1,f20])).
% 0.41/0.77  fof(f20,plain,(
% 0.41/0.77    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.41/0.77    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.41/0.77  fof(f1,axiom,(
% 0.41/0.77    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.41/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.41/0.77  fof(f120,plain,(
% 0.41/0.77    ( ! [X0,X1] : (~sP0(X1,X0,k4_xboole_0(sK3,sK2)) | r2_hidden(sK1,X0) | r2_hidden(sK1,sK2)) )),
% 0.41/0.77    inference(resolution,[],[f111,f45])).
% 0.41/0.77  fof(f45,plain,(
% 0.41/0.77    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~sP0(X0,X1,X2)) )),
% 0.41/0.77    inference(cnf_transformation,[],[f30])).
% 0.41/0.77  fof(f30,plain,(
% 0.41/0.77    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X0) & r2_hidden(sK4(X0,X1,X2),X1)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.41/0.77    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).
% 0.41/0.77  fof(f29,plain,(
% 0.41/0.77    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X0) & r2_hidden(sK4(X0,X1,X2),X1)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.41/0.77    introduced(choice_axiom,[])).
% 0.41/0.77  fof(f28,plain,(
% 0.41/0.77    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.41/0.77    inference(rectify,[],[f27])).
% 0.41/0.77  fof(f27,plain,(
% 0.41/0.77    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.41/0.77    inference(flattening,[],[f26])).
% 0.41/0.77  fof(f26,plain,(
% 0.41/0.77    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.41/0.77    inference(nnf_transformation,[],[f20])).
% 0.41/0.77  fof(f111,plain,(
% 0.41/0.77    r2_hidden(sK1,k4_xboole_0(sK3,sK2)) | r2_hidden(sK1,sK2)),
% 0.41/0.77    inference(resolution,[],[f110,f61])).
% 0.41/0.77  fof(f61,plain,(
% 0.41/0.77    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_xboole_0(X0,X1)) | r2_hidden(X2,X0) | r2_hidden(X2,k4_xboole_0(X1,X0))) )),
% 0.41/0.77    inference(superposition,[],[f53,f40])).
% 0.41/0.77  fof(f40,plain,(
% 0.41/0.77    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.41/0.77    inference(cnf_transformation,[],[f3])).
% 0.41/0.77  fof(f3,axiom,(
% 0.41/0.77    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.41/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.41/0.77  fof(f53,plain,(
% 0.41/0.77    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | r2_hidden(X0,X2)) )),
% 0.41/0.77    inference(cnf_transformation,[],[f32])).
% 0.41/0.77  fof(f32,plain,(
% 0.41/0.77    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 0.41/0.77    inference(nnf_transformation,[],[f19])).
% 0.41/0.77  fof(f19,plain,(
% 0.41/0.77    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 0.41/0.77    inference(ennf_transformation,[],[f2])).
% 0.41/0.77  fof(f2,axiom,(
% 0.41/0.77    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 0.41/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 0.41/0.77  fof(f110,plain,(
% 0.41/0.77    r2_hidden(sK1,k2_xboole_0(sK2,sK3))),
% 0.41/0.77    inference(subsumption_resolution,[],[f108,f97])).
% 0.41/0.77  fof(f97,plain,(
% 0.41/0.77    ~v3_setfam_1(k2_xboole_0(sK2,sK3),sK1)),
% 0.41/0.77    inference(backward_demodulation,[],[f37,f95])).
% 0.41/0.77  fof(f95,plain,(
% 0.41/0.77    k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3) = k2_xboole_0(sK2,sK3)),
% 0.41/0.77    inference(resolution,[],[f63,f36])).
% 0.41/0.77  fof(f63,plain,(
% 0.41/0.77    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) | k4_subset_1(k1_zfmisc_1(sK1),sK2,X0) = k2_xboole_0(sK2,X0)) )),
% 0.41/0.77    inference(resolution,[],[f44,f34])).
% 0.41/0.77  fof(f44,plain,(
% 0.41/0.77    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)) )),
% 0.41/0.77    inference(cnf_transformation,[],[f18])).
% 0.41/0.77  fof(f18,plain,(
% 0.41/0.77    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.41/0.77    inference(flattening,[],[f17])).
% 0.41/0.77  fof(f17,plain,(
% 0.41/0.77    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.41/0.77    inference(ennf_transformation,[],[f7])).
% 0.41/0.77  fof(f7,axiom,(
% 0.41/0.77    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.41/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.41/0.77  fof(f37,plain,(
% 0.41/0.77    ~v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),sK1)),
% 0.41/0.77    inference(cnf_transformation,[],[f24])).
% 0.41/0.77  fof(f108,plain,(
% 0.41/0.77    r2_hidden(sK1,k2_xboole_0(sK2,sK3)) | v3_setfam_1(k2_xboole_0(sK2,sK3),sK1)),
% 0.41/0.77    inference(resolution,[],[f106,f42])).
% 0.41/0.77  fof(f42,plain,(
% 0.41/0.77    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | r2_hidden(X0,X1) | v3_setfam_1(X1,X0)) )),
% 0.41/0.77    inference(cnf_transformation,[],[f25])).
% 0.41/0.77  fof(f106,plain,(
% 0.41/0.77    m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 0.41/0.77    inference(subsumption_resolution,[],[f105,f34])).
% 0.41/0.77  fof(f105,plain,(
% 0.41/0.77    m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 0.41/0.77    inference(subsumption_resolution,[],[f104,f36])).
% 0.41/0.77  fof(f104,plain,(
% 0.41/0.77    m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 0.41/0.77    inference(superposition,[],[f43,f95])).
% 0.41/0.77  fof(f43,plain,(
% 0.41/0.77    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.41/0.77    inference(cnf_transformation,[],[f16])).
% 0.41/0.77  fof(f16,plain,(
% 0.41/0.77    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.41/0.77    inference(flattening,[],[f15])).
% 0.41/0.77  fof(f15,plain,(
% 0.41/0.77    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.41/0.77    inference(ennf_transformation,[],[f6])).
% 0.41/0.77  fof(f6,axiom,(
% 0.41/0.77    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.41/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 0.41/0.77  % SZS output end Proof for theBenchmark
% 0.41/0.77  % (13971)------------------------------
% 0.41/0.77  % (13971)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.41/0.77  % (13971)Termination reason: Refutation
% 0.41/0.77  
% 0.41/0.77  % (13971)Memory used [KB]: 6396
% 0.41/0.77  % (13971)Time elapsed: 0.135 s
% 0.41/0.77  % (13971)------------------------------
% 0.41/0.77  % (13971)------------------------------
% 0.48/0.77  % (13793)Success in time 0.407 s
%------------------------------------------------------------------------------
