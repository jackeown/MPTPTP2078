%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1081+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:14 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   53 (  99 expanded)
%              Number of leaves         :   10 (  28 expanded)
%              Depth                    :   20
%              Number of atoms          :  204 ( 412 expanded)
%              Number of equality atoms :   34 (  34 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f103,plain,(
    $false ),
    inference(subsumption_resolution,[],[f102,f31])).

fof(f31,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f102,plain,(
    v1_xboole_0(k1_tarski(sK4)) ),
    inference(resolution,[],[f101,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X0,X1)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( sP1(X2,X0,X1)
      | v1_xboole_0(X2) ) ),
    inference(definition_folding,[],[f11,f13,f12])).

fof(f12,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ m1_subset_1(X3,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( ( m1_funct_2(X2,X0,X1)
      <=> sP0(X1,X0,X2) )
      | ~ sP1(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( m1_funct_2(X2,X0,X1)
      <=> ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
            | ~ m1_subset_1(X3,X2) ) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ( m1_funct_2(X2,X0,X1)
      <=> ! [X3] :
            ( m1_subset_1(X3,X2)
           => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_2)).

fof(f101,plain,(
    ~ sP1(k1_tarski(sK4),sK2,sK3) ),
    inference(subsumption_resolution,[],[f98,f30])).

fof(f30,plain,(
    ~ m1_funct_2(k1_tarski(sK4),sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ m1_funct_2(k1_tarski(sK4),sK2,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f8,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ~ m1_funct_2(k1_tarski(X2),X0,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ~ m1_funct_2(k1_tarski(sK4),sK2,sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK4,sK2,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ m1_funct_2(k1_tarski(X2),X0,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ m1_funct_2(k1_tarski(X2),X0,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => m1_funct_2(k1_tarski(X2),X0,X1) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => m1_funct_2(k1_tarski(X2),X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t198_funct_2)).

fof(f98,plain,
    ( m1_funct_2(k1_tarski(sK4),sK2,sK3)
    | ~ sP1(k1_tarski(sK4),sK2,sK3) ),
    inference(resolution,[],[f96,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X2,X1,X0)
      | m1_funct_2(X0,X1,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( m1_funct_2(X0,X1,X2)
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ m1_funct_2(X0,X1,X2) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ( ( m1_funct_2(X2,X0,X1)
          | ~ sP0(X1,X0,X2) )
        & ( sP0(X1,X0,X2)
          | ~ m1_funct_2(X2,X0,X1) ) )
      | ~ sP1(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f96,plain,(
    sP0(sK3,sK2,k1_tarski(sK4)) ),
    inference(subsumption_resolution,[],[f95,f28])).

fof(f28,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f95,plain,
    ( ~ v1_funct_2(sK4,sK2,sK3)
    | sP0(sK3,sK2,k1_tarski(sK4)) ),
    inference(subsumption_resolution,[],[f94,f29])).

fof(f29,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f16])).

fof(f94,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | sP0(sK3,sK2,k1_tarski(sK4)) ),
    inference(subsumption_resolution,[],[f92,f27])).

fof(f27,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f16])).

fof(f92,plain,
    ( ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | sP0(sK3,sK2,k1_tarski(sK4)) ),
    inference(superposition,[],[f43,f91])).

fof(f91,plain,(
    sK4 = sK6(sK3,sK2,k1_tarski(sK4)) ),
    inference(resolution,[],[f90,f30])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( m1_funct_2(k1_tarski(X0),X1,X2)
      | sK6(X2,X1,k1_tarski(X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f89,f31])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( m1_funct_2(k1_tarski(X0),X1,X2)
      | sK6(X2,X1,k1_tarski(X0)) = X0
      | v1_xboole_0(k1_tarski(X0)) ) ),
    inference(resolution,[],[f53,f44])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(k1_tarski(X2),X1,X0)
      | m1_funct_2(k1_tarski(X2),X1,X0)
      | sK6(X0,X1,k1_tarski(X2)) = X2 ) ),
    inference(resolution,[],[f52,f38])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,k1_tarski(X2))
      | sK6(X0,X1,k1_tarski(X2)) = X2 ) ),
    inference(resolution,[],[f42,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_tarski(X0))
      | X0 = X1 ) ),
    inference(subsumption_resolution,[],[f50,f31])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_tarski(X0))
      | ~ m1_subset_1(X1,k1_tarski(X0))
      | X0 = X1 ) ),
    inference(resolution,[],[f32,f47])).

fof(f47,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f18,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
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
    inference(rectify,[],[f17])).

fof(f17,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ~ m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            | ~ v1_funct_2(sK6(X0,X1,X2),X1,X0)
            | ~ v1_funct_1(sK6(X0,X1,X2)) )
          & m1_subset_1(sK6(X0,X1,X2),X2) ) )
      & ( ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X4,X1,X0)
              & v1_funct_1(X4) )
            | ~ m1_subset_1(X4,X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f24,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            | ~ v1_funct_2(X3,X1,X0)
            | ~ v1_funct_1(X3) )
          & m1_subset_1(X3,X2) )
     => ( ( ~ m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(sK6(X0,X1,X2),X1,X0)
          | ~ v1_funct_1(sK6(X0,X1,X2)) )
        & m1_subset_1(sK6(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              | ~ v1_funct_2(X3,X1,X0)
              | ~ v1_funct_1(X3) )
            & m1_subset_1(X3,X2) ) )
      & ( ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X4,X1,X0)
              & v1_funct_1(X4) )
            | ~ m1_subset_1(X4,X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X3,X0,X1)
              | ~ v1_funct_1(X3) )
            & m1_subset_1(X3,X2) ) )
      & ( ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
            | ~ m1_subset_1(X3,X2) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(sK6(X0,X1,X2))
      | ~ m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(sK6(X0,X1,X2),X1,X0)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

%------------------------------------------------------------------------------
