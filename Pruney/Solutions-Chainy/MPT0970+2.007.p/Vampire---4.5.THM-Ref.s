%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  124 (4244 expanded)
%              Number of leaves         :   21 (1256 expanded)
%              Depth                    :   29
%              Number of atoms          :  440 (21518 expanded)
%              Number of equality atoms :  159 (6242 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f385,plain,(
    $false ),
    inference(subsumption_resolution,[],[f384,f300])).

fof(f300,plain,(
    k1_xboole_0 != k1_relat_1(sK5) ),
    inference(subsumption_resolution,[],[f111,f276])).

fof(f276,plain,(
    k1_xboole_0 != k2_relat_1(sK5) ),
    inference(backward_demodulation,[],[f135,f262])).

fof(f262,plain,(
    k1_xboole_0 = sK4 ),
    inference(subsumption_resolution,[],[f259,f136])).

fof(f136,plain,(
    ~ r1_tarski(sK4,k2_relat_1(sK5)) ),
    inference(subsumption_resolution,[],[f115,f135])).

fof(f115,plain,
    ( ~ r1_tarski(sK4,k2_relat_1(sK5))
    | sK4 = k2_relat_1(sK5) ),
    inference(resolution,[],[f113,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f113,plain,(
    r1_tarski(k2_relat_1(sK5),sK4) ),
    inference(subsumption_resolution,[],[f112,f104])).

fof(f104,plain,(
    v1_relat_1(sK5) ),
    inference(resolution,[],[f81,f56])).

fof(f56,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( sK4 != k2_relset_1(sK3,sK4,sK5)
    & ! [X3] :
        ( ( k1_funct_1(sK5,sK6(X3)) = X3
          & r2_hidden(sK6(X3),sK3) )
        | ~ r2_hidden(X3,sK4) )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK5,sK3,sK4)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f16,f34,f33])).

fof(f33,plain,
    ( ? [X0,X1,X2] :
        ( k2_relset_1(X0,X1,X2) != X1
        & ! [X3] :
            ( ? [X4] :
                ( k1_funct_1(X2,X4) = X3
                & r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X1) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( sK4 != k2_relset_1(sK3,sK4,sK5)
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(sK5,X4) = X3
              & r2_hidden(X4,sK3) )
          | ~ r2_hidden(X3,sK4) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK5,sK3,sK4)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X3] :
      ( ? [X4] :
          ( k1_funct_1(sK5,X4) = X3
          & r2_hidden(X4,sK3) )
     => ( k1_funct_1(sK5,sK6(X3)) = X3
        & r2_hidden(sK6(X3),sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( ! [X4] :
                    ~ ( k1_funct_1(X2,X4) = X3
                      & r2_hidden(X4,X0) )
                & r2_hidden(X3,X1) )
         => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( ! [X4] :
                  ~ ( k1_funct_1(X2,X4) = X3
                    & r2_hidden(X4,X0) )
              & r2_hidden(X3,X1) )
       => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f112,plain,
    ( r1_tarski(k2_relat_1(sK5),sK4)
    | ~ v1_relat_1(sK5) ),
    inference(resolution,[],[f110,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f110,plain,(
    v5_relat_1(sK5,sK4) ),
    inference(resolution,[],[f84,f56])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f259,plain,
    ( k1_xboole_0 = sK4
    | r1_tarski(sK4,k2_relat_1(sK5)) ),
    inference(resolution,[],[f258,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK10(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK10(X0,X1),X1)
          & r2_hidden(sK10(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f48,f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK10(X0,X1),X1)
        & r2_hidden(sK10(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f258,plain,
    ( r2_hidden(sK10(sK4,k2_relat_1(sK5)),k2_relat_1(sK5))
    | k1_xboole_0 = sK4 ),
    inference(subsumption_resolution,[],[f257,f136])).

fof(f257,plain,
    ( k1_xboole_0 = sK4
    | r2_hidden(sK10(sK4,k2_relat_1(sK5)),k2_relat_1(sK5))
    | r1_tarski(sK4,k2_relat_1(sK5)) ),
    inference(resolution,[],[f256,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK10(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f256,plain,
    ( ~ r2_hidden(sK10(sK4,k2_relat_1(sK5)),sK4)
    | k1_xboole_0 = sK4
    | r2_hidden(sK10(sK4,k2_relat_1(sK5)),k2_relat_1(sK5)) ),
    inference(resolution,[],[f204,f57])).

fof(f57,plain,(
    ! [X3] :
      ( r2_hidden(sK6(X3),sK3)
      | ~ r2_hidden(X3,sK4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f204,plain,
    ( ~ r2_hidden(sK6(sK10(sK4,k2_relat_1(sK5))),sK3)
    | r2_hidden(sK10(sK4,k2_relat_1(sK5)),k2_relat_1(sK5))
    | k1_xboole_0 = sK4 ),
    inference(superposition,[],[f201,f137])).

fof(f137,plain,(
    sK10(sK4,k2_relat_1(sK5)) = k1_funct_1(sK5,sK6(sK10(sK4,k2_relat_1(sK5)))) ),
    inference(resolution,[],[f106,f136])).

fof(f106,plain,(
    ! [X0] :
      ( r1_tarski(sK4,X0)
      | sK10(sK4,X0) = k1_funct_1(sK5,sK6(sK10(sK4,X0))) ) ),
    inference(resolution,[],[f58,f79])).

fof(f58,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK4)
      | k1_funct_1(sK5,sK6(X3)) = X3 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f201,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5))
      | ~ r2_hidden(X0,sK3)
      | k1_xboole_0 = sK4 ) ),
    inference(subsumption_resolution,[],[f200,f104])).

fof(f200,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5))
      | ~ r2_hidden(X0,sK3)
      | k1_xboole_0 = sK4
      | ~ v1_relat_1(sK5) ) ),
    inference(subsumption_resolution,[],[f199,f54])).

fof(f54,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f199,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5))
      | ~ r2_hidden(X0,sK3)
      | k1_xboole_0 = sK4
      | ~ v1_funct_1(sK5)
      | ~ v1_relat_1(sK5) ) ),
    inference(resolution,[],[f198,f101])).

fof(f101,plain,(
    ! [X0] :
      ( sP0(X0,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f92,f72])).

fof(f72,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f19,f29,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( k1_funct_1(X0,X3) = X2
              & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> sP0(X0,X1) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f92,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | sP0(X0,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | k2_relat_1(X0) != X1
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ~ sP0(X0,X1) )
          & ( sP0(X0,X1)
            | k2_relat_1(X0) != X1 ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f198,plain,(
    ! [X2,X3] :
      ( ~ sP0(sK5,X3)
      | r2_hidden(k1_funct_1(sK5,X2),X3)
      | ~ r2_hidden(X2,sK3)
      | k1_xboole_0 = sK4 ) ),
    inference(superposition,[],[f93,f193])).

fof(f193,plain,
    ( sK3 = k1_relat_1(sK5)
    | k1_xboole_0 = sK4 ),
    inference(superposition,[],[f192,f133])).

fof(f133,plain,(
    k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
    inference(resolution,[],[f82,f56])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f192,plain,
    ( sK3 = k1_relset_1(sK3,sK4,sK5)
    | k1_xboole_0 = sK4 ),
    inference(subsumption_resolution,[],[f191,f55])).

fof(f55,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f191,plain,
    ( ~ v1_funct_2(sK5,sK3,sK4)
    | k1_xboole_0 = sK4
    | sK3 = k1_relset_1(sK3,sK4,sK5) ),
    inference(resolution,[],[f85,f118])).

fof(f118,plain,(
    sP2(sK3,sK5,sK4) ),
    inference(resolution,[],[f89,f56])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP2(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP2(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP2(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f27,f31])).

fof(f31,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP2(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 = X2
      | k1_relset_1(X0,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP2(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f93,plain,(
    ! [X6,X0,X1] :
      ( ~ r2_hidden(X6,k1_relat_1(X0))
      | r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ sP0(X0,X1) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != sK7(X0,X1)
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( ( sK7(X0,X1) = k1_funct_1(X0,sK8(X0,X1))
              & r2_hidden(sK8(X0,X1),k1_relat_1(X0)) )
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( k1_funct_1(X0,X6) != X5
                  | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
            & ( ( k1_funct_1(X0,sK9(X0,X5)) = X5
                & r2_hidden(sK9(X0,X5),k1_relat_1(X0)) )
              | ~ r2_hidden(X5,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f39,f42,f41,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK7(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK7(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK7(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK7(X0,X1) = k1_funct_1(X0,sK8(X0,X1))
        & r2_hidden(sK8(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK9(X0,X5)) = X5
        & r2_hidden(sK9(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( ! [X3] :
                  ( k1_funct_1(X0,X3) != X2
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( k1_funct_1(X0,X4) = X2
                  & r2_hidden(X4,k1_relat_1(X0)) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( k1_funct_1(X0,X6) != X5
                  | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
            & ( ? [X7] :
                  ( k1_funct_1(X0,X7) = X5
                  & r2_hidden(X7,k1_relat_1(X0)) )
              | ~ r2_hidden(X5,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( ! [X3] :
                  ( k1_funct_1(X0,X3) != X2
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( k1_funct_1(X0,X3) != X2
                  | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
            & ( ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) )
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f135,plain,(
    sK4 != k2_relat_1(sK5) ),
    inference(superposition,[],[f59,f134])).

fof(f134,plain,(
    k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
    inference(resolution,[],[f83,f56])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f59,plain,(
    sK4 != k2_relset_1(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f111,plain,
    ( k1_xboole_0 != k1_relat_1(sK5)
    | k1_xboole_0 = k2_relat_1(sK5) ),
    inference(resolution,[],[f62,f104])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(f384,plain,(
    k1_xboole_0 = k1_relat_1(sK5) ),
    inference(backward_demodulation,[],[f373,f383])).

fof(f383,plain,(
    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) ),
    inference(subsumption_resolution,[],[f381,f368])).

fof(f368,plain,(
    v1_funct_2(sK5,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f263,f367])).

fof(f367,plain,(
    k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f349,f61])).

fof(f61,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f349,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f276,f332])).

fof(f332,plain,
    ( k1_xboole_0 = sK5
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f326,f263])).

% (7582)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
fof(f326,plain,
    ( ~ v1_funct_2(sK5,sK3,k1_xboole_0)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK5 ),
    inference(resolution,[],[f264,f100])).

fof(f100,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2 ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f264,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f56,f262])).

fof(f263,plain,(
    v1_funct_2(sK5,sK3,k1_xboole_0) ),
    inference(backward_demodulation,[],[f55,f262])).

fof(f381,plain,
    ( ~ v1_funct_2(sK5,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) ),
    inference(resolution,[],[f372,f97])).

fof(f97,plain,(
    ! [X2,X1] :
      ( ~ sP2(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X1,k1_xboole_0,X2)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,X1) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 != X0
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f372,plain,(
    sP2(k1_xboole_0,sK5,k1_xboole_0) ),
    inference(backward_demodulation,[],[f273,f367])).

fof(f273,plain,(
    sP2(sK3,sK5,k1_xboole_0) ),
    inference(backward_demodulation,[],[f118,f262])).

fof(f373,plain,(
    k1_relat_1(sK5) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) ),
    inference(backward_demodulation,[],[f274,f367])).

fof(f274,plain,(
    k1_relat_1(sK5) = k1_relset_1(sK3,k1_xboole_0,sK5) ),
    inference(backward_demodulation,[],[f133,f262])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:34:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (7571)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (7585)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (7563)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (7560)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (7579)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (7569)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (7561)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (7578)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (7564)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (7570)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (7584)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (7562)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (7556)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (7565)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (7559)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.55  % (7567)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (7568)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (7558)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.55  % (7557)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.55  % (7583)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (7581)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (7576)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (7572)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (7563)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f385,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(subsumption_resolution,[],[f384,f300])).
% 0.21/0.55  fof(f300,plain,(
% 0.21/0.55    k1_xboole_0 != k1_relat_1(sK5)),
% 0.21/0.55    inference(subsumption_resolution,[],[f111,f276])).
% 0.21/0.55  fof(f276,plain,(
% 0.21/0.55    k1_xboole_0 != k2_relat_1(sK5)),
% 0.21/0.55    inference(backward_demodulation,[],[f135,f262])).
% 0.21/0.55  fof(f262,plain,(
% 0.21/0.55    k1_xboole_0 = sK4),
% 0.21/0.55    inference(subsumption_resolution,[],[f259,f136])).
% 0.21/0.55  fof(f136,plain,(
% 0.21/0.55    ~r1_tarski(sK4,k2_relat_1(sK5))),
% 0.21/0.55    inference(subsumption_resolution,[],[f115,f135])).
% 0.21/0.55  fof(f115,plain,(
% 0.21/0.55    ~r1_tarski(sK4,k2_relat_1(sK5)) | sK4 = k2_relat_1(sK5)),
% 0.21/0.55    inference(resolution,[],[f113,f77])).
% 0.21/0.55  fof(f77,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.55    inference(cnf_transformation,[],[f46])).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.55    inference(flattening,[],[f45])).
% 0.21/0.55  fof(f45,plain,(
% 0.21/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.55    inference(nnf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.55  fof(f113,plain,(
% 0.21/0.55    r1_tarski(k2_relat_1(sK5),sK4)),
% 0.21/0.55    inference(subsumption_resolution,[],[f112,f104])).
% 0.21/0.55  fof(f104,plain,(
% 0.21/0.55    v1_relat_1(sK5)),
% 0.21/0.55    inference(resolution,[],[f81,f56])).
% 0.21/0.55  fof(f56,plain,(
% 0.21/0.55    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 0.21/0.55    inference(cnf_transformation,[],[f35])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    sK4 != k2_relset_1(sK3,sK4,sK5) & ! [X3] : ((k1_funct_1(sK5,sK6(X3)) = X3 & r2_hidden(sK6(X3),sK3)) | ~r2_hidden(X3,sK4)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f16,f34,f33])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (sK4 != k2_relset_1(sK3,sK4,sK5) & ! [X3] : (? [X4] : (k1_funct_1(sK5,X4) = X3 & r2_hidden(X4,sK3)) | ~r2_hidden(X3,sK4)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ! [X3] : (? [X4] : (k1_funct_1(sK5,X4) = X3 & r2_hidden(X4,sK3)) => (k1_funct_1(sK5,sK6(X3)) = X3 & r2_hidden(sK6(X3),sK3)))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.55    inference(flattening,[],[f15])).
% 0.21/0.55  fof(f15,plain,(
% 0.21/0.55    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.55    inference(ennf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.21/0.55    inference(negated_conjecture,[],[f12])).
% 0.21/0.55  fof(f12,conjecture,(
% 0.21/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).
% 0.21/0.55  fof(f81,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.55    inference(ennf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.55  fof(f112,plain,(
% 0.21/0.55    r1_tarski(k2_relat_1(sK5),sK4) | ~v1_relat_1(sK5)),
% 0.21/0.55    inference(resolution,[],[f110,f73])).
% 0.21/0.55  fof(f73,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f44])).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.55    inference(nnf_transformation,[],[f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.55  fof(f110,plain,(
% 0.21/0.55    v5_relat_1(sK5,sK4)),
% 0.21/0.55    inference(resolution,[],[f84,f56])).
% 0.21/0.55  fof(f84,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.55    inference(ennf_transformation,[],[f14])).
% 0.21/0.55  fof(f14,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.21/0.55    inference(pure_predicate_removal,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.55  fof(f259,plain,(
% 0.21/0.55    k1_xboole_0 = sK4 | r1_tarski(sK4,k2_relat_1(sK5))),
% 0.21/0.55    inference(resolution,[],[f258,f80])).
% 0.21/0.55  fof(f80,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(sK10(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f50])).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK10(X0,X1),X1) & r2_hidden(sK10(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f48,f49])).
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK10(X0,X1),X1) & r2_hidden(sK10(X0,X1),X0)))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f48,plain,(
% 0.21/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.55    inference(rectify,[],[f47])).
% 0.21/0.55  fof(f47,plain,(
% 0.21/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.55    inference(nnf_transformation,[],[f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.55  fof(f258,plain,(
% 0.21/0.55    r2_hidden(sK10(sK4,k2_relat_1(sK5)),k2_relat_1(sK5)) | k1_xboole_0 = sK4),
% 0.21/0.55    inference(subsumption_resolution,[],[f257,f136])).
% 0.21/0.55  fof(f257,plain,(
% 0.21/0.55    k1_xboole_0 = sK4 | r2_hidden(sK10(sK4,k2_relat_1(sK5)),k2_relat_1(sK5)) | r1_tarski(sK4,k2_relat_1(sK5))),
% 0.21/0.55    inference(resolution,[],[f256,f79])).
% 0.21/0.55  fof(f79,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r2_hidden(sK10(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f50])).
% 0.21/0.55  fof(f256,plain,(
% 0.21/0.55    ~r2_hidden(sK10(sK4,k2_relat_1(sK5)),sK4) | k1_xboole_0 = sK4 | r2_hidden(sK10(sK4,k2_relat_1(sK5)),k2_relat_1(sK5))),
% 0.21/0.55    inference(resolution,[],[f204,f57])).
% 0.21/0.55  fof(f57,plain,(
% 0.21/0.55    ( ! [X3] : (r2_hidden(sK6(X3),sK3) | ~r2_hidden(X3,sK4)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f35])).
% 0.21/0.55  fof(f204,plain,(
% 0.21/0.55    ~r2_hidden(sK6(sK10(sK4,k2_relat_1(sK5))),sK3) | r2_hidden(sK10(sK4,k2_relat_1(sK5)),k2_relat_1(sK5)) | k1_xboole_0 = sK4),
% 0.21/0.55    inference(superposition,[],[f201,f137])).
% 0.21/0.55  fof(f137,plain,(
% 0.21/0.55    sK10(sK4,k2_relat_1(sK5)) = k1_funct_1(sK5,sK6(sK10(sK4,k2_relat_1(sK5))))),
% 0.21/0.55    inference(resolution,[],[f106,f136])).
% 0.21/0.55  fof(f106,plain,(
% 0.21/0.55    ( ! [X0] : (r1_tarski(sK4,X0) | sK10(sK4,X0) = k1_funct_1(sK5,sK6(sK10(sK4,X0)))) )),
% 0.21/0.55    inference(resolution,[],[f58,f79])).
% 0.21/0.55  fof(f58,plain,(
% 0.21/0.55    ( ! [X3] : (~r2_hidden(X3,sK4) | k1_funct_1(sK5,sK6(X3)) = X3) )),
% 0.21/0.55    inference(cnf_transformation,[],[f35])).
% 0.21/0.55  fof(f201,plain,(
% 0.21/0.55    ( ! [X0] : (r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) | ~r2_hidden(X0,sK3) | k1_xboole_0 = sK4) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f200,f104])).
% 0.21/0.55  fof(f200,plain,(
% 0.21/0.55    ( ! [X0] : (r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) | ~r2_hidden(X0,sK3) | k1_xboole_0 = sK4 | ~v1_relat_1(sK5)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f199,f54])).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    v1_funct_1(sK5)),
% 0.21/0.55    inference(cnf_transformation,[],[f35])).
% 0.21/0.55  fof(f199,plain,(
% 0.21/0.55    ( ! [X0] : (r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) | ~r2_hidden(X0,sK3) | k1_xboole_0 = sK4 | ~v1_funct_1(sK5) | ~v1_relat_1(sK5)) )),
% 0.21/0.55    inference(resolution,[],[f198,f101])).
% 0.21/0.55  fof(f101,plain,(
% 0.21/0.55    ( ! [X0] : (sP0(X0,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.55    inference(resolution,[],[f92,f72])).
% 0.21/0.55  fof(f72,plain,(
% 0.21/0.55    ( ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(definition_folding,[],[f19,f29,f28])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0)))))),
% 0.21/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> sP0(X0,X1)) | ~sP1(X0))),
% 0.21/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(flattening,[],[f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 0.21/0.55  fof(f92,plain,(
% 0.21/0.55    ( ! [X0] : (~sP1(X0) | sP0(X0,k2_relat_1(X0))) )),
% 0.21/0.55    inference(equality_resolution,[],[f64])).
% 0.21/0.55  fof(f64,plain,(
% 0.21/0.55    ( ! [X0,X1] : (sP0(X0,X1) | k2_relat_1(X0) != X1 | ~sP1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f37])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ~sP0(X0,X1)) & (sP0(X0,X1) | k2_relat_1(X0) != X1)) | ~sP1(X0))),
% 0.21/0.55    inference(nnf_transformation,[],[f29])).
% 0.21/0.55  fof(f198,plain,(
% 0.21/0.55    ( ! [X2,X3] : (~sP0(sK5,X3) | r2_hidden(k1_funct_1(sK5,X2),X3) | ~r2_hidden(X2,sK3) | k1_xboole_0 = sK4) )),
% 0.21/0.55    inference(superposition,[],[f93,f193])).
% 0.21/0.55  fof(f193,plain,(
% 0.21/0.55    sK3 = k1_relat_1(sK5) | k1_xboole_0 = sK4),
% 0.21/0.55    inference(superposition,[],[f192,f133])).
% 0.21/0.55  fof(f133,plain,(
% 0.21/0.55    k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5)),
% 0.21/0.55    inference(resolution,[],[f82,f56])).
% 0.21/0.55  fof(f82,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.55    inference(ennf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.55  fof(f192,plain,(
% 0.21/0.55    sK3 = k1_relset_1(sK3,sK4,sK5) | k1_xboole_0 = sK4),
% 0.21/0.55    inference(subsumption_resolution,[],[f191,f55])).
% 0.21/0.55  fof(f55,plain,(
% 0.21/0.55    v1_funct_2(sK5,sK3,sK4)),
% 0.21/0.55    inference(cnf_transformation,[],[f35])).
% 0.21/0.55  fof(f191,plain,(
% 0.21/0.55    ~v1_funct_2(sK5,sK3,sK4) | k1_xboole_0 = sK4 | sK3 = k1_relset_1(sK3,sK4,sK5)),
% 0.21/0.55    inference(resolution,[],[f85,f118])).
% 0.21/0.55  fof(f118,plain,(
% 0.21/0.55    sP2(sK3,sK5,sK4)),
% 0.21/0.55    inference(resolution,[],[f89,f56])).
% 0.21/0.55  fof(f89,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP2(X0,X2,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f53])).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP2(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.55    inference(nnf_transformation,[],[f32])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP2(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.55    inference(definition_folding,[],[f27,f31])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP2(X0,X2,X1))),
% 0.21/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.55    inference(flattening,[],[f26])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.55    inference(ennf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.55  fof(f85,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 = X2 | k1_relset_1(X0,X2,X1) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f52])).
% 0.21/0.55  fof(f52,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP2(X0,X1,X2))),
% 0.21/0.55    inference(rectify,[],[f51])).
% 0.21/0.55  fof(f51,plain,(
% 0.21/0.55    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP2(X0,X2,X1))),
% 0.21/0.55    inference(nnf_transformation,[],[f31])).
% 0.21/0.55  fof(f93,plain,(
% 0.21/0.55    ( ! [X6,X0,X1] : (~r2_hidden(X6,k1_relat_1(X0)) | r2_hidden(k1_funct_1(X0,X6),X1) | ~sP0(X0,X1)) )),
% 0.21/0.55    inference(equality_resolution,[],[f68])).
% 0.21/0.55  fof(f68,plain,(
% 0.21/0.55    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | ~sP0(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f43])).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    ! [X0,X1] : ((sP0(X0,X1) | ((! [X3] : (k1_funct_1(X0,X3) != sK7(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK7(X0,X1),X1)) & ((sK7(X0,X1) = k1_funct_1(X0,sK8(X0,X1)) & r2_hidden(sK8(X0,X1),k1_relat_1(X0))) | r2_hidden(sK7(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK9(X0,X5)) = X5 & r2_hidden(sK9(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | ~sP0(X0,X1)))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f39,f42,f41,f40])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK7(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK7(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK7(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK7(X0,X1),X1))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK7(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK7(X0,X1) = k1_funct_1(X0,sK8(X0,X1)) & r2_hidden(sK8(X0,X1),k1_relat_1(X0))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK9(X0,X5)) = X5 & r2_hidden(sK9(X0,X5),k1_relat_1(X0))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | ~sP0(X0,X1)))),
% 0.21/0.55    inference(rectify,[],[f38])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | ~sP0(X0,X1)))),
% 0.21/0.55    inference(nnf_transformation,[],[f28])).
% 0.21/0.55  fof(f135,plain,(
% 0.21/0.55    sK4 != k2_relat_1(sK5)),
% 0.21/0.55    inference(superposition,[],[f59,f134])).
% 0.21/0.55  fof(f134,plain,(
% 0.21/0.55    k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5)),
% 0.21/0.55    inference(resolution,[],[f83,f56])).
% 0.21/0.55  fof(f83,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.55    inference(ennf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.55  fof(f59,plain,(
% 0.21/0.55    sK4 != k2_relset_1(sK3,sK4,sK5)),
% 0.21/0.55    inference(cnf_transformation,[],[f35])).
% 0.21/0.55  fof(f111,plain,(
% 0.21/0.55    k1_xboole_0 != k1_relat_1(sK5) | k1_xboole_0 = k2_relat_1(sK5)),
% 0.21/0.55    inference(resolution,[],[f62,f104])).
% 0.21/0.55  fof(f62,plain,(
% 0.21/0.55    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = k2_relat_1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f36])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(nnf_transformation,[],[f17])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).
% 0.21/0.55  fof(f384,plain,(
% 0.21/0.55    k1_xboole_0 = k1_relat_1(sK5)),
% 0.21/0.55    inference(backward_demodulation,[],[f373,f383])).
% 0.21/0.55  fof(f383,plain,(
% 0.21/0.55    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK5)),
% 0.21/0.55    inference(subsumption_resolution,[],[f381,f368])).
% 0.21/0.55  fof(f368,plain,(
% 0.21/0.55    v1_funct_2(sK5,k1_xboole_0,k1_xboole_0)),
% 0.21/0.55    inference(backward_demodulation,[],[f263,f367])).
% 0.21/0.55  fof(f367,plain,(
% 0.21/0.55    k1_xboole_0 = sK3),
% 0.21/0.55    inference(subsumption_resolution,[],[f349,f61])).
% 0.21/0.55  fof(f61,plain,(
% 0.21/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.55    inference(cnf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.55  fof(f349,plain,(
% 0.21/0.55    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 = sK3),
% 0.21/0.55    inference(superposition,[],[f276,f332])).
% 0.21/0.55  fof(f332,plain,(
% 0.21/0.55    k1_xboole_0 = sK5 | k1_xboole_0 = sK3),
% 0.21/0.55    inference(subsumption_resolution,[],[f326,f263])).
% 0.21/0.55  % (7582)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  fof(f326,plain,(
% 0.21/0.55    ~v1_funct_2(sK5,sK3,k1_xboole_0) | k1_xboole_0 = sK3 | k1_xboole_0 = sK5),
% 0.21/0.55    inference(resolution,[],[f264,f100])).
% 0.21/0.55  fof(f100,plain,(
% 0.21/0.55    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2) )),
% 0.21/0.55    inference(equality_resolution,[],[f90])).
% 0.21/0.55  fof(f90,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f53])).
% 0.21/0.55  fof(f264,plain,(
% 0.21/0.55    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)))),
% 0.21/0.55    inference(backward_demodulation,[],[f56,f262])).
% 0.21/0.55  fof(f263,plain,(
% 0.21/0.55    v1_funct_2(sK5,sK3,k1_xboole_0)),
% 0.21/0.55    inference(backward_demodulation,[],[f55,f262])).
% 0.21/0.55  fof(f381,plain,(
% 0.21/0.55    ~v1_funct_2(sK5,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK5)),
% 0.21/0.55    inference(resolution,[],[f372,f97])).
% 0.21/0.55  fof(f97,plain,(
% 0.21/0.55    ( ! [X2,X1] : (~sP2(k1_xboole_0,X1,X2) | ~v1_funct_2(X1,k1_xboole_0,X2) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,X1)) )),
% 0.21/0.55    inference(equality_resolution,[],[f86])).
% 0.21/0.55  fof(f86,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 != X0 | ~sP2(X0,X1,X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f52])).
% 0.21/0.55  fof(f372,plain,(
% 0.21/0.55    sP2(k1_xboole_0,sK5,k1_xboole_0)),
% 0.21/0.55    inference(backward_demodulation,[],[f273,f367])).
% 0.21/0.55  fof(f273,plain,(
% 0.21/0.55    sP2(sK3,sK5,k1_xboole_0)),
% 0.21/0.55    inference(backward_demodulation,[],[f118,f262])).
% 0.21/0.55  fof(f373,plain,(
% 0.21/0.55    k1_relat_1(sK5) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK5)),
% 0.21/0.55    inference(backward_demodulation,[],[f274,f367])).
% 0.21/0.55  fof(f274,plain,(
% 0.21/0.55    k1_relat_1(sK5) = k1_relset_1(sK3,k1_xboole_0,sK5)),
% 0.21/0.55    inference(backward_demodulation,[],[f133,f262])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (7563)------------------------------
% 0.21/0.55  % (7563)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (7563)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (7563)Memory used [KB]: 6652
% 0.21/0.55  % (7563)Time elapsed: 0.119 s
% 0.21/0.55  % (7563)------------------------------
% 0.21/0.55  % (7563)------------------------------
% 0.21/0.55  % (7574)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.56  % (7573)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.57  % (7580)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.57  % (7566)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.57  % (7575)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.57  % (7573)Refutation not found, incomplete strategy% (7573)------------------------------
% 0.21/0.57  % (7573)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (7566)Refutation not found, incomplete strategy% (7566)------------------------------
% 0.21/0.57  % (7566)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (7566)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (7566)Memory used [KB]: 10746
% 0.21/0.57  % (7566)Time elapsed: 0.142 s
% 0.21/0.57  % (7566)------------------------------
% 0.21/0.57  % (7566)------------------------------
% 0.21/0.58  % (7555)Success in time 0.217 s
%------------------------------------------------------------------------------
