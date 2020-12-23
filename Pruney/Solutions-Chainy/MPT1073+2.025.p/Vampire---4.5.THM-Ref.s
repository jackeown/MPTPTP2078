%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 182 expanded)
%              Number of leaves         :   14 (  47 expanded)
%              Depth                    :   14
%              Number of atoms          :  268 ( 868 expanded)
%              Number of equality atoms :   62 ( 188 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f138,plain,(
    $false ),
    inference(resolution,[],[f137,f62])).

fof(f62,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f137,plain,(
    ~ r1_tarski(sK3,sK3) ),
    inference(resolution,[],[f135,f118])).

fof(f118,plain,(
    ! [X6] :
      ( m1_subset_1(sK8(sK5,sK3,sK2),X6)
      | ~ r1_tarski(sK3,X6) ) ),
    inference(resolution,[],[f114,f76])).

fof(f76,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_hidden(X1,X3)
      | m1_subset_1(X1,X2)
      | ~ r1_tarski(X3,X2) ) ),
    inference(resolution,[],[f58,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f114,plain,(
    r2_hidden(sK8(sK5,sK3,sK2),sK3) ),
    inference(resolution,[],[f105,f80])).

fof(f80,plain,(
    ! [X0] : sP0(sK5,X0,k9_relat_1(sK5,X0)) ),
    inference(global_subsumption,[],[f66,f79])).

fof(f79,plain,(
    ! [X0] :
      ( sP0(sK5,X0,k9_relat_1(sK5,X0))
      | ~ v1_relat_1(sK5) ) ),
    inference(resolution,[],[f70,f35])).

fof(f35,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ! [X4] :
        ( sK2 != k1_funct_1(sK5,X4)
        | ~ m1_subset_1(X4,sK3) )
    & r2_hidden(sK2,k2_relset_1(sK3,sK4,sK5))
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f12,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4] :
            ( k1_funct_1(X3,X4) != X0
            | ~ m1_subset_1(X4,X1) )
        & r2_hidden(X0,k2_relset_1(X1,X2,X3))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X3) )
   => ( ! [X4] :
          ( sK2 != k1_funct_1(sK5,X4)
          | ~ m1_subset_1(X4,sK3) )
      & r2_hidden(sK2,k2_relset_1(sK3,sK4,sK5))
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => k1_funct_1(X3,X4) != X0 )
            & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => k1_funct_1(X3,X4) != X0 )
            & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ( m1_subset_1(X4,X1)
             => k1_funct_1(X3,X4) != X0 )
          & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | sP0(X0,X1,k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f60,f49])).

fof(f49,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f14,f21,f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( sP0(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( k1_funct_1(X0,X4) = X3
              & r2_hidden(X4,X1)
              & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> sP0(X0,X1,X2) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0)
      | sP0(X0,X1,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ~ sP0(X0,X1,X2) )
          & ( sP0(X0,X1,X2)
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f66,plain,(
    v1_relat_1(sK5) ),
    inference(resolution,[],[f55,f36])).

fof(f36,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f24])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1,k9_relat_1(sK5,sK3))
      | r2_hidden(sK8(X0,X1,sK2),X1) ) ),
    inference(backward_demodulation,[],[f82,f102])).

fof(f102,plain,(
    k2_relset_1(sK3,sK4,sK5) = k9_relat_1(sK5,sK3) ),
    inference(forward_demodulation,[],[f100,f88])).

fof(f88,plain,(
    ! [X0] : k9_relat_1(sK5,X0) = k7_relset_1(sK3,sK4,sK5,X0) ),
    inference(resolution,[],[f59,f36])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f100,plain,(
    k2_relset_1(sK3,sK4,sK5) = k7_relset_1(sK3,sK4,sK5,sK3) ),
    inference(resolution,[],[f56,f36])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1,k2_relset_1(sK3,sK4,sK5))
      | r2_hidden(sK8(X0,X1,sK2),X1) ) ),
    inference(resolution,[],[f42,f37])).

fof(f37,plain,(
    r2_hidden(sK2,k2_relset_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f24])).

fof(f42,plain,(
    ! [X6,X2,X0,X1] :
      ( ~ r2_hidden(X6,X2)
      | r2_hidden(sK8(X0,X1,X6),X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ! [X4] :
                ( k1_funct_1(X0,X4) != sK6(X0,X1,X2)
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X4,k1_relat_1(X0)) )
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( sK6(X0,X1,X2) = k1_funct_1(X0,sK7(X0,X1,X2))
              & r2_hidden(sK7(X0,X1,X2),X1)
              & r2_hidden(sK7(X0,X1,X2),k1_relat_1(X0)) )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( k1_funct_1(X0,X7) != X6
                  | ~ r2_hidden(X7,X1)
                  | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
            & ( ( k1_funct_1(X0,sK8(X0,X1,X6)) = X6
                & r2_hidden(sK8(X0,X1,X6),X1)
                & r2_hidden(sK8(X0,X1,X6),k1_relat_1(X0)) )
              | ~ r2_hidden(X6,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f27,f30,f29,f28])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( k1_funct_1(X0,X4) != X3
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X4,k1_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( k1_funct_1(X0,X5) = X3
                & r2_hidden(X5,X1)
                & r2_hidden(X5,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( k1_funct_1(X0,X4) != sK6(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK6(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = sK6(X0,X1,X2)
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( sK6(X0,X1,X2) = k1_funct_1(X0,sK7(X0,X1,X2))
        & r2_hidden(sK7(X0,X1,X2),X1)
        & r2_hidden(sK7(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK8(X0,X1,X6)) = X6
        & r2_hidden(sK8(X0,X1,X6),X1)
        & r2_hidden(sK8(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ! [X4] :
                  ( k1_funct_1(X0,X4) != X3
                  | ~ r2_hidden(X4,X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X5] :
                  ( k1_funct_1(X0,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X5,k1_relat_1(X0)) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( k1_funct_1(X0,X7) != X6
                  | ~ r2_hidden(X7,X1)
                  | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
            & ( ? [X8] :
                  ( k1_funct_1(X0,X8) = X6
                  & r2_hidden(X8,X1)
                  & r2_hidden(X8,k1_relat_1(X0)) )
              | ~ r2_hidden(X6,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ! [X4] :
                  ( k1_funct_1(X0,X4) != X3
                  | ~ r2_hidden(X4,X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4] :
                  ( k1_funct_1(X0,X4) != X3
                  | ~ r2_hidden(X4,X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) ) )
            & ( ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f135,plain,(
    ~ m1_subset_1(sK8(sK5,sK3,sK2),sK3) ),
    inference(trivial_inequality_removal,[],[f134])).

fof(f134,plain,
    ( sK2 != sK2
    | ~ m1_subset_1(sK8(sK5,sK3,sK2),sK3) ),
    inference(superposition,[],[f38,f132])).

fof(f132,plain,(
    sK2 = k1_funct_1(sK5,sK8(sK5,sK3,sK2)) ),
    inference(resolution,[],[f103,f80])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1,k9_relat_1(sK5,sK3))
      | sK2 = k1_funct_1(X0,sK8(X0,X1,sK2)) ) ),
    inference(backward_demodulation,[],[f87,f102])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1,k2_relset_1(sK3,sK4,sK5))
      | sK2 = k1_funct_1(X0,sK8(X0,X1,sK2)) ) ),
    inference(resolution,[],[f43,f37])).

fof(f43,plain,(
    ! [X6,X2,X0,X1] :
      ( ~ r2_hidden(X6,X2)
      | k1_funct_1(X0,sK8(X0,X1,X6)) = X6
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f38,plain,(
    ! [X4] :
      ( sK2 != k1_funct_1(sK5,X4)
      | ~ m1_subset_1(X4,sK3) ) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:41:47 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (27055)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.47  % (27055)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (27047)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.47  % (27048)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f138,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(resolution,[],[f137,f62])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.48    inference(equality_resolution,[],[f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.48    inference(flattening,[],[f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.48    inference(nnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.48  fof(f137,plain,(
% 0.21/0.48    ~r1_tarski(sK3,sK3)),
% 0.21/0.48    inference(resolution,[],[f135,f118])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    ( ! [X6] : (m1_subset_1(sK8(sK5,sK3,sK2),X6) | ~r1_tarski(sK3,X6)) )),
% 0.21/0.48    inference(resolution,[],[f114,f76])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    ( ! [X2,X3,X1] : (~r2_hidden(X1,X3) | m1_subset_1(X1,X2) | ~r1_tarski(X3,X2)) )),
% 0.21/0.48    inference(resolution,[],[f58,f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.48    inference(nnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    r2_hidden(sK8(sK5,sK3,sK2),sK3)),
% 0.21/0.48    inference(resolution,[],[f105,f80])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    ( ! [X0] : (sP0(sK5,X0,k9_relat_1(sK5,X0))) )),
% 0.21/0.48    inference(global_subsumption,[],[f66,f79])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    ( ! [X0] : (sP0(sK5,X0,k9_relat_1(sK5,X0)) | ~v1_relat_1(sK5)) )),
% 0.21/0.48    inference(resolution,[],[f70,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    v1_funct_1(sK5)),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X4] : (sK2 != k1_funct_1(sK5,X4) | ~m1_subset_1(X4,sK3)) & r2_hidden(sK2,k2_relset_1(sK3,sK4,sK5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_1(sK5)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f12,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X3)) => (! [X4] : (sK2 != k1_funct_1(sK5,X4) | ~m1_subset_1(X4,sK3)) & r2_hidden(sK2,k2_relset_1(sK3,sK4,sK5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_1(sK5))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X3))),
% 0.21/0.48    inference(flattening,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X3)))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 0.21/0.48    inference(pure_predicate_removal,[],[f9])).
% 0.21/0.48  fof(f9,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 0.21/0.48    inference(negated_conjecture,[],[f8])).
% 0.21/0.48  fof(f8,conjecture,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_funct_1(X0) | sP0(X0,X1,k9_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(resolution,[],[f60,f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(definition_folding,[],[f14,f21,f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (sP0(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0)))))),
% 0.21/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> sP0(X0,X1,X2)) | ~sP1(X0))),
% 0.21/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~sP1(X0) | sP0(X0,X1,k9_relat_1(X0,X1))) )),
% 0.21/0.48    inference(equality_resolution,[],[f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | k9_relat_1(X0,X1) != X2 | ~sP1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ~sP0(X0,X1,X2)) & (sP0(X0,X1,X2) | k9_relat_1(X0,X1) != X2)) | ~sP1(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f21])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    v1_relat_1(sK5)),
% 0.21/0.48    inference(resolution,[],[f55,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~sP0(X0,X1,k9_relat_1(sK5,sK3)) | r2_hidden(sK8(X0,X1,sK2),X1)) )),
% 0.21/0.48    inference(backward_demodulation,[],[f82,f102])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    k2_relset_1(sK3,sK4,sK5) = k9_relat_1(sK5,sK3)),
% 0.21/0.48    inference(forward_demodulation,[],[f100,f88])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    ( ! [X0] : (k9_relat_1(sK5,X0) = k7_relset_1(sK3,sK4,sK5,X0)) )),
% 0.21/0.48    inference(resolution,[],[f59,f36])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    k2_relset_1(sK3,sK4,sK5) = k7_relset_1(sK3,sK4,sK5,sK3)),
% 0.21/0.48    inference(resolution,[],[f56,f36])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~sP0(X0,X1,k2_relset_1(sK3,sK4,sK5)) | r2_hidden(sK8(X0,X1,sK2),X1)) )),
% 0.21/0.48    inference(resolution,[],[f42,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    r2_hidden(sK2,k2_relset_1(sK3,sK4,sK5))),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X6,X2,X0,X1] : (~r2_hidden(X6,X2) | r2_hidden(sK8(X0,X1,X6),X1) | ~sP0(X0,X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((! [X4] : (k1_funct_1(X0,X4) != sK6(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((sK6(X0,X1,X2) = k1_funct_1(X0,sK7(X0,X1,X2)) & r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(sK7(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK8(X0,X1,X6)) = X6 & r2_hidden(sK8(X0,X1,X6),X1) & r2_hidden(sK8(X0,X1,X6),k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | ~sP0(X0,X1,X2)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f27,f30,f29,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((! [X4] : (k1_funct_1(X0,X4) != sK6(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (? [X5] : (k1_funct_1(X0,X5) = sK6(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X2,X1,X0] : (? [X5] : (k1_funct_1(X0,X5) = sK6(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) => (sK6(X0,X1,X2) = k1_funct_1(X0,sK7(X0,X1,X2)) & r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(sK7(X0,X1,X2),k1_relat_1(X0))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X6,X1,X0] : (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) => (k1_funct_1(X0,sK8(X0,X1,X6)) = X6 & r2_hidden(sK8(X0,X1,X6),X1) & r2_hidden(sK8(X0,X1,X6),k1_relat_1(X0))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | ~sP0(X0,X1,X2)))),
% 0.21/0.48    inference(rectify,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0)))) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | ~sP0(X0,X1,X2)))),
% 0.21/0.48    inference(nnf_transformation,[],[f20])).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    ~m1_subset_1(sK8(sK5,sK3,sK2),sK3)),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f134])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    sK2 != sK2 | ~m1_subset_1(sK8(sK5,sK3,sK2),sK3)),
% 0.21/0.48    inference(superposition,[],[f38,f132])).
% 0.21/0.48  fof(f132,plain,(
% 0.21/0.48    sK2 = k1_funct_1(sK5,sK8(sK5,sK3,sK2))),
% 0.21/0.48    inference(resolution,[],[f103,f80])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~sP0(X0,X1,k9_relat_1(sK5,sK3)) | sK2 = k1_funct_1(X0,sK8(X0,X1,sK2))) )),
% 0.21/0.48    inference(backward_demodulation,[],[f87,f102])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~sP0(X0,X1,k2_relset_1(sK3,sK4,sK5)) | sK2 = k1_funct_1(X0,sK8(X0,X1,sK2))) )),
% 0.21/0.48    inference(resolution,[],[f43,f37])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X6,X2,X0,X1] : (~r2_hidden(X6,X2) | k1_funct_1(X0,sK8(X0,X1,X6)) = X6 | ~sP0(X0,X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f31])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X4] : (sK2 != k1_funct_1(sK5,X4) | ~m1_subset_1(X4,sK3)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (27055)------------------------------
% 0.21/0.48  % (27055)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (27055)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (27055)Memory used [KB]: 6268
% 0.21/0.48  % (27055)Time elapsed: 0.056 s
% 0.21/0.48  % (27055)------------------------------
% 0.21/0.48  % (27055)------------------------------
% 0.21/0.48  % (27039)Success in time 0.123 s
%------------------------------------------------------------------------------
