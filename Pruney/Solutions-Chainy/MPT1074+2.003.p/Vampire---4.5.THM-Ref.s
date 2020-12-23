%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:05 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 426 expanded)
%              Number of leaves         :   16 ( 137 expanded)
%              Depth                    :   24
%              Number of atoms          :  364 (2573 expanded)
%              Number of equality atoms :   24 (  39 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f202,plain,(
    $false ),
    inference(subsumption_resolution,[],[f199,f88])).

fof(f88,plain,(
    ~ v5_relat_1(sK4,sK1) ),
    inference(subsumption_resolution,[],[f87,f70])).

fof(f70,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f56,f45])).

fof(f45,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
    & ! [X4] :
        ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1)
        | ~ m1_subset_1(X4,sK2) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4)
    & ~ v1_xboole_0(sK3)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f13,f29,f28,f27])).

fof(f27,plain,
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
              ( ~ r1_tarski(k2_relset_1(sK2,X2,X3),sK1)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(sK2,X2,X3,X4),sK1)
                  | ~ m1_subset_1(X4,sK2) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,X2)))
              & v1_funct_2(X3,sK2,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k2_relset_1(sK2,X2,X3),sK1)
            & ! [X4] :
                ( r2_hidden(k3_funct_2(sK2,X2,X3,X4),sK1)
                | ~ m1_subset_1(X4,sK2) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,X2)))
            & v1_funct_2(X3,sK2,X2)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k2_relset_1(sK2,sK3,X3),sK1)
          & ! [X4] :
              ( r2_hidden(k3_funct_2(sK2,sK3,X3,X4),sK1)
              | ~ m1_subset_1(X4,sK2) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
          & v1_funct_2(X3,sK2,sK3)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k2_relset_1(sK2,sK3,X3),sK1)
        & ! [X4] :
            ( r2_hidden(k3_funct_2(sK2,sK3,X3,X4),sK1)
            | ~ m1_subset_1(X4,sK2) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
        & v1_funct_2(X3,sK2,sK3)
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
      & ! [X4] :
          ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1)
          | ~ m1_subset_1(X4,sK2) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK4,sK2,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t191_funct_2)).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f87,plain,
    ( ~ v5_relat_1(sK4,sK1)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f86,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f86,plain,(
    ~ r1_tarski(k2_relat_1(sK4),sK1) ),
    inference(backward_demodulation,[],[f47,f84])).

fof(f84,plain,(
    k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(resolution,[],[f57,f45])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f47,plain,(
    ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f199,plain,(
    v5_relat_1(sK4,sK1) ),
    inference(resolution,[],[f194,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f194,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) ),
    inference(resolution,[],[f193,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(X2,X1,X0)
        & v1_funct_1(X2) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X1,X0,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ sP0(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X1,X0,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ sP0(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f193,plain,(
    sP0(sK1,k1_relat_1(sK4),sK4) ),
    inference(subsumption_resolution,[],[f192,f70])).

fof(f192,plain,
    ( sP0(sK1,k1_relat_1(sK4),sK4)
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f191,f43])).

fof(f43,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f191,plain,
    ( sP0(sK1,k1_relat_1(sK4),sK4)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(duplicate_literal_removal,[],[f189])).

fof(f189,plain,
    ( sP0(sK1,k1_relat_1(sK4),sK4)
    | sP0(sK1,k1_relat_1(sK4),sK4)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f187,f66])).

fof(f66,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(k1_funct_1(X2,sK6(k1_relat_1(X2),X1,X2)),X1)
      | sP0(X1,k1_relat_1(X2),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | ~ r2_hidden(k1_funct_1(X2,sK6(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( sP0(X1,X0,X2)
      | ( ~ r2_hidden(k1_funct_1(X2,sK6(X0,X1,X2)),X1)
        & r2_hidden(sK6(X0,X1,X2),X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f26,f39])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(k1_funct_1(X2,sK6(X0,X1,X2)),X1)
        & r2_hidden(sK6(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( sP0(X1,X0,X2)
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_folding,[],[f22,f25])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).

fof(f187,plain,
    ( r2_hidden(k1_funct_1(sK4,sK6(k1_relat_1(sK4),sK1,sK4)),sK1)
    | sP0(sK1,k1_relat_1(sK4),sK4) ),
    inference(superposition,[],[f125,f185])).

fof(f185,plain,(
    k3_funct_2(sK2,sK3,sK4,sK6(k1_relat_1(sK4),sK1,sK4)) = k1_funct_1(sK4,sK6(k1_relat_1(sK4),sK1,sK4)) ),
    inference(resolution,[],[f182,f88])).

fof(f182,plain,(
    ! [X1] :
      ( v5_relat_1(sK4,X1)
      | k3_funct_2(sK2,sK3,sK4,sK6(k1_relat_1(sK4),X1,sK4)) = k1_funct_1(sK4,sK6(k1_relat_1(sK4),X1,sK4)) ) ),
    inference(resolution,[],[f150,f59])).

fof(f150,plain,(
    ! [X0] :
      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
      | k1_funct_1(sK4,sK6(k1_relat_1(sK4),X0,sK4)) = k3_funct_2(sK2,sK3,sK4,sK6(k1_relat_1(sK4),X0,sK4)) ) ),
    inference(resolution,[],[f135,f62])).

fof(f135,plain,(
    ! [X2] :
      ( sP0(X2,k1_relat_1(sK4),sK4)
      | k3_funct_2(sK2,sK3,sK4,sK6(k1_relat_1(sK4),X2,sK4)) = k1_funct_1(sK4,sK6(k1_relat_1(sK4),X2,sK4)) ) ),
    inference(resolution,[],[f132,f117])).

fof(f117,plain,(
    ! [X2] :
      ( r2_hidden(sK6(k1_relat_1(sK4),X2,sK4),sK2)
      | sP0(X2,k1_relat_1(sK4),sK4) ) ),
    inference(resolution,[],[f115,f107])).

fof(f107,plain,(
    r1_tarski(k1_relat_1(sK4),sK2) ),
    inference(duplicate_literal_removal,[],[f104])).

fof(f104,plain,
    ( r1_tarski(k1_relat_1(sK4),sK2)
    | r1_tarski(k1_relat_1(sK4),sK2) ),
    inference(resolution,[],[f102,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f102,plain,(
    ! [X0] :
      ( r2_hidden(sK5(k1_relat_1(sK4),X0),sK2)
      | r1_tarski(k1_relat_1(sK4),X0) ) ),
    inference(resolution,[],[f100,f74])).

fof(f74,plain,(
    v4_relat_1(sK4,sK2) ),
    inference(resolution,[],[f58,f45])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(sK4,X1)
      | r1_tarski(k1_relat_1(sK4),X0)
      | r2_hidden(sK5(k1_relat_1(sK4),X0),X1) ) ),
    inference(resolution,[],[f83,f70])).

fof(f83,plain,(
    ! [X6,X7,X5] :
      ( ~ v1_relat_1(X5)
      | r1_tarski(k1_relat_1(X5),X6)
      | ~ v4_relat_1(X5,X7)
      | r2_hidden(sK5(k1_relat_1(X5),X6),X7) ) ),
    inference(resolution,[],[f73,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | r2_hidden(sK5(X0,X1),X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f53,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(sK4),X1)
      | r2_hidden(sK6(k1_relat_1(sK4),X0,sK4),X1)
      | sP0(X0,k1_relat_1(sK4),sK4) ) ),
    inference(subsumption_resolution,[],[f114,f70])).

fof(f114,plain,(
    ! [X0,X1] :
      ( sP0(X0,k1_relat_1(sK4),sK4)
      | ~ v1_relat_1(sK4)
      | r2_hidden(sK6(k1_relat_1(sK4),X0,sK4),X1)
      | ~ r1_tarski(k1_relat_1(sK4),X1) ) ),
    inference(resolution,[],[f103,f43])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X1)
      | sP0(X0,k1_relat_1(X1),X1)
      | ~ v1_relat_1(X1)
      | r2_hidden(sK6(k1_relat_1(X1),X0,X1),X2)
      | ~ r1_tarski(k1_relat_1(X1),X2) ) ),
    inference(resolution,[],[f67,f53])).

fof(f67,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK6(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | sP0(X1,k1_relat_1(X2),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | r2_hidden(sK6(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f132,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0) ) ),
    inference(resolution,[],[f131,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f131,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK2)
      | k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0) ) ),
    inference(subsumption_resolution,[],[f130,f41])).

fof(f41,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f130,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK2)
      | k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0)
      | v1_xboole_0(sK2) ) ),
    inference(subsumption_resolution,[],[f129,f45])).

fof(f129,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      | ~ m1_subset_1(X0,sK2)
      | k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0)
      | v1_xboole_0(sK2) ) ),
    inference(resolution,[],[f128,f44])).

fof(f44,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(sK4,X1,X2)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ m1_subset_1(X0,X1)
      | k1_funct_1(sK4,X0) = k3_funct_2(X1,X2,sK4,X0)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f65,f43])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f125,plain,(
    ! [X0] :
      ( r2_hidden(k3_funct_2(sK2,sK3,sK4,sK6(k1_relat_1(sK4),X0,sK4)),sK1)
      | sP0(X0,k1_relat_1(sK4),sK4) ) ),
    inference(resolution,[],[f120,f69])).

fof(f69,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f55,f54])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK1,X1)
      | sP0(X0,k1_relat_1(sK4),sK4)
      | r2_hidden(k3_funct_2(sK2,sK3,sK4,sK6(k1_relat_1(sK4),X0,sK4)),X1) ) ),
    inference(resolution,[],[f117,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK2)
      | ~ r1_tarski(sK1,X1)
      | r2_hidden(k3_funct_2(sK2,sK3,sK4,X0),X1) ) ),
    inference(resolution,[],[f79,f52])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,sK2)
      | r2_hidden(k3_funct_2(sK2,sK3,sK4,X0),X1)
      | ~ r1_tarski(sK1,X1) ) ),
    inference(resolution,[],[f46,f53])).

fof(f46,plain,(
    ! [X4] :
      ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1)
      | ~ m1_subset_1(X4,sK2) ) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:59:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (19041)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.47  % (19048)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.48  % (19041)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % (19056)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f202,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(subsumption_resolution,[],[f199,f88])).
% 0.20/0.49  fof(f88,plain,(
% 0.20/0.49    ~v5_relat_1(sK4,sK1)),
% 0.20/0.49    inference(subsumption_resolution,[],[f87,f70])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    v1_relat_1(sK4)),
% 0.20/0.49    inference(resolution,[],[f56,f45])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 0.20/0.49    inference(cnf_transformation,[],[f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ((~r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) & ! [X4] : (r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1) | ~m1_subset_1(X4,sK2)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)) & ~v1_xboole_0(sK3)) & ~v1_xboole_0(sK2)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f13,f29,f28,f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(sK2,X2,X3),sK1) & ! [X4] : (r2_hidden(k3_funct_2(sK2,X2,X3,X4),sK1) | ~m1_subset_1(X4,sK2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,X2))) & v1_funct_2(X3,sK2,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK2))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(sK2,X2,X3),sK1) & ! [X4] : (r2_hidden(k3_funct_2(sK2,X2,X3,X4),sK1) | ~m1_subset_1(X4,sK2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,X2))) & v1_funct_2(X3,sK2,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (~r1_tarski(k2_relset_1(sK2,sK3,X3),sK1) & ! [X4] : (r2_hidden(k3_funct_2(sK2,sK3,X3,X4),sK1) | ~m1_subset_1(X4,sK2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(X3,sK2,sK3) & v1_funct_1(X3)) & ~v1_xboole_0(sK3))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ? [X3] : (~r1_tarski(k2_relset_1(sK2,sK3,X3),sK1) & ! [X4] : (r2_hidden(k3_funct_2(sK2,sK3,X3,X4),sK1) | ~m1_subset_1(X4,sK2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(X3,sK2,sK3) & v1_funct_1(X3)) => (~r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) & ! [X4] : (r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1) | ~m1_subset_1(X4,sK2)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 0.20/0.49    inference(flattening,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 0.20/0.49    inference(negated_conjecture,[],[f10])).
% 0.20/0.49  fof(f10,conjecture,(
% 0.20/0.49    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t191_funct_2)).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.49  fof(f87,plain,(
% 0.20/0.49    ~v5_relat_1(sK4,sK1) | ~v1_relat_1(sK4)),
% 0.20/0.49    inference(resolution,[],[f86,f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(nnf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.20/0.49  fof(f86,plain,(
% 0.20/0.49    ~r1_tarski(k2_relat_1(sK4),sK1)),
% 0.20/0.49    inference(backward_demodulation,[],[f47,f84])).
% 0.20/0.49  fof(f84,plain,(
% 0.20/0.49    k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4)),
% 0.20/0.49    inference(resolution,[],[f57,f45])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ~r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f30])).
% 0.20/0.49  fof(f199,plain,(
% 0.20/0.49    v5_relat_1(sK4,sK1)),
% 0.20/0.49    inference(resolution,[],[f194,f59])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.49  fof(f194,plain,(
% 0.20/0.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1)))),
% 0.20/0.49    inference(resolution,[],[f193,f62])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X2,X1,X0) & v1_funct_1(X2)) | ~sP0(X0,X1,X2))),
% 0.20/0.49    inference(rectify,[],[f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ! [X1,X0,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~sP0(X1,X0,X2))),
% 0.20/0.49    inference(nnf_transformation,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X1,X0,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~sP0(X1,X0,X2))),
% 0.20/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.49  fof(f193,plain,(
% 0.20/0.49    sP0(sK1,k1_relat_1(sK4),sK4)),
% 0.20/0.49    inference(subsumption_resolution,[],[f192,f70])).
% 0.20/0.49  fof(f192,plain,(
% 0.20/0.49    sP0(sK1,k1_relat_1(sK4),sK4) | ~v1_relat_1(sK4)),
% 0.20/0.49    inference(subsumption_resolution,[],[f191,f43])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    v1_funct_1(sK4)),
% 0.20/0.49    inference(cnf_transformation,[],[f30])).
% 0.20/0.49  fof(f191,plain,(
% 0.20/0.49    sP0(sK1,k1_relat_1(sK4),sK4) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f189])).
% 0.20/0.49  fof(f189,plain,(
% 0.20/0.49    sP0(sK1,k1_relat_1(sK4),sK4) | sP0(sK1,k1_relat_1(sK4),sK4) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 0.20/0.49    inference(resolution,[],[f187,f66])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    ( ! [X2,X1] : (~r2_hidden(k1_funct_1(X2,sK6(k1_relat_1(X2),X1,X2)),X1) | sP0(X1,k1_relat_1(X2),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.49    inference(equality_resolution,[],[f64])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | ~r2_hidden(k1_funct_1(X2,sK6(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f40])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (sP0(X1,X0,X2) | (~r2_hidden(k1_funct_1(X2,sK6(X0,X1,X2)),X1) & r2_hidden(sK6(X0,X1,X2),X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f26,f39])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) => (~r2_hidden(k1_funct_1(X2,sK6(X0,X1,X2)),X1) & r2_hidden(sK6(X0,X1,X2),X0)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (sP0(X1,X0,X2) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.49    inference(definition_folding,[],[f22,f25])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.49    inference(flattening,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.49    inference(ennf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).
% 0.20/0.49  fof(f187,plain,(
% 0.20/0.49    r2_hidden(k1_funct_1(sK4,sK6(k1_relat_1(sK4),sK1,sK4)),sK1) | sP0(sK1,k1_relat_1(sK4),sK4)),
% 0.20/0.49    inference(superposition,[],[f125,f185])).
% 0.20/0.49  fof(f185,plain,(
% 0.20/0.49    k3_funct_2(sK2,sK3,sK4,sK6(k1_relat_1(sK4),sK1,sK4)) = k1_funct_1(sK4,sK6(k1_relat_1(sK4),sK1,sK4))),
% 0.20/0.49    inference(resolution,[],[f182,f88])).
% 0.20/0.49  fof(f182,plain,(
% 0.20/0.49    ( ! [X1] : (v5_relat_1(sK4,X1) | k3_funct_2(sK2,sK3,sK4,sK6(k1_relat_1(sK4),X1,sK4)) = k1_funct_1(sK4,sK6(k1_relat_1(sK4),X1,sK4))) )),
% 0.20/0.49    inference(resolution,[],[f150,f59])).
% 0.20/0.49  fof(f150,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) | k1_funct_1(sK4,sK6(k1_relat_1(sK4),X0,sK4)) = k3_funct_2(sK2,sK3,sK4,sK6(k1_relat_1(sK4),X0,sK4))) )),
% 0.20/0.49    inference(resolution,[],[f135,f62])).
% 0.20/0.49  fof(f135,plain,(
% 0.20/0.49    ( ! [X2] : (sP0(X2,k1_relat_1(sK4),sK4) | k3_funct_2(sK2,sK3,sK4,sK6(k1_relat_1(sK4),X2,sK4)) = k1_funct_1(sK4,sK6(k1_relat_1(sK4),X2,sK4))) )),
% 0.20/0.49    inference(resolution,[],[f132,f117])).
% 0.20/0.49  fof(f117,plain,(
% 0.20/0.49    ( ! [X2] : (r2_hidden(sK6(k1_relat_1(sK4),X2,sK4),sK2) | sP0(X2,k1_relat_1(sK4),sK4)) )),
% 0.20/0.49    inference(resolution,[],[f115,f107])).
% 0.20/0.49  fof(f107,plain,(
% 0.20/0.49    r1_tarski(k1_relat_1(sK4),sK2)),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f104])).
% 0.20/0.49  fof(f104,plain,(
% 0.20/0.49    r1_tarski(k1_relat_1(sK4),sK2) | r1_tarski(k1_relat_1(sK4),sK2)),
% 0.20/0.49    inference(resolution,[],[f102,f55])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f35])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.49    inference(rectify,[],[f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.49    inference(nnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.49  fof(f102,plain,(
% 0.20/0.49    ( ! [X0] : (r2_hidden(sK5(k1_relat_1(sK4),X0),sK2) | r1_tarski(k1_relat_1(sK4),X0)) )),
% 0.20/0.49    inference(resolution,[],[f100,f74])).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    v4_relat_1(sK4,sK2)),
% 0.20/0.49    inference(resolution,[],[f58,f45])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f20])).
% 0.20/0.49  fof(f100,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v4_relat_1(sK4,X1) | r1_tarski(k1_relat_1(sK4),X0) | r2_hidden(sK5(k1_relat_1(sK4),X0),X1)) )),
% 0.20/0.49    inference(resolution,[],[f83,f70])).
% 0.20/0.49  fof(f83,plain,(
% 0.20/0.49    ( ! [X6,X7,X5] : (~v1_relat_1(X5) | r1_tarski(k1_relat_1(X5),X6) | ~v4_relat_1(X5,X7) | r2_hidden(sK5(k1_relat_1(X5),X6),X7)) )),
% 0.20/0.49    inference(resolution,[],[f73,f50])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(nnf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | r2_hidden(sK5(X0,X1),X2) | r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(resolution,[],[f53,f54])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f115,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(sK4),X1) | r2_hidden(sK6(k1_relat_1(sK4),X0,sK4),X1) | sP0(X0,k1_relat_1(sK4),sK4)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f114,f70])).
% 0.20/0.49  fof(f114,plain,(
% 0.20/0.49    ( ! [X0,X1] : (sP0(X0,k1_relat_1(sK4),sK4) | ~v1_relat_1(sK4) | r2_hidden(sK6(k1_relat_1(sK4),X0,sK4),X1) | ~r1_tarski(k1_relat_1(sK4),X1)) )),
% 0.20/0.49    inference(resolution,[],[f103,f43])).
% 0.20/0.49  fof(f103,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v1_funct_1(X1) | sP0(X0,k1_relat_1(X1),X1) | ~v1_relat_1(X1) | r2_hidden(sK6(k1_relat_1(X1),X0,X1),X2) | ~r1_tarski(k1_relat_1(X1),X2)) )),
% 0.20/0.49    inference(resolution,[],[f67,f53])).
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    ( ! [X2,X1] : (r2_hidden(sK6(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | sP0(X1,k1_relat_1(X2),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.49    inference(equality_resolution,[],[f63])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | r2_hidden(sK6(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f40])).
% 0.20/0.49  fof(f132,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(X0,sK2) | k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0)) )),
% 0.20/0.49    inference(resolution,[],[f131,f52])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.20/0.49  fof(f131,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,sK2) | k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f130,f41])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ~v1_xboole_0(sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f30])).
% 0.20/0.49  fof(f130,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,sK2) | k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0) | v1_xboole_0(sK2)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f129,f45])).
% 0.20/0.49  fof(f129,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~m1_subset_1(X0,sK2) | k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0) | v1_xboole_0(sK2)) )),
% 0.20/0.49    inference(resolution,[],[f128,f44])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    v1_funct_2(sK4,sK2,sK3)),
% 0.20/0.49    inference(cnf_transformation,[],[f30])).
% 0.20/0.49  fof(f128,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v1_funct_2(sK4,X1,X2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(X0,X1) | k1_funct_1(sK4,X0) = k3_funct_2(X1,X2,sK4,X0) | v1_xboole_0(X1)) )),
% 0.20/0.49    inference(resolution,[],[f65,f43])).
% 0.20/0.49  fof(f65,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | v1_xboole_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.20/0.49    inference(flattening,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.20/0.49  fof(f125,plain,(
% 0.20/0.49    ( ! [X0] : (r2_hidden(k3_funct_2(sK2,sK3,sK4,sK6(k1_relat_1(sK4),X0,sK4)),sK1) | sP0(X0,k1_relat_1(sK4),sK4)) )),
% 0.20/0.49    inference(resolution,[],[f120,f69])).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f68])).
% 0.20/0.50  fof(f68,plain,(
% 0.20/0.50    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 0.20/0.50    inference(resolution,[],[f55,f54])).
% 0.20/0.50  fof(f120,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_tarski(sK1,X1) | sP0(X0,k1_relat_1(sK4),sK4) | r2_hidden(k3_funct_2(sK2,sK3,sK4,sK6(k1_relat_1(sK4),X0,sK4)),X1)) )),
% 0.20/0.50    inference(resolution,[],[f117,f89])).
% 0.20/0.50  fof(f89,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(X0,sK2) | ~r1_tarski(sK1,X1) | r2_hidden(k3_funct_2(sK2,sK3,sK4,X0),X1)) )),
% 0.20/0.50    inference(resolution,[],[f79,f52])).
% 0.20/0.50  fof(f79,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,sK2) | r2_hidden(k3_funct_2(sK2,sK3,sK4,X0),X1) | ~r1_tarski(sK1,X1)) )),
% 0.20/0.50    inference(resolution,[],[f46,f53])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ( ! [X4] : (r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1) | ~m1_subset_1(X4,sK2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f30])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (19041)------------------------------
% 0.20/0.50  % (19041)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (19041)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (19041)Memory used [KB]: 6396
% 0.20/0.50  % (19041)Time elapsed: 0.085 s
% 0.20/0.50  % (19041)------------------------------
% 0.20/0.50  % (19041)------------------------------
% 0.20/0.50  % (19033)Success in time 0.143 s
%------------------------------------------------------------------------------
