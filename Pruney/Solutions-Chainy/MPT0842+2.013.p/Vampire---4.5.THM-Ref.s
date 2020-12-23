%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:58 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 292 expanded)
%              Number of leaves         :   22 (  94 expanded)
%              Depth                    :   16
%              Number of atoms          :  402 (1962 expanded)
%              Number of equality atoms :   13 (  25 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f173,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f86,f91,f108,f172])).

fof(f172,plain,
    ( ~ spl11_1
    | ~ spl11_2 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | ~ spl11_1
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f169,f155])).

fof(f155,plain,
    ( ~ m1_subset_1(sK10(sK4,sK1,sK3),sK2)
    | ~ spl11_1
    | ~ spl11_2 ),
    inference(unit_resulting_resolution,[],[f135,f134,f80])).

fof(f80,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,sK2)
        | ~ r2_hidden(X5,sK1)
        | ~ r2_hidden(k4_tarski(sK4,X5),sK3) )
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl11_2
  <=> ! [X5] :
        ( ~ r2_hidden(X5,sK1)
        | ~ m1_subset_1(X5,sK2)
        | ~ r2_hidden(k4_tarski(sK4,X5),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f134,plain,
    ( r2_hidden(k4_tarski(sK4,sK10(sK4,sK1,sK3)),sK3)
    | ~ spl11_1 ),
    inference(unit_resulting_resolution,[],[f112,f101,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,sK10(X0,X1,X2)),X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK10(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK10(X0,X1,X2)),X2)
            & r2_hidden(sK10(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f42,f43])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK10(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK10(X0,X1,X2)),X2)
        & r2_hidden(sK10(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X0,X4),X2)
              & r2_hidden(X4,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X0,X3),X2)
              & r2_hidden(X3,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(f101,plain,(
    v1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f58,f45,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f45,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( ! [X5] :
          ( ~ r2_hidden(X5,sK1)
          | ~ r2_hidden(k4_tarski(sK4,X5),sK3)
          | ~ m1_subset_1(X5,sK2) )
      | ~ r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) )
    & ( ( r2_hidden(sK5,sK1)
        & r2_hidden(k4_tarski(sK4,sK5),sK3)
        & m1_subset_1(sK5,sK2) )
      | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) )
    & m1_subset_1(sK4,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f25,f28,f27,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ( ! [X5] :
                  ( ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(k4_tarski(X4,X5),X3)
                  | ~ m1_subset_1(X5,X2) )
              | ~ r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) )
            & ( ? [X6] :
                  ( r2_hidden(X6,X1)
                  & r2_hidden(k4_tarski(X4,X6),X3)
                  & m1_subset_1(X6,X2) )
              | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) )
            & m1_subset_1(X4,X0) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
   => ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(X5,sK1)
                | ~ r2_hidden(k4_tarski(X4,X5),sK3)
                | ~ m1_subset_1(X5,sK2) )
            | ~ r2_hidden(X4,k8_relset_1(sK0,sK2,sK3,sK1)) )
          & ( ? [X6] :
                ( r2_hidden(X6,sK1)
                & r2_hidden(k4_tarski(X4,X6),sK3)
                & m1_subset_1(X6,sK2) )
            | r2_hidden(X4,k8_relset_1(sK0,sK2,sK3,sK1)) )
          & m1_subset_1(X4,sK0) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X4] :
        ( ( ! [X5] :
              ( ~ r2_hidden(X5,sK1)
              | ~ r2_hidden(k4_tarski(X4,X5),sK3)
              | ~ m1_subset_1(X5,sK2) )
          | ~ r2_hidden(X4,k8_relset_1(sK0,sK2,sK3,sK1)) )
        & ( ? [X6] :
              ( r2_hidden(X6,sK1)
              & r2_hidden(k4_tarski(X4,X6),sK3)
              & m1_subset_1(X6,sK2) )
          | r2_hidden(X4,k8_relset_1(sK0,sK2,sK3,sK1)) )
        & m1_subset_1(X4,sK0) )
   => ( ( ! [X5] :
            ( ~ r2_hidden(X5,sK1)
            | ~ r2_hidden(k4_tarski(sK4,X5),sK3)
            | ~ m1_subset_1(X5,sK2) )
        | ~ r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) )
      & ( ? [X6] :
            ( r2_hidden(X6,sK1)
            & r2_hidden(k4_tarski(sK4,X6),sK3)
            & m1_subset_1(X6,sK2) )
        | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) )
      & m1_subset_1(sK4,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X6] :
        ( r2_hidden(X6,sK1)
        & r2_hidden(k4_tarski(sK4,X6),sK3)
        & m1_subset_1(X6,sK2) )
   => ( r2_hidden(sK5,sK1)
      & r2_hidden(k4_tarski(sK4,sK5),sK3)
      & m1_subset_1(sK5,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(X5,X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X3)
                | ~ m1_subset_1(X5,X2) )
            | ~ r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) )
          & ( ? [X6] :
                ( r2_hidden(X6,X1)
                & r2_hidden(k4_tarski(X4,X6),X3)
                & m1_subset_1(X6,X2) )
            | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) )
          & m1_subset_1(X4,X0) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(X5,X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X3)
                | ~ m1_subset_1(X5,X2) )
            | ~ r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X4,X5),X3)
                & m1_subset_1(X5,X2) )
            | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) )
          & m1_subset_1(X4,X0) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(X5,X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X3)
                | ~ m1_subset_1(X5,X2) )
            | ~ r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X4,X5),X3)
                & m1_subset_1(X5,X2) )
            | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) )
          & m1_subset_1(X4,X0) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
          <~> ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X4,X5),X3)
                & m1_subset_1(X5,X2) ) )
          & m1_subset_1(X4,X0) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => ! [X4] :
            ( m1_subset_1(X4,X0)
           => ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
            <=> ? [X5] :
                  ( r2_hidden(X5,X1)
                  & r2_hidden(k4_tarski(X4,X5),X3)
                  & m1_subset_1(X5,X2) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ~ v1_xboole_0(X2)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                   => ! [X4] :
                        ( m1_subset_1(X4,X0)
                       => ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
                        <=> ? [X5] :
                              ( r2_hidden(X5,X1)
                              & r2_hidden(k4_tarski(X4,X5),X3)
                              & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                 => ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X4,X5),X3)
                            & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_relset_1)).

fof(f58,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f112,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ spl11_1 ),
    inference(forward_demodulation,[],[f76,f99])).

fof(f99,plain,(
    ! [X0] : k10_relat_1(sK3,X0) = k8_relset_1(sK0,sK2,sK3,X0) ),
    inference(unit_resulting_resolution,[],[f45,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f76,plain,
    ( r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl11_1
  <=> r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f135,plain,
    ( r2_hidden(sK10(sK4,sK1,sK3),sK1)
    | ~ spl11_1 ),
    inference(unit_resulting_resolution,[],[f112,f101,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK10(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f169,plain,
    ( m1_subset_1(sK10(sK4,sK1,sK3),sK2)
    | ~ spl11_1 ),
    inference(unit_resulting_resolution,[],[f153,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f153,plain,
    ( r2_hidden(sK10(sK4,sK1,sK3),sK2)
    | ~ spl11_1 ),
    inference(unit_resulting_resolution,[],[f139,f133,f62])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK9(X0,X1),X1)
          & r2_hidden(sK9(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f38,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK9(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
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

fof(f133,plain,
    ( r2_hidden(sK10(sK4,sK1,sK3),k2_relat_1(sK3))
    | ~ spl11_1 ),
    inference(unit_resulting_resolution,[],[f112,f101,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK10(X0,X1,X2),k2_relat_1(X2))
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f139,plain,(
    r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(unit_resulting_resolution,[],[f101,f100,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f100,plain,(
    v5_relat_1(sK3,sK2) ),
    inference(unit_resulting_resolution,[],[f45,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f108,plain,
    ( spl11_1
    | ~ spl11_3
    | ~ spl11_4 ),
    inference(avatar_contradiction_clause,[],[f107])).

fof(f107,plain,
    ( $false
    | spl11_1
    | ~ spl11_3
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f103,f101])).

fof(f103,plain,
    ( ~ v1_relat_1(sK3)
    | spl11_1
    | ~ spl11_3
    | ~ spl11_4 ),
    inference(unit_resulting_resolution,[],[f85,f90,f102,f71])).

fof(f71,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

% (11777)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
fof(f35,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),X4),X0) )
                | ~ r2_hidden(sK6(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK7(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0) )
                | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ( r2_hidden(sK8(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(X6,sK8(X0,X1,X6)),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f31,f34,f33,f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X3,X4),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X3,X5),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),X4),X0) )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(sK6(X0,X1,X2),X5),X0) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(sK6(X0,X1,X2),X5),X0) )
     => ( r2_hidden(sK7(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK8(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK8(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X3,X5),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X6,X8),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

fof(f102,plain,
    ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | spl11_1 ),
    inference(backward_demodulation,[],[f77,f99])).

fof(f77,plain,
    ( ~ r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))
    | spl11_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f90,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),sK3)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl11_4
  <=> r2_hidden(k4_tarski(sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f85,plain,
    ( r2_hidden(sK5,sK1)
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl11_3
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f91,plain,
    ( spl11_1
    | spl11_4 ),
    inference(avatar_split_clause,[],[f48,f88,f75])).

fof(f48,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),sK3)
    | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f86,plain,
    ( spl11_1
    | spl11_3 ),
    inference(avatar_split_clause,[],[f49,f83,f75])).

fof(f49,plain,
    ( r2_hidden(sK5,sK1)
    | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f81,plain,
    ( ~ spl11_1
    | spl11_2 ),
    inference(avatar_split_clause,[],[f50,f79,f75])).

fof(f50,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK1)
      | ~ r2_hidden(k4_tarski(sK4,X5),sK3)
      | ~ m1_subset_1(X5,sK2)
      | ~ r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:52:00 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.50  % (11768)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.51  % (11776)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.51  % (11769)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (11767)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.29/0.51  % (11774)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.29/0.52  % (11759)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.29/0.52  % (11761)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.29/0.52  % (11757)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.29/0.52  % (11780)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.29/0.52  % (11784)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.29/0.52  % (11771)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.29/0.52  % (11768)Refutation not found, incomplete strategy% (11768)------------------------------
% 1.29/0.52  % (11768)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.52  % (11768)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.52  
% 1.29/0.52  % (11768)Memory used [KB]: 10618
% 1.29/0.52  % (11768)Time elapsed: 0.126 s
% 1.29/0.52  % (11768)------------------------------
% 1.29/0.52  % (11768)------------------------------
% 1.29/0.52  % (11786)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.29/0.52  % (11775)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.29/0.52  % (11762)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.29/0.52  % (11784)Refutation found. Thanks to Tanya!
% 1.29/0.52  % SZS status Theorem for theBenchmark
% 1.29/0.53  % (11781)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.29/0.53  % (11760)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.29/0.53  % (11763)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.29/0.53  % (11778)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.29/0.53  % (11782)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.29/0.53  % (11787)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.29/0.53  % (11769)Refutation not found, incomplete strategy% (11769)------------------------------
% 1.29/0.53  % (11769)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % (11769)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.53  
% 1.41/0.53  % (11769)Memory used [KB]: 10746
% 1.41/0.53  % (11769)Time elapsed: 0.127 s
% 1.41/0.53  % (11769)------------------------------
% 1.41/0.53  % (11769)------------------------------
% 1.41/0.53  % (11773)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.41/0.53  % (11772)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.41/0.53  % (11785)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.41/0.53  % (11779)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.41/0.54  % (11764)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.41/0.54  % (11765)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.41/0.54  % SZS output start Proof for theBenchmark
% 1.41/0.54  fof(f173,plain,(
% 1.41/0.54    $false),
% 1.41/0.54    inference(avatar_sat_refutation,[],[f81,f86,f91,f108,f172])).
% 1.41/0.54  fof(f172,plain,(
% 1.41/0.54    ~spl11_1 | ~spl11_2),
% 1.41/0.54    inference(avatar_contradiction_clause,[],[f171])).
% 1.41/0.54  fof(f171,plain,(
% 1.41/0.54    $false | (~spl11_1 | ~spl11_2)),
% 1.41/0.54    inference(subsumption_resolution,[],[f169,f155])).
% 1.41/0.54  fof(f155,plain,(
% 1.41/0.54    ~m1_subset_1(sK10(sK4,sK1,sK3),sK2) | (~spl11_1 | ~spl11_2)),
% 1.41/0.54    inference(unit_resulting_resolution,[],[f135,f134,f80])).
% 1.41/0.54  fof(f80,plain,(
% 1.41/0.54    ( ! [X5] : (~m1_subset_1(X5,sK2) | ~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(sK4,X5),sK3)) ) | ~spl11_2),
% 1.41/0.54    inference(avatar_component_clause,[],[f79])).
% 1.41/0.54  fof(f79,plain,(
% 1.41/0.54    spl11_2 <=> ! [X5] : (~r2_hidden(X5,sK1) | ~m1_subset_1(X5,sK2) | ~r2_hidden(k4_tarski(sK4,X5),sK3))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 1.41/0.54  fof(f134,plain,(
% 1.41/0.54    r2_hidden(k4_tarski(sK4,sK10(sK4,sK1,sK3)),sK3) | ~spl11_1),
% 1.41/0.54    inference(unit_resulting_resolution,[],[f112,f101,f66])).
% 1.41/0.54  fof(f66,plain,(
% 1.41/0.54    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,sK10(X0,X1,X2)),X2) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f44])).
% 1.41/0.54  fof(f44,plain,(
% 1.41/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK10(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK10(X0,X1,X2)),X2) & r2_hidden(sK10(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.41/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f42,f43])).
% 1.41/0.54  fof(f43,plain,(
% 1.41/0.54    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK10(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK10(X0,X1,X2)),X2) & r2_hidden(sK10(X0,X1,X2),k2_relat_1(X2))))),
% 1.41/0.54    introduced(choice_axiom,[])).
% 1.41/0.54  fof(f42,plain,(
% 1.41/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.41/0.54    inference(rectify,[],[f41])).
% 1.41/0.54  fof(f41,plain,(
% 1.41/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.41/0.54    inference(nnf_transformation,[],[f20])).
% 1.41/0.54  fof(f20,plain,(
% 1.41/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.41/0.54    inference(ennf_transformation,[],[f7])).
% 1.41/0.54  fof(f7,axiom,(
% 1.41/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).
% 1.41/0.54  fof(f101,plain,(
% 1.41/0.54    v1_relat_1(sK3)),
% 1.41/0.54    inference(unit_resulting_resolution,[],[f58,f45,f51])).
% 1.41/0.54  fof(f51,plain,(
% 1.41/0.54    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f15])).
% 1.41/0.54  fof(f15,plain,(
% 1.41/0.54    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.41/0.54    inference(ennf_transformation,[],[f3])).
% 1.41/0.54  fof(f3,axiom,(
% 1.41/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.41/0.54  fof(f45,plain,(
% 1.41/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.41/0.54    inference(cnf_transformation,[],[f29])).
% 1.41/0.54  fof(f29,plain,(
% 1.41/0.54    ((! [X5] : (~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(sK4,X5),sK3) | ~m1_subset_1(X5,sK2)) | ~r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))) & ((r2_hidden(sK5,sK1) & r2_hidden(k4_tarski(sK4,sK5),sK3) & m1_subset_1(sK5,sK2)) | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))) & m1_subset_1(sK4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.41/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f25,f28,f27,f26])).
% 1.41/0.54  fof(f26,plain,(
% 1.41/0.54    ? [X0,X1,X2,X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X4,X6),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) => (? [X4] : ((! [X5] : (~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(X4,X5),sK3) | ~m1_subset_1(X5,sK2)) | ~r2_hidden(X4,k8_relset_1(sK0,sK2,sK3,sK1))) & (? [X6] : (r2_hidden(X6,sK1) & r2_hidden(k4_tarski(X4,X6),sK3) & m1_subset_1(X6,sK2)) | r2_hidden(X4,k8_relset_1(sK0,sK2,sK3,sK1))) & m1_subset_1(X4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))))),
% 1.41/0.54    introduced(choice_axiom,[])).
% 1.41/0.54  fof(f27,plain,(
% 1.41/0.54    ? [X4] : ((! [X5] : (~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(X4,X5),sK3) | ~m1_subset_1(X5,sK2)) | ~r2_hidden(X4,k8_relset_1(sK0,sK2,sK3,sK1))) & (? [X6] : (r2_hidden(X6,sK1) & r2_hidden(k4_tarski(X4,X6),sK3) & m1_subset_1(X6,sK2)) | r2_hidden(X4,k8_relset_1(sK0,sK2,sK3,sK1))) & m1_subset_1(X4,sK0)) => ((! [X5] : (~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(sK4,X5),sK3) | ~m1_subset_1(X5,sK2)) | ~r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))) & (? [X6] : (r2_hidden(X6,sK1) & r2_hidden(k4_tarski(sK4,X6),sK3) & m1_subset_1(X6,sK2)) | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))) & m1_subset_1(sK4,sK0))),
% 1.41/0.54    introduced(choice_axiom,[])).
% 1.41/0.54  fof(f28,plain,(
% 1.41/0.54    ? [X6] : (r2_hidden(X6,sK1) & r2_hidden(k4_tarski(sK4,X6),sK3) & m1_subset_1(X6,sK2)) => (r2_hidden(sK5,sK1) & r2_hidden(k4_tarski(sK4,sK5),sK3) & m1_subset_1(sK5,sK2))),
% 1.41/0.54    introduced(choice_axiom,[])).
% 1.41/0.54  fof(f25,plain,(
% 1.41/0.54    ? [X0,X1,X2,X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X4,X6),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 1.41/0.54    inference(rectify,[],[f24])).
% 1.41/0.54  fof(f24,plain,(
% 1.41/0.54    ? [X0,X1,X2,X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 1.41/0.54    inference(flattening,[],[f23])).
% 1.41/0.54  fof(f23,plain,(
% 1.41/0.54    ? [X0,X1,X2,X3] : (? [X4] : (((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 1.41/0.54    inference(nnf_transformation,[],[f14])).
% 1.41/0.54  fof(f14,plain,(
% 1.41/0.54    ? [X0,X1,X2,X3] : (? [X4] : ((r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <~> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 1.41/0.54    inference(ennf_transformation,[],[f12])).
% 1.41/0.54  fof(f12,plain,(
% 1.41/0.54    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2)))))),
% 1.41/0.54    inference(pure_predicate_removal,[],[f11])).
% 1.41/0.54  fof(f11,negated_conjecture,(
% 1.41/0.54    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))))))))),
% 1.41/0.54    inference(negated_conjecture,[],[f10])).
% 1.41/0.54  fof(f10,conjecture,(
% 1.41/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))))))))),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_relset_1)).
% 1.41/0.54  fof(f58,plain,(
% 1.41/0.54    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.41/0.54    inference(cnf_transformation,[],[f6])).
% 1.41/0.54  fof(f6,axiom,(
% 1.41/0.54    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.41/0.54  fof(f112,plain,(
% 1.41/0.54    r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~spl11_1),
% 1.41/0.54    inference(forward_demodulation,[],[f76,f99])).
% 1.41/0.54  fof(f99,plain,(
% 1.41/0.54    ( ! [X0] : (k10_relat_1(sK3,X0) = k8_relset_1(sK0,sK2,sK3,X0)) )),
% 1.41/0.54    inference(unit_resulting_resolution,[],[f45,f70])).
% 1.41/0.54  fof(f70,plain,(
% 1.41/0.54    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.41/0.54    inference(cnf_transformation,[],[f22])).
% 1.41/0.54  fof(f22,plain,(
% 1.41/0.54    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.54    inference(ennf_transformation,[],[f9])).
% 1.41/0.54  fof(f9,axiom,(
% 1.41/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 1.41/0.54  fof(f76,plain,(
% 1.41/0.54    r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) | ~spl11_1),
% 1.41/0.54    inference(avatar_component_clause,[],[f75])).
% 1.41/0.54  fof(f75,plain,(
% 1.41/0.54    spl11_1 <=> r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 1.41/0.54  fof(f135,plain,(
% 1.41/0.54    r2_hidden(sK10(sK4,sK1,sK3),sK1) | ~spl11_1),
% 1.41/0.54    inference(unit_resulting_resolution,[],[f112,f101,f67])).
% 1.41/0.54  fof(f67,plain,(
% 1.41/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK10(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f44])).
% 1.41/0.54  fof(f169,plain,(
% 1.41/0.54    m1_subset_1(sK10(sK4,sK1,sK3),sK2) | ~spl11_1),
% 1.41/0.54    inference(unit_resulting_resolution,[],[f153,f61])).
% 1.41/0.54  fof(f61,plain,(
% 1.41/0.54    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f18])).
% 1.41/0.54  fof(f18,plain,(
% 1.41/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.41/0.54    inference(ennf_transformation,[],[f2])).
% 1.41/0.54  fof(f2,axiom,(
% 1.41/0.54    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.41/0.54  fof(f153,plain,(
% 1.41/0.54    r2_hidden(sK10(sK4,sK1,sK3),sK2) | ~spl11_1),
% 1.41/0.54    inference(unit_resulting_resolution,[],[f139,f133,f62])).
% 1.41/0.54  fof(f62,plain,(
% 1.41/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f40])).
% 1.41/0.54  fof(f40,plain,(
% 1.41/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.41/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f38,f39])).
% 1.41/0.54  fof(f39,plain,(
% 1.41/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0)))),
% 1.41/0.54    introduced(choice_axiom,[])).
% 1.41/0.54  fof(f38,plain,(
% 1.41/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.41/0.54    inference(rectify,[],[f37])).
% 1.41/0.54  fof(f37,plain,(
% 1.41/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.41/0.54    inference(nnf_transformation,[],[f19])).
% 1.41/0.54  fof(f19,plain,(
% 1.41/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.41/0.54    inference(ennf_transformation,[],[f1])).
% 1.41/0.54  fof(f1,axiom,(
% 1.41/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.41/0.54  fof(f133,plain,(
% 1.41/0.54    r2_hidden(sK10(sK4,sK1,sK3),k2_relat_1(sK3)) | ~spl11_1),
% 1.41/0.54    inference(unit_resulting_resolution,[],[f112,f101,f65])).
% 1.41/0.54  fof(f65,plain,(
% 1.41/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK10(X0,X1,X2),k2_relat_1(X2)) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f44])).
% 1.41/0.54  fof(f139,plain,(
% 1.41/0.54    r1_tarski(k2_relat_1(sK3),sK2)),
% 1.41/0.54    inference(unit_resulting_resolution,[],[f101,f100,f59])).
% 1.41/0.54  fof(f59,plain,(
% 1.41/0.54    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f36])).
% 1.41/0.54  fof(f36,plain,(
% 1.41/0.54    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.41/0.54    inference(nnf_transformation,[],[f17])).
% 1.41/0.54  fof(f17,plain,(
% 1.41/0.54    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.41/0.54    inference(ennf_transformation,[],[f5])).
% 1.41/0.54  fof(f5,axiom,(
% 1.41/0.54    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.41/0.54  fof(f100,plain,(
% 1.41/0.54    v5_relat_1(sK3,sK2)),
% 1.41/0.54    inference(unit_resulting_resolution,[],[f45,f69])).
% 1.41/0.54  fof(f69,plain,(
% 1.41/0.54    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.41/0.54    inference(cnf_transformation,[],[f21])).
% 1.41/0.54  fof(f21,plain,(
% 1.41/0.54    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.54    inference(ennf_transformation,[],[f13])).
% 1.41/0.54  fof(f13,plain,(
% 1.41/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.41/0.54    inference(pure_predicate_removal,[],[f8])).
% 1.41/0.54  fof(f8,axiom,(
% 1.41/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.41/0.54  fof(f108,plain,(
% 1.41/0.54    spl11_1 | ~spl11_3 | ~spl11_4),
% 1.41/0.54    inference(avatar_contradiction_clause,[],[f107])).
% 1.41/0.54  fof(f107,plain,(
% 1.41/0.54    $false | (spl11_1 | ~spl11_3 | ~spl11_4)),
% 1.41/0.54    inference(subsumption_resolution,[],[f103,f101])).
% 1.41/0.54  fof(f103,plain,(
% 1.41/0.54    ~v1_relat_1(sK3) | (spl11_1 | ~spl11_3 | ~spl11_4)),
% 1.41/0.54    inference(unit_resulting_resolution,[],[f85,f90,f102,f71])).
% 1.41/0.54  fof(f71,plain,(
% 1.41/0.54    ( ! [X6,X0,X7,X1] : (r2_hidden(X6,k10_relat_1(X0,X1)) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | ~v1_relat_1(X0)) )),
% 1.41/0.54    inference(equality_resolution,[],[f54])).
% 1.41/0.54  fof(f54,plain,(
% 1.41/0.54    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | k10_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f35])).
% 1.41/0.54  % (11777)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.41/0.54  fof(f35,plain,(
% 1.41/0.54    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK6(X0,X1,X2),X4),X0)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0)) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & ((r2_hidden(sK8(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK8(X0,X1,X6)),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.41/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f31,f34,f33,f32])).
% 1.41/0.54  fof(f32,plain,(
% 1.41/0.54    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK6(X0,X1,X2),X4),X0)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(sK6(X0,X1,X2),X5),X0)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 1.41/0.54    introduced(choice_axiom,[])).
% 1.41/0.54  fof(f33,plain,(
% 1.41/0.54    ! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(sK6(X0,X1,X2),X5),X0)) => (r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0)))),
% 1.41/0.54    introduced(choice_axiom,[])).
% 1.41/0.54  fof(f34,plain,(
% 1.41/0.54    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) => (r2_hidden(sK8(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK8(X0,X1,X6)),X0)))),
% 1.41/0.54    introduced(choice_axiom,[])).
% 1.41/0.54  fof(f31,plain,(
% 1.41/0.54    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.41/0.54    inference(rectify,[],[f30])).
% 1.41/0.54  fof(f30,plain,(
% 1.41/0.54    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.41/0.54    inference(nnf_transformation,[],[f16])).
% 1.41/0.54  fof(f16,plain,(
% 1.41/0.54    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 1.41/0.54    inference(ennf_transformation,[],[f4])).
% 1.41/0.54  fof(f4,axiom,(
% 1.41/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).
% 1.41/0.54  fof(f102,plain,(
% 1.41/0.54    ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | spl11_1),
% 1.41/0.54    inference(backward_demodulation,[],[f77,f99])).
% 1.41/0.54  fof(f77,plain,(
% 1.41/0.54    ~r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) | spl11_1),
% 1.41/0.54    inference(avatar_component_clause,[],[f75])).
% 1.41/0.54  fof(f90,plain,(
% 1.41/0.54    r2_hidden(k4_tarski(sK4,sK5),sK3) | ~spl11_4),
% 1.41/0.54    inference(avatar_component_clause,[],[f88])).
% 1.41/0.54  fof(f88,plain,(
% 1.41/0.54    spl11_4 <=> r2_hidden(k4_tarski(sK4,sK5),sK3)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 1.41/0.54  fof(f85,plain,(
% 1.41/0.54    r2_hidden(sK5,sK1) | ~spl11_3),
% 1.41/0.54    inference(avatar_component_clause,[],[f83])).
% 1.41/0.54  fof(f83,plain,(
% 1.41/0.54    spl11_3 <=> r2_hidden(sK5,sK1)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 1.41/0.54  fof(f91,plain,(
% 1.41/0.54    spl11_1 | spl11_4),
% 1.41/0.54    inference(avatar_split_clause,[],[f48,f88,f75])).
% 1.41/0.54  fof(f48,plain,(
% 1.41/0.54    r2_hidden(k4_tarski(sK4,sK5),sK3) | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))),
% 1.41/0.54    inference(cnf_transformation,[],[f29])).
% 1.41/0.54  fof(f86,plain,(
% 1.41/0.54    spl11_1 | spl11_3),
% 1.41/0.54    inference(avatar_split_clause,[],[f49,f83,f75])).
% 1.41/0.54  fof(f49,plain,(
% 1.41/0.54    r2_hidden(sK5,sK1) | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))),
% 1.41/0.54    inference(cnf_transformation,[],[f29])).
% 1.41/0.54  fof(f81,plain,(
% 1.41/0.54    ~spl11_1 | spl11_2),
% 1.41/0.54    inference(avatar_split_clause,[],[f50,f79,f75])).
% 1.41/0.54  fof(f50,plain,(
% 1.41/0.54    ( ! [X5] : (~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(sK4,X5),sK3) | ~m1_subset_1(X5,sK2) | ~r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))) )),
% 1.41/0.54    inference(cnf_transformation,[],[f29])).
% 1.41/0.54  % SZS output end Proof for theBenchmark
% 1.41/0.54  % (11784)------------------------------
% 1.41/0.54  % (11784)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (11784)Termination reason: Refutation
% 1.41/0.54  
% 1.41/0.54  % (11784)Memory used [KB]: 10874
% 1.41/0.54  % (11784)Time elapsed: 0.124 s
% 1.41/0.54  % (11784)------------------------------
% 1.41/0.54  % (11784)------------------------------
% 1.41/0.54  % (11770)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.41/0.54  % (11752)Success in time 0.193 s
%------------------------------------------------------------------------------
