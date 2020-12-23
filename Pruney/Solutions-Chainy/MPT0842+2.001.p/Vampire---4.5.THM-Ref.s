%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:56 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 306 expanded)
%              Number of leaves         :   21 ( 101 expanded)
%              Depth                    :   16
%              Number of atoms          :  399 (1983 expanded)
%              Number of equality atoms :   13 (  34 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f308,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f100,f105,f110,f204,f307])).

fof(f307,plain,
    ( ~ spl11_1
    | ~ spl11_2 ),
    inference(avatar_contradiction_clause,[],[f306])).

fof(f306,plain,
    ( $false
    | ~ spl11_1
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f304,f280])).

fof(f280,plain,
    ( r2_hidden(k4_tarski(sK4,sK9(sK4,sK1,sK3)),sK3)
    | ~ spl11_1 ),
    inference(unit_resulting_resolution,[],[f119,f220,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | r2_hidden(k4_tarski(X0,sK9(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK9(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK9(X0,X1,X2)),X2)
            & r2_hidden(sK9(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f38,f39])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK9(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK9(X0,X1,X2)),X2)
        & r2_hidden(sK9(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(f220,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ spl11_1 ),
    inference(unit_resulting_resolution,[],[f90,f95,f199,f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ sQ10_eqProxy(X2,X3)
      | ~ sQ10_eqProxy(X0,X1)
      | r2_hidden(X1,X3) ) ),
    inference(equality_proxy_axiom,[],[f68])).

fof(f68,plain,(
    ! [X1,X0] :
      ( sQ10_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ10_eqProxy])])).

fof(f199,plain,(
    ! [X0] : sQ10_eqProxy(k8_relset_1(sK0,sK2,sK3,X0),k10_relat_1(sK3,X0)) ),
    inference(unit_resulting_resolution,[],[f41,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sQ10_eqProxy(k8_relset_1(X0,X1,X2,X3),k10_relat_1(X2,X3)) ) ),
    inference(equality_proxy_replacement,[],[f64,f68])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f41,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f24,f27,f26,f25])).

fof(f25,plain,
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

fof(f26,plain,
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

fof(f27,plain,
    ( ? [X6] :
        ( r2_hidden(X6,sK1)
        & r2_hidden(k4_tarski(sK4,X6),sK3)
        & m1_subset_1(X6,sK2) )
   => ( r2_hidden(sK5,sK1)
      & r2_hidden(k4_tarski(sK4,sK5),sK3)
      & m1_subset_1(sK5,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
          <~> ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X4,X5),X3)
                & m1_subset_1(X5,X2) ) )
          & m1_subset_1(X4,X0) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => ! [X4] :
            ( m1_subset_1(X4,X0)
           => ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
            <=> ? [X5] :
                  ( r2_hidden(X5,X1)
                  & r2_hidden(k4_tarski(X4,X5),X3)
                  & m1_subset_1(X5,X2) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_relset_1)).

fof(f95,plain,
    ( r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl11_1
  <=> r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f90,plain,(
    ! [X0] : sQ10_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f68])).

fof(f119,plain,(
    v1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f41,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f304,plain,
    ( ~ r2_hidden(k4_tarski(sK4,sK9(sK4,sK1,sK3)),sK3)
    | ~ spl11_1
    | ~ spl11_2 ),
    inference(unit_resulting_resolution,[],[f283,f303,f99])).

fof(f99,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,sK1)
        | ~ m1_subset_1(X5,sK2)
        | ~ r2_hidden(k4_tarski(sK4,X5),sK3) )
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl11_2
  <=> ! [X5] :
        ( ~ r2_hidden(X5,sK1)
        | ~ m1_subset_1(X5,sK2)
        | ~ r2_hidden(k4_tarski(sK4,X5),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f303,plain,
    ( m1_subset_1(sK9(sK4,sK1,sK3),sK2)
    | ~ spl11_1 ),
    inference(unit_resulting_resolution,[],[f126,f281,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f281,plain,
    ( r2_hidden(sK9(sK4,sK1,sK3),k2_relat_1(sK3))
    | ~ spl11_1 ),
    inference(unit_resulting_resolution,[],[f119,f220,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | r2_hidden(sK9(X0,X1,X2),k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f126,plain,(
    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f124,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f124,plain,(
    r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(unit_resulting_resolution,[],[f119,f123,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
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

fof(f123,plain,(
    v5_relat_1(sK3,sK2) ),
    inference(unit_resulting_resolution,[],[f41,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f283,plain,
    ( r2_hidden(sK9(sK4,sK1,sK3),sK1)
    | ~ spl11_1 ),
    inference(unit_resulting_resolution,[],[f119,f220,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | r2_hidden(sK9(X0,X1,X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f204,plain,
    ( spl11_1
    | ~ spl11_3
    | ~ spl11_4 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | spl11_1
    | ~ spl11_3
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f200,f41])).

fof(f200,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl11_1
    | ~ spl11_3
    | ~ spl11_4 ),
    inference(unit_resulting_resolution,[],[f174,f72])).

fof(f174,plain,
    ( ~ sQ10_eqProxy(k8_relset_1(sK0,sK2,sK3,sK1),k10_relat_1(sK3,sK1))
    | spl11_1
    | ~ spl11_3
    | ~ spl11_4 ),
    inference(unit_resulting_resolution,[],[f149,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ sQ10_eqProxy(X0,X1)
      | sQ10_eqProxy(X1,X0) ) ),
    inference(equality_proxy_axiom,[],[f68])).

fof(f149,plain,
    ( ~ sQ10_eqProxy(k10_relat_1(sK3,sK1),k8_relset_1(sK0,sK2,sK3,sK1))
    | spl11_1
    | ~ spl11_3
    | ~ spl11_4 ),
    inference(unit_resulting_resolution,[],[f96,f90,f144,f85])).

fof(f144,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ spl11_3
    | ~ spl11_4 ),
    inference(unit_resulting_resolution,[],[f104,f119,f109,f65])).

fof(f65,plain,(
    ! [X6,X0,X7,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | r2_hidden(X6,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f30,f33,f32,f31])).

fof(f31,plain,(
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

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(sK6(X0,X1,X2),X5),X0) )
     => ( r2_hidden(sK7(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK8(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK8(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

fof(f109,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),sK3)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl11_4
  <=> r2_hidden(k4_tarski(sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f104,plain,
    ( r2_hidden(sK5,sK1)
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl11_3
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f96,plain,
    ( ~ r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))
    | spl11_1 ),
    inference(avatar_component_clause,[],[f94])).

fof(f110,plain,
    ( spl11_1
    | spl11_4 ),
    inference(avatar_split_clause,[],[f44,f107,f94])).

fof(f44,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),sK3)
    | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f105,plain,
    ( spl11_1
    | spl11_3 ),
    inference(avatar_split_clause,[],[f45,f102,f94])).

fof(f45,plain,
    ( r2_hidden(sK5,sK1)
    | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f100,plain,
    ( ~ spl11_1
    | spl11_2 ),
    inference(avatar_split_clause,[],[f46,f98,f94])).

fof(f46,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK1)
      | ~ r2_hidden(k4_tarski(sK4,X5),sK3)
      | ~ m1_subset_1(X5,sK2)
      | ~ r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:26:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (18212)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.44  % (18212)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f308,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(avatar_sat_refutation,[],[f100,f105,f110,f204,f307])).
% 0.20/0.44  fof(f307,plain,(
% 0.20/0.44    ~spl11_1 | ~spl11_2),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f306])).
% 0.20/0.44  fof(f306,plain,(
% 0.20/0.44    $false | (~spl11_1 | ~spl11_2)),
% 0.20/0.44    inference(subsumption_resolution,[],[f304,f280])).
% 0.20/0.44  fof(f280,plain,(
% 0.20/0.44    r2_hidden(k4_tarski(sK4,sK9(sK4,sK1,sK3)),sK3) | ~spl11_1),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f119,f220,f58])).
% 0.20/0.44  fof(f58,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (~r2_hidden(X0,k10_relat_1(X2,X1)) | r2_hidden(k4_tarski(X0,sK9(X0,X1,X2)),X2) | ~v1_relat_1(X2)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f40])).
% 0.20/0.44  fof(f40,plain,(
% 0.20/0.44    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK9(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK9(X0,X1,X2)),X2) & r2_hidden(sK9(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f38,f39])).
% 0.20/0.44  fof(f39,plain,(
% 0.20/0.44    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK9(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK9(X0,X1,X2)),X2) & r2_hidden(sK9(X0,X1,X2),k2_relat_1(X2))))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f38,plain,(
% 0.20/0.44    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.20/0.44    inference(rectify,[],[f37])).
% 0.20/0.44  fof(f37,plain,(
% 0.20/0.44    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.20/0.44    inference(nnf_transformation,[],[f16])).
% 0.20/0.44  fof(f16,plain,(
% 0.20/0.44    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.20/0.44    inference(ennf_transformation,[],[f5])).
% 0.20/0.44  fof(f5,axiom,(
% 0.20/0.44    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).
% 0.20/0.44  fof(f220,plain,(
% 0.20/0.44    r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~spl11_1),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f90,f95,f199,f85])).
% 0.20/0.44  fof(f85,plain,(
% 0.20/0.44    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X2) | ~sQ10_eqProxy(X2,X3) | ~sQ10_eqProxy(X0,X1) | r2_hidden(X1,X3)) )),
% 0.20/0.44    inference(equality_proxy_axiom,[],[f68])).
% 0.20/0.44  fof(f68,plain,(
% 0.20/0.44    ! [X1,X0] : (sQ10_eqProxy(X0,X1) <=> X0 = X1)),
% 0.20/0.44    introduced(equality_proxy_definition,[new_symbols(naming,[sQ10_eqProxy])])).
% 0.20/0.44  fof(f199,plain,(
% 0.20/0.44    ( ! [X0] : (sQ10_eqProxy(k8_relset_1(sK0,sK2,sK3,X0),k10_relat_1(sK3,X0))) )),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f41,f72])).
% 0.20/0.44  fof(f72,plain,(
% 0.20/0.44    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sQ10_eqProxy(k8_relset_1(X0,X1,X2,X3),k10_relat_1(X2,X3))) )),
% 0.20/0.44    inference(equality_proxy_replacement,[],[f64,f68])).
% 0.20/0.44  fof(f64,plain,(
% 0.20/0.44    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f21])).
% 0.20/0.44  fof(f21,plain,(
% 0.20/0.44    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.44    inference(ennf_transformation,[],[f8])).
% 0.20/0.44  fof(f8,axiom,(
% 0.20/0.44    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.20/0.44  fof(f41,plain,(
% 0.20/0.44    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.20/0.44    inference(cnf_transformation,[],[f28])).
% 0.20/0.44  fof(f28,plain,(
% 0.20/0.44    ((! [X5] : (~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(sK4,X5),sK3) | ~m1_subset_1(X5,sK2)) | ~r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))) & ((r2_hidden(sK5,sK1) & r2_hidden(k4_tarski(sK4,sK5),sK3) & m1_subset_1(sK5,sK2)) | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))) & m1_subset_1(sK4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f24,f27,f26,f25])).
% 0.20/0.45  fof(f25,plain,(
% 0.20/0.45    ? [X0,X1,X2,X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X4,X6),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) => (? [X4] : ((! [X5] : (~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(X4,X5),sK3) | ~m1_subset_1(X5,sK2)) | ~r2_hidden(X4,k8_relset_1(sK0,sK2,sK3,sK1))) & (? [X6] : (r2_hidden(X6,sK1) & r2_hidden(k4_tarski(X4,X6),sK3) & m1_subset_1(X6,sK2)) | r2_hidden(X4,k8_relset_1(sK0,sK2,sK3,sK1))) & m1_subset_1(X4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f26,plain,(
% 0.20/0.45    ? [X4] : ((! [X5] : (~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(X4,X5),sK3) | ~m1_subset_1(X5,sK2)) | ~r2_hidden(X4,k8_relset_1(sK0,sK2,sK3,sK1))) & (? [X6] : (r2_hidden(X6,sK1) & r2_hidden(k4_tarski(X4,X6),sK3) & m1_subset_1(X6,sK2)) | r2_hidden(X4,k8_relset_1(sK0,sK2,sK3,sK1))) & m1_subset_1(X4,sK0)) => ((! [X5] : (~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(sK4,X5),sK3) | ~m1_subset_1(X5,sK2)) | ~r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))) & (? [X6] : (r2_hidden(X6,sK1) & r2_hidden(k4_tarski(sK4,X6),sK3) & m1_subset_1(X6,sK2)) | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))) & m1_subset_1(sK4,sK0))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f27,plain,(
% 0.20/0.45    ? [X6] : (r2_hidden(X6,sK1) & r2_hidden(k4_tarski(sK4,X6),sK3) & m1_subset_1(X6,sK2)) => (r2_hidden(sK5,sK1) & r2_hidden(k4_tarski(sK4,sK5),sK3) & m1_subset_1(sK5,sK2))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f24,plain,(
% 0.20/0.45    ? [X0,X1,X2,X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X4,X6),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.20/0.45    inference(rectify,[],[f23])).
% 0.20/0.45  fof(f23,plain,(
% 0.20/0.45    ? [X0,X1,X2,X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.20/0.45    inference(flattening,[],[f22])).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    ? [X0,X1,X2,X3] : (? [X4] : (((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.20/0.45    inference(nnf_transformation,[],[f13])).
% 0.20/0.45  fof(f13,plain,(
% 0.20/0.45    ? [X0,X1,X2,X3] : (? [X4] : ((r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <~> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.20/0.45    inference(ennf_transformation,[],[f11])).
% 0.20/0.45  fof(f11,plain,(
% 0.20/0.45    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2)))))),
% 0.20/0.45    inference(pure_predicate_removal,[],[f10])).
% 0.20/0.45  fof(f10,negated_conjecture,(
% 0.20/0.45    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))))))))),
% 0.20/0.45    inference(negated_conjecture,[],[f9])).
% 0.20/0.45  fof(f9,conjecture,(
% 0.20/0.45    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))))))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_relset_1)).
% 0.20/0.45  fof(f95,plain,(
% 0.20/0.45    r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) | ~spl11_1),
% 0.20/0.45    inference(avatar_component_clause,[],[f94])).
% 0.20/0.45  fof(f94,plain,(
% 0.20/0.45    spl11_1 <=> r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 0.20/0.45  fof(f90,plain,(
% 0.20/0.45    ( ! [X0] : (sQ10_eqProxy(X0,X0)) )),
% 0.20/0.45    inference(equality_proxy_axiom,[],[f68])).
% 0.20/0.45  fof(f119,plain,(
% 0.20/0.45    v1_relat_1(sK3)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f41,f61])).
% 0.20/0.45  fof(f61,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f17])).
% 0.20/0.45  fof(f17,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.45    inference(ennf_transformation,[],[f6])).
% 0.20/0.45  fof(f6,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.45  fof(f304,plain,(
% 0.20/0.45    ~r2_hidden(k4_tarski(sK4,sK9(sK4,sK1,sK3)),sK3) | (~spl11_1 | ~spl11_2)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f283,f303,f99])).
% 0.20/0.45  fof(f99,plain,(
% 0.20/0.45    ( ! [X5] : (~r2_hidden(X5,sK1) | ~m1_subset_1(X5,sK2) | ~r2_hidden(k4_tarski(sK4,X5),sK3)) ) | ~spl11_2),
% 0.20/0.45    inference(avatar_component_clause,[],[f98])).
% 0.20/0.45  fof(f98,plain,(
% 0.20/0.45    spl11_2 <=> ! [X5] : (~r2_hidden(X5,sK1) | ~m1_subset_1(X5,sK2) | ~r2_hidden(k4_tarski(sK4,X5),sK3))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 0.20/0.45  fof(f303,plain,(
% 0.20/0.45    m1_subset_1(sK9(sK4,sK1,sK3),sK2) | ~spl11_1),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f126,f281,f63])).
% 0.20/0.45  fof(f63,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f20])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.45    inference(flattening,[],[f19])).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.20/0.45    inference(ennf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.20/0.45  fof(f281,plain,(
% 0.20/0.45    r2_hidden(sK9(sK4,sK1,sK3),k2_relat_1(sK3)) | ~spl11_1),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f119,f220,f57])).
% 0.20/0.45  fof(f57,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~r2_hidden(X0,k10_relat_1(X2,X1)) | r2_hidden(sK9(X0,X1,X2),k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f40])).
% 0.20/0.45  fof(f126,plain,(
% 0.20/0.45    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2))),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f124,f56])).
% 0.20/0.45  fof(f56,plain,(
% 0.20/0.45    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f36])).
% 0.20/0.45  fof(f36,plain,(
% 0.20/0.45    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.45    inference(nnf_transformation,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.45  fof(f124,plain,(
% 0.20/0.45    r1_tarski(k2_relat_1(sK3),sK2)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f119,f123,f53])).
% 0.20/0.45  fof(f53,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f35])).
% 0.20/0.45  fof(f35,plain,(
% 0.20/0.45    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.45    inference(nnf_transformation,[],[f15])).
% 0.20/0.45  fof(f15,plain,(
% 0.20/0.45    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.45    inference(ennf_transformation,[],[f4])).
% 0.20/0.45  fof(f4,axiom,(
% 0.20/0.45    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.20/0.45  fof(f123,plain,(
% 0.20/0.45    v5_relat_1(sK3,sK2)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f41,f62])).
% 0.20/0.45  fof(f62,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f18])).
% 0.20/0.45  fof(f18,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.45    inference(ennf_transformation,[],[f12])).
% 0.20/0.45  fof(f12,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.20/0.45    inference(pure_predicate_removal,[],[f7])).
% 0.20/0.45  fof(f7,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.45  fof(f283,plain,(
% 0.20/0.45    r2_hidden(sK9(sK4,sK1,sK3),sK1) | ~spl11_1),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f119,f220,f59])).
% 0.20/0.45  fof(f59,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~r2_hidden(X0,k10_relat_1(X2,X1)) | r2_hidden(sK9(X0,X1,X2),X1) | ~v1_relat_1(X2)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f40])).
% 0.20/0.45  fof(f204,plain,(
% 0.20/0.45    spl11_1 | ~spl11_3 | ~spl11_4),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f203])).
% 0.20/0.45  fof(f203,plain,(
% 0.20/0.45    $false | (spl11_1 | ~spl11_3 | ~spl11_4)),
% 0.20/0.45    inference(subsumption_resolution,[],[f200,f41])).
% 0.20/0.45  fof(f200,plain,(
% 0.20/0.45    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | (spl11_1 | ~spl11_3 | ~spl11_4)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f174,f72])).
% 0.20/0.45  fof(f174,plain,(
% 0.20/0.45    ~sQ10_eqProxy(k8_relset_1(sK0,sK2,sK3,sK1),k10_relat_1(sK3,sK1)) | (spl11_1 | ~spl11_3 | ~spl11_4)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f149,f91])).
% 0.20/0.45  fof(f91,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~sQ10_eqProxy(X0,X1) | sQ10_eqProxy(X1,X0)) )),
% 0.20/0.45    inference(equality_proxy_axiom,[],[f68])).
% 0.20/0.45  fof(f149,plain,(
% 0.20/0.45    ~sQ10_eqProxy(k10_relat_1(sK3,sK1),k8_relset_1(sK0,sK2,sK3,sK1)) | (spl11_1 | ~spl11_3 | ~spl11_4)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f96,f90,f144,f85])).
% 0.20/0.45  fof(f144,plain,(
% 0.20/0.45    r2_hidden(sK4,k10_relat_1(sK3,sK1)) | (~spl11_3 | ~spl11_4)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f104,f119,f109,f65])).
% 0.20/0.45  fof(f65,plain,(
% 0.20/0.45    ( ! [X6,X0,X7,X1] : (~v1_relat_1(X0) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | r2_hidden(X6,k10_relat_1(X0,X1))) )),
% 0.20/0.45    inference(equality_resolution,[],[f49])).
% 0.20/0.45  fof(f49,plain,(
% 0.20/0.45    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | k10_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f34])).
% 0.20/0.45  fof(f34,plain,(
% 0.20/0.45    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK6(X0,X1,X2),X4),X0)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0)) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & ((r2_hidden(sK8(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK8(X0,X1,X6)),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f30,f33,f32,f31])).
% 0.20/0.45  fof(f31,plain,(
% 0.20/0.45    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK6(X0,X1,X2),X4),X0)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(sK6(X0,X1,X2),X5),X0)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f32,plain,(
% 0.20/0.45    ! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(sK6(X0,X1,X2),X5),X0)) => (r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0)))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f33,plain,(
% 0.20/0.45    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) => (r2_hidden(sK8(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK8(X0,X1,X6)),X0)))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f30,plain,(
% 0.20/0.45    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.20/0.45    inference(rectify,[],[f29])).
% 0.20/0.45  fof(f29,plain,(
% 0.20/0.45    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.20/0.45    inference(nnf_transformation,[],[f14])).
% 0.20/0.45  fof(f14,plain,(
% 0.20/0.45    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f3])).
% 0.20/0.45  fof(f3,axiom,(
% 0.20/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).
% 0.20/0.45  fof(f109,plain,(
% 0.20/0.45    r2_hidden(k4_tarski(sK4,sK5),sK3) | ~spl11_4),
% 0.20/0.45    inference(avatar_component_clause,[],[f107])).
% 0.20/0.45  fof(f107,plain,(
% 0.20/0.45    spl11_4 <=> r2_hidden(k4_tarski(sK4,sK5),sK3)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 0.20/0.45  fof(f104,plain,(
% 0.20/0.45    r2_hidden(sK5,sK1) | ~spl11_3),
% 0.20/0.45    inference(avatar_component_clause,[],[f102])).
% 0.20/0.45  fof(f102,plain,(
% 0.20/0.45    spl11_3 <=> r2_hidden(sK5,sK1)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 0.20/0.45  fof(f96,plain,(
% 0.20/0.45    ~r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) | spl11_1),
% 0.20/0.45    inference(avatar_component_clause,[],[f94])).
% 0.20/0.45  fof(f110,plain,(
% 0.20/0.45    spl11_1 | spl11_4),
% 0.20/0.45    inference(avatar_split_clause,[],[f44,f107,f94])).
% 0.20/0.45  fof(f44,plain,(
% 0.20/0.45    r2_hidden(k4_tarski(sK4,sK5),sK3) | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))),
% 0.20/0.45    inference(cnf_transformation,[],[f28])).
% 0.20/0.45  fof(f105,plain,(
% 0.20/0.45    spl11_1 | spl11_3),
% 0.20/0.45    inference(avatar_split_clause,[],[f45,f102,f94])).
% 0.20/0.45  fof(f45,plain,(
% 0.20/0.45    r2_hidden(sK5,sK1) | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))),
% 0.20/0.45    inference(cnf_transformation,[],[f28])).
% 0.20/0.45  fof(f100,plain,(
% 0.20/0.45    ~spl11_1 | spl11_2),
% 0.20/0.45    inference(avatar_split_clause,[],[f46,f98,f94])).
% 0.20/0.45  fof(f46,plain,(
% 0.20/0.45    ( ! [X5] : (~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(sK4,X5),sK3) | ~m1_subset_1(X5,sK2) | ~r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f28])).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (18212)------------------------------
% 0.20/0.45  % (18212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (18212)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (18212)Memory used [KB]: 10746
% 0.20/0.45  % (18212)Time elapsed: 0.012 s
% 0.20/0.45  % (18212)------------------------------
% 0.20/0.45  % (18212)------------------------------
% 0.20/0.45  % (18197)Success in time 0.089 s
%------------------------------------------------------------------------------
