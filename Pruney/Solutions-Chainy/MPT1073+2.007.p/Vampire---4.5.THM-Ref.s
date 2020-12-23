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
% DateTime   : Thu Dec  3 13:07:56 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 149 expanded)
%              Number of leaves         :   16 (  43 expanded)
%              Depth                    :   17
%              Number of atoms          :  309 ( 674 expanded)
%              Number of equality atoms :   49 ( 134 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f156,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f101,f141,f155])).

fof(f155,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f33,f150,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f150,plain,
    ( ~ v4_relat_1(sK3,sK1)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f147,f91])).

fof(f91,plain,
    ( v1_relat_1(sK3)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl8_2
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f147,plain,
    ( ~ v4_relat_1(sK3,sK1)
    | ~ v1_relat_1(sK3)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(resolution,[],[f145,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
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

fof(f145,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK1)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(resolution,[],[f144,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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

fof(f144,plain,
    ( ~ m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f143,f95])).

fof(f95,plain,
    ( r2_hidden(sK0,k2_relat_1(sK3))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl8_3
  <=> r2_hidden(sK0,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f143,plain,
    ( ~ m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1))
    | ~ r2_hidden(sK0,k2_relat_1(sK3))
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f142,f91])).

fof(f142,plain,
    ( ~ m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1))
    | ~ r2_hidden(sK0,k2_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f103,f32])).

fof(f32,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ! [X4] :
        ( sK0 != k1_funct_1(sK3,X4)
        | ~ m1_subset_1(X4,sK1) )
    & r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4] :
            ( k1_funct_1(X3,X4) != X0
            | ~ m1_subset_1(X4,X1) )
        & r2_hidden(X0,k2_relset_1(X1,X2,X3))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X3) )
   => ( ! [X4] :
          ( sK0 != k1_funct_1(sK3,X4)
          | ~ m1_subset_1(X4,sK1) )
      & r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).

fof(f103,plain,
    ( ~ m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1))
    | ~ r2_hidden(sK0,k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl8_1 ),
    inference(resolution,[],[f102,f53])).

fof(f53,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK6(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK6(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK4(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK4(X0,X1),X1) )
              & ( ( sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
                  & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK4(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK6(X0,X5)) = X5
                    & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f25,f28,f27,f26])).

fof(f26,plain,(
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
              ( k1_funct_1(X0,X3) != sK4(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK4(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK4(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK6(X0,X5)) = X5
        & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
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
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
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
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f102,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK6(sK3,sK0),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK1)) )
    | spl8_1 ),
    inference(resolution,[],[f88,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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

fof(f88,plain,
    ( ~ m1_subset_1(sK6(sK3,sK0),sK1)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl8_1
  <=> m1_subset_1(sK6(sK3,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f33,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f23])).

fof(f141,plain,(
    spl8_3 ),
    inference(avatar_contradiction_clause,[],[f140])).

fof(f140,plain,
    ( $false
    | spl8_3 ),
    inference(subsumption_resolution,[],[f136,f33])).

fof(f136,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl8_3 ),
    inference(resolution,[],[f133,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( sQ7_eqProxy(k2_relset_1(X0,X1,X2),k2_relat_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_proxy_replacement,[],[f47,f54])).

fof(f54,plain,(
    ! [X1,X0] :
      ( sQ7_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ7_eqProxy])])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f133,plain,
    ( ~ sQ7_eqProxy(k2_relset_1(sK1,sK2,sK3),k2_relat_1(sK3))
    | spl8_3 ),
    inference(resolution,[],[f128,f34])).

fof(f34,plain,(
    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f23])).

fof(f128,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,X0)
        | ~ sQ7_eqProxy(X0,k2_relat_1(sK3)) )
    | spl8_3 ),
    inference(resolution,[],[f126,f78])).

fof(f78,plain,(
    ! [X0] : sQ7_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f54])).

fof(f126,plain,
    ( ! [X0,X1] :
        ( ~ sQ7_eqProxy(X1,sK0)
        | ~ r2_hidden(X1,X0)
        | ~ sQ7_eqProxy(X0,k2_relat_1(sK3)) )
    | spl8_3 ),
    inference(resolution,[],[f72,f96])).

fof(f96,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK3))
    | spl8_3 ),
    inference(avatar_component_clause,[],[f94])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ sQ7_eqProxy(X2,X3)
      | ~ r2_hidden(X0,X2)
      | ~ sQ7_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f54])).

fof(f101,plain,(
    spl8_2 ),
    inference(avatar_contradiction_clause,[],[f98])).

fof(f98,plain,
    ( $false
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f33,f92,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f92,plain,
    ( ~ v1_relat_1(sK3)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f97,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f84,f94,f90,f86])).

fof(f84,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ m1_subset_1(sK6(sK3,sK0),sK1) ),
    inference(subsumption_resolution,[],[f83,f32])).

fof(f83,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ m1_subset_1(sK6(sK3,sK0),sK1) ),
    inference(resolution,[],[f59,f81])).

fof(f81,plain,(
    ! [X0] :
      ( ~ sQ7_eqProxy(k1_funct_1(sK3,X0),sK0)
      | ~ m1_subset_1(X0,sK1) ) ),
    inference(resolution,[],[f79,f55])).

fof(f55,plain,(
    ! [X4] :
      ( ~ sQ7_eqProxy(sK0,k1_funct_1(sK3,X4))
      | ~ m1_subset_1(X4,sK1) ) ),
    inference(equality_proxy_replacement,[],[f35,f54])).

fof(f35,plain,(
    ! [X4] :
      ( sK0 != k1_funct_1(sK3,X4)
      | ~ m1_subset_1(X4,sK1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f79,plain,(
    ! [X0,X1] :
      ( sQ7_eqProxy(X1,X0)
      | ~ sQ7_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f54])).

fof(f59,plain,(
    ! [X0,X5] :
      ( sQ7_eqProxy(k1_funct_1(X0,sK6(X0,X5)),X5)
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f52,f54])).

fof(f52,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK6(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK6(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:39:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (23810)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.46  % (23810)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f156,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f97,f101,f141,f155])).
% 0.21/0.46  fof(f155,plain,(
% 0.21/0.46    spl8_1 | ~spl8_2 | ~spl8_3),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f151])).
% 0.21/0.46  fof(f151,plain,(
% 0.21/0.46    $false | (spl8_1 | ~spl8_2 | ~spl8_3)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f33,f150,f48])).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(ennf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.21/0.46    inference(pure_predicate_removal,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.46  fof(f150,plain,(
% 0.21/0.46    ~v4_relat_1(sK3,sK1) | (spl8_1 | ~spl8_2 | ~spl8_3)),
% 0.21/0.46    inference(subsumption_resolution,[],[f147,f91])).
% 0.21/0.46  fof(f91,plain,(
% 0.21/0.46    v1_relat_1(sK3) | ~spl8_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f90])).
% 0.21/0.46  fof(f90,plain,(
% 0.21/0.46    spl8_2 <=> v1_relat_1(sK3)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.46  fof(f147,plain,(
% 0.21/0.46    ~v4_relat_1(sK3,sK1) | ~v1_relat_1(sK3) | (spl8_1 | ~spl8_2 | ~spl8_3)),
% 0.21/0.46    inference(resolution,[],[f145,f42])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f30])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(nnf_transformation,[],[f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.46  fof(f145,plain,(
% 0.21/0.46    ~r1_tarski(k1_relat_1(sK3),sK1) | (spl8_1 | ~spl8_2 | ~spl8_3)),
% 0.21/0.46    inference(resolution,[],[f144,f45])).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f31])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.46    inference(nnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.46  fof(f144,plain,(
% 0.21/0.46    ~m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1)) | (spl8_1 | ~spl8_2 | ~spl8_3)),
% 0.21/0.46    inference(subsumption_resolution,[],[f143,f95])).
% 0.21/0.46  fof(f95,plain,(
% 0.21/0.46    r2_hidden(sK0,k2_relat_1(sK3)) | ~spl8_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f94])).
% 0.21/0.46  fof(f94,plain,(
% 0.21/0.46    spl8_3 <=> r2_hidden(sK0,k2_relat_1(sK3))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.46  fof(f143,plain,(
% 0.21/0.46    ~m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1)) | ~r2_hidden(sK0,k2_relat_1(sK3)) | (spl8_1 | ~spl8_2)),
% 0.21/0.46    inference(subsumption_resolution,[],[f142,f91])).
% 0.21/0.46  fof(f142,plain,(
% 0.21/0.46    ~m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1)) | ~r2_hidden(sK0,k2_relat_1(sK3)) | ~v1_relat_1(sK3) | spl8_1),
% 0.21/0.46    inference(subsumption_resolution,[],[f103,f32])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    v1_funct_1(sK3)),
% 0.21/0.46    inference(cnf_transformation,[],[f23])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ! [X4] : (sK0 != k1_funct_1(sK3,X4) | ~m1_subset_1(X4,sK1)) & r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(sK3)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X3)) => (! [X4] : (sK0 != k1_funct_1(sK3,X4) | ~m1_subset_1(X4,sK1)) & r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(sK3))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X3))),
% 0.21/0.46    inference(flattening,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X3)))),
% 0.21/0.46    inference(ennf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 0.21/0.46    inference(pure_predicate_removal,[],[f9])).
% 0.21/0.46  fof(f9,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 0.21/0.46    inference(negated_conjecture,[],[f8])).
% 0.21/0.46  fof(f8,conjecture,(
% 0.21/0.46    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).
% 0.21/0.46  fof(f103,plain,(
% 0.21/0.46    ~m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1)) | ~r2_hidden(sK0,k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl8_1),
% 0.21/0.46    inference(resolution,[],[f102,f53])).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    ( ! [X0,X5] : (r2_hidden(sK6(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(equality_resolution,[],[f36])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    ( ! [X0,X5,X1] : (r2_hidden(sK6(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f29])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1),X1)) & ((sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK6(X0,X5)) = X5 & r2_hidden(sK6(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f25,f28,f27,f26])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK4(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK4(X0,X1),X1))))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK4(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK6(X0,X5)) = X5 & r2_hidden(sK6(X0,X5),k1_relat_1(X0))))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(rectify,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(flattening,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 0.21/0.47  fof(f102,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(sK6(sK3,sK0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK1))) ) | spl8_1),
% 0.21/0.47    inference(resolution,[],[f88,f49])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.47    inference(flattening,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    ~m1_subset_1(sK6(sK3,sK0),sK1) | spl8_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f86])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    spl8_1 <=> m1_subset_1(sK6(sK3,sK0),sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f141,plain,(
% 0.21/0.47    spl8_3),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f140])).
% 0.21/0.47  fof(f140,plain,(
% 0.21/0.47    $false | spl8_3),
% 0.21/0.47    inference(subsumption_resolution,[],[f136,f33])).
% 0.21/0.47  fof(f136,plain,(
% 0.21/0.47    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl8_3),
% 0.21/0.47    inference(resolution,[],[f133,f60])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (sQ7_eqProxy(k2_relset_1(X0,X1,X2),k2_relat_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.47    inference(equality_proxy_replacement,[],[f47,f54])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    ! [X1,X0] : (sQ7_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.47    introduced(equality_proxy_definition,[new_symbols(naming,[sQ7_eqProxy])])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.47  fof(f133,plain,(
% 0.21/0.47    ~sQ7_eqProxy(k2_relset_1(sK1,sK2,sK3),k2_relat_1(sK3)) | spl8_3),
% 0.21/0.47    inference(resolution,[],[f128,f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f128,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(sK0,X0) | ~sQ7_eqProxy(X0,k2_relat_1(sK3))) ) | spl8_3),
% 0.21/0.47    inference(resolution,[],[f126,f78])).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    ( ! [X0] : (sQ7_eqProxy(X0,X0)) )),
% 0.21/0.47    inference(equality_proxy_axiom,[],[f54])).
% 0.21/0.47  fof(f126,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~sQ7_eqProxy(X1,sK0) | ~r2_hidden(X1,X0) | ~sQ7_eqProxy(X0,k2_relat_1(sK3))) ) | spl8_3),
% 0.21/0.47    inference(resolution,[],[f72,f96])).
% 0.21/0.47  fof(f96,plain,(
% 0.21/0.47    ~r2_hidden(sK0,k2_relat_1(sK3)) | spl8_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f94])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~sQ7_eqProxy(X2,X3) | ~r2_hidden(X0,X2) | ~sQ7_eqProxy(X0,X1)) )),
% 0.21/0.47    inference(equality_proxy_axiom,[],[f54])).
% 0.21/0.47  fof(f101,plain,(
% 0.21/0.47    spl8_2),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f98])).
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    $false | spl8_2),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f33,f92,f46])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.47  fof(f92,plain,(
% 0.21/0.47    ~v1_relat_1(sK3) | spl8_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f90])).
% 0.21/0.47  fof(f97,plain,(
% 0.21/0.47    ~spl8_1 | ~spl8_2 | ~spl8_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f84,f94,f90,f86])).
% 0.21/0.47  fof(f84,plain,(
% 0.21/0.47    ~r2_hidden(sK0,k2_relat_1(sK3)) | ~v1_relat_1(sK3) | ~m1_subset_1(sK6(sK3,sK0),sK1)),
% 0.21/0.47    inference(subsumption_resolution,[],[f83,f32])).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    ~r2_hidden(sK0,k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~m1_subset_1(sK6(sK3,sK0),sK1)),
% 0.21/0.47    inference(resolution,[],[f59,f81])).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    ( ! [X0] : (~sQ7_eqProxy(k1_funct_1(sK3,X0),sK0) | ~m1_subset_1(X0,sK1)) )),
% 0.21/0.47    inference(resolution,[],[f79,f55])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    ( ! [X4] : (~sQ7_eqProxy(sK0,k1_funct_1(sK3,X4)) | ~m1_subset_1(X4,sK1)) )),
% 0.21/0.47    inference(equality_proxy_replacement,[],[f35,f54])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X4] : (sK0 != k1_funct_1(sK3,X4) | ~m1_subset_1(X4,sK1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    ( ! [X0,X1] : (sQ7_eqProxy(X1,X0) | ~sQ7_eqProxy(X0,X1)) )),
% 0.21/0.47    inference(equality_proxy_axiom,[],[f54])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    ( ! [X0,X5] : (sQ7_eqProxy(k1_funct_1(X0,sK6(X0,X5)),X5) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(equality_proxy_replacement,[],[f52,f54])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    ( ! [X0,X5] : (k1_funct_1(X0,sK6(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK6(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f29])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (23810)------------------------------
% 0.21/0.47  % (23810)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (23810)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (23810)Memory used [KB]: 6140
% 0.21/0.47  % (23810)Time elapsed: 0.014 s
% 0.21/0.47  % (23810)------------------------------
% 0.21/0.47  % (23810)------------------------------
% 0.21/0.47  % (23800)Success in time 0.109 s
%------------------------------------------------------------------------------
