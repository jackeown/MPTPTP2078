%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:58 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 193 expanded)
%              Number of leaves         :   24 (  69 expanded)
%              Depth                    :   11
%              Number of atoms          :  322 ( 623 expanded)
%              Number of equality atoms :   42 (  82 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f157,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f58,f62,f69,f77,f80,f100,f119,f134,f139,f144,f152,f154,f156])).

fof(f156,plain,
    ( ~ spl5_2
    | ~ spl5_18 ),
    inference(avatar_contradiction_clause,[],[f155])).

fof(f155,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f57,f150])).

fof(f150,plain,
    ( ! [X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl5_18
  <=> ! [X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f57,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl5_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f154,plain,
    ( ~ spl5_2
    | ~ spl5_8 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f57,f96])).

fof(f96,plain,
    ( ! [X2,X3] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl5_8
  <=> ! [X3,X2] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f152,plain,
    ( spl5_18
    | ~ spl5_4
    | spl5_17 ),
    inference(avatar_split_clause,[],[f147,f142,f67,f149])).

fof(f67,plain,
    ( spl5_4
  <=> r2_hidden(sK0,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f142,plain,
    ( spl5_17
  <=> r2_hidden(sK0,k9_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f147,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,k2_relat_1(sK3))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) )
    | spl5_17 ),
    inference(superposition,[],[f143,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = k2_relat_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(global_subsumption,[],[f44,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = k2_relat_1(X0)
      | ~ v1_relat_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(superposition,[],[f37,f82])).

fof(f82,plain,(
    ! [X4,X0,X1] :
      ( k7_relat_1(X0,X1) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ),
    inference(global_subsumption,[],[f39,f44,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

% (21660)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f143,plain,
    ( ~ r2_hidden(sK0,k9_relat_1(sK3,sK1))
    | spl5_17 ),
    inference(avatar_component_clause,[],[f142])).

fof(f144,plain,
    ( ~ spl5_5
    | ~ spl5_17
    | spl5_16 ),
    inference(avatar_split_clause,[],[f140,f137,f142,f72])).

fof(f72,plain,
    ( spl5_5
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f137,plain,
    ( spl5_16
  <=> r2_hidden(sK4(sK0,sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f140,plain,
    ( ~ r2_hidden(sK0,k9_relat_1(sK3,sK1))
    | ~ v1_relat_1(sK3)
    | spl5_16 ),
    inference(resolution,[],[f138,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2)
            & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2)
        & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f138,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,sK3),sK1)
    | spl5_16 ),
    inference(avatar_component_clause,[],[f137])).

fof(f139,plain,
    ( ~ spl5_16
    | spl5_15 ),
    inference(avatar_split_clause,[],[f135,f132,f137])).

fof(f132,plain,
    ( spl5_15
  <=> m1_subset_1(sK4(sK0,sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f135,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,sK3),sK1)
    | spl5_15 ),
    inference(resolution,[],[f133,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f133,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,sK3),sK1)
    | spl5_15 ),
    inference(avatar_component_clause,[],[f132])).

fof(f134,plain,
    ( ~ spl5_15
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f123,f117,f132])).

fof(f117,plain,
    ( spl5_12
  <=> sK0 = k1_funct_1(sK3,sK4(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f123,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,sK3),sK1)
    | ~ spl5_12 ),
    inference(trivial_inequality_removal,[],[f122])).

fof(f122,plain,
    ( sK0 != sK0
    | ~ m1_subset_1(sK4(sK0,sK1,sK3),sK1)
    | ~ spl5_12 ),
    inference(superposition,[],[f36,f118])).

fof(f118,plain,
    ( sK0 = k1_funct_1(sK3,sK4(sK0,sK1,sK3))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f117])).

fof(f36,plain,(
    ! [X4] :
      ( sK0 != k1_funct_1(sK3,X4)
      | ~ m1_subset_1(X4,sK1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ! [X4] :
        ( sK0 != k1_funct_1(sK3,X4)
        | ~ m1_subset_1(X4,sK1) )
    & r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f25])).

fof(f25,plain,
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

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => k1_funct_1(X3,X4) != X0 )
            & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => k1_funct_1(X3,X4) != X0 )
            & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ( m1_subset_1(X4,X1)
             => k1_funct_1(X3,X4) != X0 )
          & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).

fof(f119,plain,
    ( spl5_12
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f107,f98,f67,f56,f117])).

fof(f98,plain,
    ( spl5_9
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | k1_funct_1(sK3,sK4(X0,X1,sK3)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f107,plain,
    ( sK0 = k1_funct_1(sK3,sK4(sK0,sK1,sK3))
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_9 ),
    inference(resolution,[],[f104,f68])).

fof(f68,plain,
    ( r2_hidden(sK0,k2_relat_1(sK3))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f104,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | k1_funct_1(sK3,sK4(X0,sK1,sK3)) = X0 )
    | ~ spl5_2
    | ~ spl5_9 ),
    inference(resolution,[],[f103,f57])).

fof(f103,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | k1_funct_1(sK3,sK4(X1,X0,sK3)) = X1
        | ~ r2_hidden(X1,k2_relat_1(sK3)) )
    | ~ spl5_9 ),
    inference(superposition,[],[f99,f84])).

fof(f99,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | k1_funct_1(sK3,sK4(X0,X1,sK3)) = X0 )
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f98])).

fof(f100,plain,
    ( spl5_8
    | spl5_9
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f93,f75,f98,f95])).

fof(f75,plain,
    ( spl5_6
  <=> ! [X1,X0] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK3)
        | k1_funct_1(sK3,X0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f93,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | k1_funct_1(sK3,sK4(X0,X1,sK3)) = X0 )
    | ~ spl5_6 ),
    inference(resolution,[],[f85,f76])).

fof(f76,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK3)
        | k1_funct_1(sK3,X0) = X1 )
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f75])).

fof(f85,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X2,X1),X0),X1)
      | ~ r2_hidden(X0,k9_relat_1(X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(resolution,[],[f41,f44])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f80,plain,
    ( ~ spl5_2
    | spl5_5 ),
    inference(avatar_contradiction_clause,[],[f79])).

fof(f79,plain,
    ( $false
    | ~ spl5_2
    | spl5_5 ),
    inference(subsumption_resolution,[],[f57,f78])).

fof(f78,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl5_5 ),
    inference(resolution,[],[f73,f44])).

fof(f73,plain,
    ( ~ v1_relat_1(sK3)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f72])).

fof(f77,plain,
    ( ~ spl5_5
    | spl5_6
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f70,f60,f75,f72])).

fof(f60,plain,
    ( spl5_3
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f70,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK3)
        | k1_funct_1(sK3,X0) = X1
        | ~ v1_relat_1(sK3) )
    | ~ spl5_3 ),
    inference(resolution,[],[f48,f61])).

fof(f61,plain,
    ( v1_funct_1(sK3)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f69,plain,
    ( ~ spl5_2
    | spl5_4
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f64,f52,f67,f56])).

fof(f52,plain,
    ( spl5_1
  <=> r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f64,plain,
    ( r2_hidden(sK0,k2_relat_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_1 ),
    inference(superposition,[],[f53,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f53,plain,
    ( r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f62,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f33,f60])).

fof(f33,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f58,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f34,f56])).

fof(f34,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f26])).

fof(f54,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f35,f52])).

fof(f35,plain,(
    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:07:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.44  % (21658)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (21654)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.47  % (21652)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (21652)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (21647)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (21647)Refutation not found, incomplete strategy% (21647)------------------------------
% 0.21/0.48  % (21647)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (21647)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (21647)Memory used [KB]: 10618
% 0.21/0.48  % (21647)Time elapsed: 0.058 s
% 0.21/0.48  % (21647)------------------------------
% 0.21/0.48  % (21647)------------------------------
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f157,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f54,f58,f62,f69,f77,f80,f100,f119,f134,f139,f144,f152,f154,f156])).
% 0.21/0.48  fof(f156,plain,(
% 0.21/0.48    ~spl5_2 | ~spl5_18),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f155])).
% 0.21/0.48  fof(f155,plain,(
% 0.21/0.48    $false | (~spl5_2 | ~spl5_18)),
% 0.21/0.48    inference(subsumption_resolution,[],[f57,f150])).
% 0.21/0.48  fof(f150,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))) ) | ~spl5_18),
% 0.21/0.48    inference(avatar_component_clause,[],[f149])).
% 0.21/0.48  fof(f149,plain,(
% 0.21/0.48    spl5_18 <=> ! [X0] : ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl5_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f56])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    spl5_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.48  fof(f154,plain,(
% 0.21/0.48    ~spl5_2 | ~spl5_8),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f153])).
% 0.21/0.48  fof(f153,plain,(
% 0.21/0.48    $false | (~spl5_2 | ~spl5_8)),
% 0.21/0.48    inference(subsumption_resolution,[],[f57,f96])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    ( ! [X2,X3] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) ) | ~spl5_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f95])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    spl5_8 <=> ! [X3,X2] : ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.48  fof(f152,plain,(
% 0.21/0.48    spl5_18 | ~spl5_4 | spl5_17),
% 0.21/0.48    inference(avatar_split_clause,[],[f147,f142,f67,f149])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    spl5_4 <=> r2_hidden(sK0,k2_relat_1(sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.48  fof(f142,plain,(
% 0.21/0.48    spl5_17 <=> r2_hidden(sK0,k9_relat_1(sK3,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.48  fof(f147,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(sK0,k2_relat_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))) ) | spl5_17),
% 0.21/0.48    inference(superposition,[],[f143,f84])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k9_relat_1(X0,X1) = k2_relat_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.21/0.48    inference(global_subsumption,[],[f44,f83])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k9_relat_1(X0,X1) = k2_relat_1(X0) | ~v1_relat_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.21/0.48    inference(superposition,[],[f37,f82])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    ( ! [X4,X0,X1] : (k7_relat_1(X0,X1) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X4)))) )),
% 0.21/0.48    inference(global_subsumption,[],[f39,f44,f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  % (21660)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.21/0.48    inference(pure_predicate_removal,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.49  fof(f143,plain,(
% 0.21/0.49    ~r2_hidden(sK0,k9_relat_1(sK3,sK1)) | spl5_17),
% 0.21/0.49    inference(avatar_component_clause,[],[f142])).
% 0.21/0.49  fof(f144,plain,(
% 0.21/0.49    ~spl5_5 | ~spl5_17 | spl5_16),
% 0.21/0.49    inference(avatar_split_clause,[],[f140,f137,f142,f72])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    spl5_5 <=> v1_relat_1(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    spl5_16 <=> r2_hidden(sK4(sK0,sK1,sK3),sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    ~r2_hidden(sK0,k9_relat_1(sK3,sK1)) | ~v1_relat_1(sK3) | spl5_16),
% 0.21/0.49    inference(resolution,[],[f138,f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2) & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2) & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(rectify,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(nnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 0.21/0.50  fof(f138,plain,(
% 0.21/0.50    ~r2_hidden(sK4(sK0,sK1,sK3),sK1) | spl5_16),
% 0.21/0.50    inference(avatar_component_clause,[],[f137])).
% 0.21/0.50  fof(f139,plain,(
% 0.21/0.50    ~spl5_16 | spl5_15),
% 0.21/0.50    inference(avatar_split_clause,[],[f135,f132,f137])).
% 0.21/0.50  fof(f132,plain,(
% 0.21/0.50    spl5_15 <=> m1_subset_1(sK4(sK0,sK1,sK3),sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.50  fof(f135,plain,(
% 0.21/0.50    ~r2_hidden(sK4(sK0,sK1,sK3),sK1) | spl5_15),
% 0.21/0.50    inference(resolution,[],[f133,f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.21/0.50  fof(f133,plain,(
% 0.21/0.50    ~m1_subset_1(sK4(sK0,sK1,sK3),sK1) | spl5_15),
% 0.21/0.50    inference(avatar_component_clause,[],[f132])).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    ~spl5_15 | ~spl5_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f123,f117,f132])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    spl5_12 <=> sK0 = k1_funct_1(sK3,sK4(sK0,sK1,sK3))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    ~m1_subset_1(sK4(sK0,sK1,sK3),sK1) | ~spl5_12),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f122])).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    sK0 != sK0 | ~m1_subset_1(sK4(sK0,sK1,sK3),sK1) | ~spl5_12),
% 0.21/0.50    inference(superposition,[],[f36,f118])).
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    sK0 = k1_funct_1(sK3,sK4(sK0,sK1,sK3)) | ~spl5_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f117])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ( ! [X4] : (sK0 != k1_funct_1(sK3,X4) | ~m1_subset_1(X4,sK1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X4] : (sK0 != k1_funct_1(sK3,X4) | ~m1_subset_1(X4,sK1)) & r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(sK3)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X3)) => (! [X4] : (sK0 != k1_funct_1(sK3,X4) | ~m1_subset_1(X4,sK1)) & r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(sK3))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X3))),
% 0.21/0.50    inference(flattening,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X3)))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 0.21/0.50    inference(pure_predicate_removal,[],[f10])).
% 0.21/0.50  fof(f10,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 0.21/0.50    inference(negated_conjecture,[],[f9])).
% 0.21/0.50  fof(f9,conjecture,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).
% 0.21/0.50  fof(f119,plain,(
% 0.21/0.50    spl5_12 | ~spl5_2 | ~spl5_4 | ~spl5_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f107,f98,f67,f56,f117])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    spl5_9 <=> ! [X1,X0] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | k1_funct_1(sK3,sK4(X0,X1,sK3)) = X0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    sK0 = k1_funct_1(sK3,sK4(sK0,sK1,sK3)) | (~spl5_2 | ~spl5_4 | ~spl5_9)),
% 0.21/0.50    inference(resolution,[],[f104,f68])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    r2_hidden(sK0,k2_relat_1(sK3)) | ~spl5_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f67])).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | k1_funct_1(sK3,sK4(X0,sK1,sK3)) = X0) ) | (~spl5_2 | ~spl5_9)),
% 0.21/0.50    inference(resolution,[],[f103,f57])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | k1_funct_1(sK3,sK4(X1,X0,sK3)) = X1 | ~r2_hidden(X1,k2_relat_1(sK3))) ) | ~spl5_9),
% 0.21/0.50    inference(superposition,[],[f99,f84])).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | k1_funct_1(sK3,sK4(X0,X1,sK3)) = X0) ) | ~spl5_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f98])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    spl5_8 | spl5_9 | ~spl5_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f93,f75,f98,f95])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    spl5_6 <=> ! [X1,X0] : (~r2_hidden(k4_tarski(X0,X1),sK3) | k1_funct_1(sK3,X0) = X1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_funct_1(sK3,sK4(X0,X1,sK3)) = X0) ) | ~spl5_6),
% 0.21/0.50    inference(resolution,[],[f85,f76])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK3) | k1_funct_1(sK3,X0) = X1) ) | ~spl5_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f75])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(k4_tarski(sK4(X0,X2,X1),X0),X1) | ~r2_hidden(X0,k9_relat_1(X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.21/0.50    inference(resolution,[],[f41,f44])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ~spl5_2 | spl5_5),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f79])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    $false | (~spl5_2 | spl5_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f57,f78])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl5_5),
% 0.21/0.50    inference(resolution,[],[f73,f44])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ~v1_relat_1(sK3) | spl5_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f72])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    ~spl5_5 | spl5_6 | ~spl5_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f70,f60,f75,f72])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    spl5_3 <=> v1_funct_1(sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK3) | k1_funct_1(sK3,X0) = X1 | ~v1_relat_1(sK3)) ) | ~spl5_3),
% 0.21/0.50    inference(resolution,[],[f48,f61])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    v1_funct_1(sK3) | ~spl5_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f60])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(flattening,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(nnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(flattening,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    ~spl5_2 | spl5_4 | ~spl5_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f64,f52,f67,f56])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    spl5_1 <=> r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    r2_hidden(sK0,k2_relat_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl5_1),
% 0.21/0.50    inference(superposition,[],[f53,f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) | ~spl5_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f52])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    spl5_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f33,f60])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    v1_funct_1(sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    spl5_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f34,f56])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    spl5_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f35,f52])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (21652)------------------------------
% 0.21/0.50  % (21652)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (21652)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (21652)Memory used [KB]: 10746
% 0.21/0.50  % (21652)Time elapsed: 0.069 s
% 0.21/0.50  % (21652)------------------------------
% 0.21/0.50  % (21652)------------------------------
% 0.21/0.50  % (21645)Success in time 0.136 s
%------------------------------------------------------------------------------
