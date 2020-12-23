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
% DateTime   : Thu Dec  3 13:00:48 EST 2020

% Result     : Theorem 1.08s
% Output     : Refutation 1.08s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 738 expanded)
%              Number of leaves         :   13 ( 186 expanded)
%              Depth                    :   21
%              Number of atoms          :  306 (3058 expanded)
%              Number of equality atoms :   85 ( 495 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f131,plain,(
    $false ),
    inference(subsumption_resolution,[],[f129,f109])).

fof(f109,plain,(
    ~ r2_hidden(sK4,k1_funct_2(k1_xboole_0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f41,f106])).

fof(f106,plain,(
    k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f102,f41])).

fof(f102,plain,
    ( r2_hidden(sK4,k1_funct_2(sK3,sK3))
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f94,f99])).

fof(f99,plain,
    ( sK3 = k1_relat_1(sK4)
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f98,f78])).

fof(f78,plain,(
    k1_relat_1(sK4) = k1_relset_1(sK3,sK3,sK4) ),
    inference(resolution,[],[f45,f40])).

fof(f40,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ r2_hidden(sK4,k1_funct_2(sK3,sK3))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
    & v1_funct_2(sK4,sK3,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f11,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( ~ r2_hidden(X1,k1_funct_2(X0,X0))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ~ r2_hidden(sK4,k1_funct_2(sK3,sK3))
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
      & v1_funct_2(sK4,sK3,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X1,k1_funct_2(X0,X0))
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X1,k1_funct_2(X0,X0))
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => r2_hidden(X1,k1_funct_2(X0,X0)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => r2_hidden(X1,k1_funct_2(X0,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_2)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

% (23830)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f98,plain,
    ( sK3 = k1_relset_1(sK3,sK3,sK4)
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f97,f39])).

fof(f39,plain,(
    v1_funct_2(sK4,sK3,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f97,plain,
    ( ~ v1_funct_2(sK4,sK3,sK3)
    | k1_xboole_0 = sK3
    | sK3 = k1_relset_1(sK3,sK3,sK4) ),
    inference(resolution,[],[f47,f77])).

fof(f77,plain,(
    sP0(sK3,sK4,sK3) ),
    inference(resolution,[],[f51,f40])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f17,f18])).

fof(f18,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 = X2
      | k1_relset_1(X0,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f94,plain,(
    r2_hidden(sK4,k1_funct_2(k1_relat_1(sK4),sK3)) ),
    inference(resolution,[],[f87,f73])).

fof(f73,plain,(
    ! [X0,X1] : sP2(X0,X1,k1_funct_2(X0,X1)) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ~ sP2(X0,X1,X2) )
      & ( sP2(X0,X1,X2)
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> sP2(X0,X1,X2) ) ),
    inference(definition_folding,[],[f6,f21,f20])).

fof(f20,plain,(
    ! [X1,X0,X3] :
      ( sP1(X1,X0,X3)
    <=> ? [X4] :
          ( r1_tarski(k2_relat_1(X4),X1)
          & k1_relat_1(X4) = X0
          & X3 = X4
          & v1_funct_1(X4)
          & v1_relat_1(X4) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( sP2(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP1(X1,X0,X3) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r1_tarski(k2_relat_1(X4),X1)
              & k1_relat_1(X4) = X0
              & X3 = X4
              & v1_funct_1(X4)
              & v1_relat_1(X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_funct_2)).

fof(f87,plain,(
    ! [X0] :
      ( ~ sP2(k1_relat_1(sK4),sK3,X0)
      | r2_hidden(sK4,X0) ) ),
    inference(resolution,[],[f85,f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X1,X0,X4)
      | r2_hidden(X4,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( ( ~ sP1(X1,X0,sK5(X0,X1,X2))
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( sP1(X1,X0,sK5(X0,X1,X2))
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP1(X1,X0,X4) )
            & ( sP1(X1,X0,X4)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP1(X1,X0,X3)
            | ~ r2_hidden(X3,X2) )
          & ( sP1(X1,X0,X3)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP1(X1,X0,sK5(X0,X1,X2))
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( sP1(X1,X0,sK5(X0,X1,X2))
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP1(X1,X0,X3)
              | ~ r2_hidden(X3,X2) )
            & ( sP1(X1,X0,X3)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP1(X1,X0,X4) )
            & ( sP1(X1,X0,X4)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP1(X1,X0,X3)
              | ~ r2_hidden(X3,X2) )
            & ( sP1(X1,X0,X3)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP1(X1,X0,X3) )
            & ( sP1(X1,X0,X3)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f85,plain,(
    sP1(sK3,k1_relat_1(sK4),sK4) ),
    inference(resolution,[],[f84,f75])).

fof(f75,plain,(
    v5_relat_1(sK4,sK3) ),
    inference(resolution,[],[f46,f40])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f3])).

% (23828)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f84,plain,(
    ! [X0] :
      ( ~ v5_relat_1(sK4,X0)
      | sP1(X0,k1_relat_1(sK4),sK4) ) ),
    inference(subsumption_resolution,[],[f83,f74])).

% (23834)Refutation not found, incomplete strategy% (23834)------------------------------
% (23834)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f74,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f44,f40])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f83,plain,(
    ! [X0] :
      ( sP1(X0,k1_relat_1(sK4),sK4)
      | ~ v5_relat_1(sK4,X0)
      | ~ v1_relat_1(sK4) ) ),
    inference(resolution,[],[f81,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f81,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK4),X0)
      | sP1(X0,k1_relat_1(sK4),sK4) ) ),
    inference(subsumption_resolution,[],[f79,f74])).

fof(f79,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK4),X0)
      | sP1(X0,k1_relat_1(sK4),sK4)
      | ~ v1_relat_1(sK4) ) ),
    inference(resolution,[],[f72,f38])).

fof(f38,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f24])).

fof(f72,plain,(
    ! [X0,X3] :
      ( ~ v1_funct_1(X3)
      | ~ r1_tarski(k2_relat_1(X3),X0)
      | sP1(X0,k1_relat_1(X3),X3)
      | ~ v1_relat_1(X3) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X3] :
      ( sP1(X0,k1_relat_1(X3),X2)
      | ~ r1_tarski(k2_relat_1(X3),X0)
      | X2 != X3
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,X1,X2)
      | ~ r1_tarski(k2_relat_1(X3),X0)
      | k1_relat_1(X3) != X1
      | X2 != X3
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ! [X3] :
            ( ~ r1_tarski(k2_relat_1(X3),X0)
            | k1_relat_1(X3) != X1
            | X2 != X3
            | ~ v1_funct_1(X3)
            | ~ v1_relat_1(X3) ) )
      & ( ( r1_tarski(k2_relat_1(sK6(X0,X1,X2)),X0)
          & k1_relat_1(sK6(X0,X1,X2)) = X1
          & sK6(X0,X1,X2) = X2
          & v1_funct_1(sK6(X0,X1,X2))
          & v1_relat_1(sK6(X0,X1,X2)) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f34,f35])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r1_tarski(k2_relat_1(X4),X0)
          & k1_relat_1(X4) = X1
          & X2 = X4
          & v1_funct_1(X4)
          & v1_relat_1(X4) )
     => ( r1_tarski(k2_relat_1(sK6(X0,X1,X2)),X0)
        & k1_relat_1(sK6(X0,X1,X2)) = X1
        & sK6(X0,X1,X2) = X2
        & v1_funct_1(sK6(X0,X1,X2))
        & v1_relat_1(sK6(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ! [X3] :
            ( ~ r1_tarski(k2_relat_1(X3),X0)
            | k1_relat_1(X3) != X1
            | X2 != X3
            | ~ v1_funct_1(X3)
            | ~ v1_relat_1(X3) ) )
      & ( ? [X4] :
            ( r1_tarski(k2_relat_1(X4),X0)
            & k1_relat_1(X4) = X1
            & X2 = X4
            & v1_funct_1(X4)
            & v1_relat_1(X4) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X1,X0,X3] :
      ( ( sP1(X1,X0,X3)
        | ! [X4] :
            ( ~ r1_tarski(k2_relat_1(X4),X1)
            | k1_relat_1(X4) != X0
            | X3 != X4
            | ~ v1_funct_1(X4)
            | ~ v1_relat_1(X4) ) )
      & ( ? [X4] :
            ( r1_tarski(k2_relat_1(X4),X1)
            & k1_relat_1(X4) = X0
            & X3 = X4
            & v1_funct_1(X4)
            & v1_relat_1(X4) )
        | ~ sP1(X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f41,plain,(
    ~ r2_hidden(sK4,k1_funct_2(sK3,sK3)) ),
    inference(cnf_transformation,[],[f24])).

fof(f129,plain,(
    r2_hidden(sK4,k1_funct_2(k1_xboole_0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f117,f123])).

fof(f123,plain,(
    k1_xboole_0 = k1_relat_1(sK4) ),
    inference(backward_demodulation,[],[f112,f122])).

fof(f122,plain,(
    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) ),
    inference(subsumption_resolution,[],[f120,f107])).

fof(f107,plain,(
    v1_funct_2(sK4,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f39,f106])).

fof(f120,plain,
    ( ~ v1_funct_2(sK4,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) ),
    inference(resolution,[],[f111,f67])).

fof(f67,plain,(
    ! [X2,X1] :
      ( ~ sP0(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X1,k1_xboole_0,X2)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,X1) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 != X0
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f111,plain,(
    sP0(k1_xboole_0,sK4,k1_xboole_0) ),
    inference(backward_demodulation,[],[f77,f106])).

fof(f112,plain,(
    k1_relat_1(sK4) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) ),
    inference(backward_demodulation,[],[f78,f106])).

fof(f117,plain,(
    r2_hidden(sK4,k1_funct_2(k1_relat_1(sK4),k1_xboole_0)) ),
    inference(backward_demodulation,[],[f94,f106])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:32:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.37  ipcrm: permission denied for id (1214349313)
% 0.13/0.37  ipcrm: permission denied for id (1217921026)
% 0.13/0.37  ipcrm: permission denied for id (1217953795)
% 0.13/0.37  ipcrm: permission denied for id (1220804612)
% 0.13/0.37  ipcrm: permission denied for id (1218019333)
% 0.13/0.37  ipcrm: permission denied for id (1214513158)
% 0.13/0.38  ipcrm: permission denied for id (1218052103)
% 0.13/0.38  ipcrm: permission denied for id (1220902921)
% 0.13/0.38  ipcrm: permission denied for id (1220935690)
% 0.13/0.38  ipcrm: permission denied for id (1220968459)
% 0.13/0.38  ipcrm: permission denied for id (1218215948)
% 0.13/0.38  ipcrm: permission denied for id (1214709773)
% 0.13/0.38  ipcrm: permission denied for id (1214742542)
% 0.13/0.39  ipcrm: permission denied for id (1218248719)
% 0.13/0.39  ipcrm: permission denied for id (1218281488)
% 0.13/0.39  ipcrm: permission denied for id (1222377489)
% 0.13/0.39  ipcrm: permission denied for id (1218347026)
% 0.13/0.39  ipcrm: permission denied for id (1218379795)
% 0.13/0.39  ipcrm: permission denied for id (1222410260)
% 0.13/0.39  ipcrm: permission denied for id (1218445333)
% 0.13/0.40  ipcrm: permission denied for id (1214939158)
% 0.13/0.40  ipcrm: permission denied for id (1218478103)
% 0.13/0.40  ipcrm: permission denied for id (1218510872)
% 0.13/0.40  ipcrm: permission denied for id (1221066777)
% 0.13/0.40  ipcrm: permission denied for id (1215070234)
% 0.13/0.40  ipcrm: permission denied for id (1218576411)
% 0.13/0.40  ipcrm: permission denied for id (1215103004)
% 0.13/0.40  ipcrm: permission denied for id (1218609181)
% 0.13/0.41  ipcrm: permission denied for id (1221099550)
% 0.13/0.41  ipcrm: permission denied for id (1218674719)
% 0.13/0.41  ipcrm: permission denied for id (1215234080)
% 0.13/0.41  ipcrm: permission denied for id (1218707489)
% 0.13/0.41  ipcrm: permission denied for id (1218740258)
% 0.13/0.41  ipcrm: permission denied for id (1222443043)
% 0.13/0.41  ipcrm: permission denied for id (1221165092)
% 0.13/0.41  ipcrm: permission denied for id (1222475813)
% 0.13/0.42  ipcrm: permission denied for id (1215365158)
% 0.13/0.42  ipcrm: permission denied for id (1218871335)
% 0.13/0.42  ipcrm: permission denied for id (1218904104)
% 0.13/0.42  ipcrm: permission denied for id (1218936873)
% 0.13/0.42  ipcrm: permission denied for id (1218969642)
% 0.13/0.42  ipcrm: permission denied for id (1215463467)
% 0.13/0.42  ipcrm: permission denied for id (1221230636)
% 0.13/0.43  ipcrm: permission denied for id (1221263405)
% 0.21/0.43  ipcrm: permission denied for id (1215561774)
% 0.21/0.43  ipcrm: permission denied for id (1219133488)
% 0.21/0.43  ipcrm: permission denied for id (1221328945)
% 0.21/0.43  ipcrm: permission denied for id (1215692850)
% 0.21/0.43  ipcrm: permission denied for id (1215725619)
% 0.21/0.44  ipcrm: permission denied for id (1221427254)
% 0.21/0.44  ipcrm: permission denied for id (1215823927)
% 0.21/0.44  ipcrm: permission denied for id (1215856696)
% 0.21/0.44  ipcrm: permission denied for id (1219297337)
% 0.21/0.44  ipcrm: permission denied for id (1219330106)
% 0.21/0.44  ipcrm: permission denied for id (1215955003)
% 0.21/0.44  ipcrm: permission denied for id (1215987772)
% 0.21/0.45  ipcrm: permission denied for id (1221460029)
% 0.21/0.45  ipcrm: permission denied for id (1216020542)
% 0.21/0.45  ipcrm: permission denied for id (1222606911)
% 0.21/0.45  ipcrm: permission denied for id (1222639680)
% 0.21/0.45  ipcrm: permission denied for id (1216118849)
% 0.21/0.45  ipcrm: permission denied for id (1216151618)
% 0.21/0.45  ipcrm: permission denied for id (1216184387)
% 0.21/0.46  ipcrm: permission denied for id (1221558340)
% 0.21/0.46  ipcrm: permission denied for id (1216249925)
% 0.21/0.46  ipcrm: permission denied for id (1216282694)
% 0.21/0.46  ipcrm: permission denied for id (1216315463)
% 0.21/0.46  ipcrm: permission denied for id (1219526728)
% 0.21/0.46  ipcrm: permission denied for id (1219559497)
% 0.21/0.46  ipcrm: permission denied for id (1222672458)
% 0.21/0.46  ipcrm: permission denied for id (1219625035)
% 0.21/0.47  ipcrm: permission denied for id (1216413772)
% 0.21/0.47  ipcrm: permission denied for id (1216446541)
% 0.21/0.47  ipcrm: permission denied for id (1222705230)
% 0.21/0.47  ipcrm: permission denied for id (1221656655)
% 0.21/0.47  ipcrm: permission denied for id (1221689424)
% 0.21/0.47  ipcrm: permission denied for id (1216577617)
% 0.21/0.47  ipcrm: permission denied for id (1221722194)
% 0.21/0.48  ipcrm: permission denied for id (1216643155)
% 0.21/0.48  ipcrm: permission denied for id (1219788884)
% 0.21/0.48  ipcrm: permission denied for id (1221754965)
% 0.21/0.48  ipcrm: permission denied for id (1221787734)
% 0.21/0.48  ipcrm: permission denied for id (1219919960)
% 0.21/0.48  ipcrm: permission denied for id (1219952729)
% 0.21/0.48  ipcrm: permission denied for id (1219985498)
% 0.21/0.49  ipcrm: permission denied for id (1216872539)
% 0.21/0.49  ipcrm: permission denied for id (1221853276)
% 0.21/0.49  ipcrm: permission denied for id (1220083806)
% 0.21/0.49  ipcrm: permission denied for id (1216970847)
% 0.21/0.49  ipcrm: permission denied for id (1217003616)
% 0.21/0.49  ipcrm: permission denied for id (1220116577)
% 0.21/0.49  ipcrm: permission denied for id (1220149346)
% 0.21/0.50  ipcrm: permission denied for id (1220182115)
% 0.21/0.50  ipcrm: permission denied for id (1217101924)
% 0.21/0.50  ipcrm: permission denied for id (1221918821)
% 0.21/0.50  ipcrm: permission denied for id (1221951590)
% 0.21/0.50  ipcrm: permission denied for id (1220280423)
% 0.21/0.50  ipcrm: permission denied for id (1222803560)
% 0.21/0.50  ipcrm: permission denied for id (1222017129)
% 0.21/0.51  ipcrm: permission denied for id (1222049898)
% 0.21/0.51  ipcrm: permission denied for id (1217298539)
% 0.21/0.51  ipcrm: permission denied for id (1217331308)
% 0.21/0.51  ipcrm: permission denied for id (1217364077)
% 0.21/0.51  ipcrm: permission denied for id (1217396846)
% 0.21/0.51  ipcrm: permission denied for id (1220411503)
% 0.21/0.51  ipcrm: permission denied for id (1222082672)
% 0.21/0.51  ipcrm: permission denied for id (1222115441)
% 0.21/0.52  ipcrm: permission denied for id (1217495154)
% 0.21/0.52  ipcrm: permission denied for id (1222148211)
% 0.21/0.52  ipcrm: permission denied for id (1222180980)
% 0.21/0.52  ipcrm: permission denied for id (1222836341)
% 0.21/0.52  ipcrm: permission denied for id (1220608118)
% 0.21/0.52  ipcrm: permission denied for id (1217626231)
% 0.21/0.52  ipcrm: permission denied for id (1220640888)
% 0.21/0.53  ipcrm: permission denied for id (1217691769)
% 0.21/0.53  ipcrm: permission denied for id (1217724538)
% 0.21/0.53  ipcrm: permission denied for id (1217790076)
% 0.21/0.53  ipcrm: permission denied for id (1217822845)
% 0.21/0.53  ipcrm: permission denied for id (1220706430)
% 1.08/0.66  % (23829)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.08/0.66  % (23842)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.08/0.67  % (23834)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.08/0.67  % (23829)Refutation found. Thanks to Tanya!
% 1.08/0.67  % SZS status Theorem for theBenchmark
% 1.08/0.67  % SZS output start Proof for theBenchmark
% 1.08/0.67  fof(f131,plain,(
% 1.08/0.67    $false),
% 1.08/0.67    inference(subsumption_resolution,[],[f129,f109])).
% 1.08/0.67  fof(f109,plain,(
% 1.08/0.67    ~r2_hidden(sK4,k1_funct_2(k1_xboole_0,k1_xboole_0))),
% 1.08/0.67    inference(backward_demodulation,[],[f41,f106])).
% 1.08/0.67  fof(f106,plain,(
% 1.08/0.67    k1_xboole_0 = sK3),
% 1.08/0.67    inference(subsumption_resolution,[],[f102,f41])).
% 1.08/0.67  fof(f102,plain,(
% 1.08/0.67    r2_hidden(sK4,k1_funct_2(sK3,sK3)) | k1_xboole_0 = sK3),
% 1.08/0.67    inference(superposition,[],[f94,f99])).
% 1.08/0.67  fof(f99,plain,(
% 1.08/0.67    sK3 = k1_relat_1(sK4) | k1_xboole_0 = sK3),
% 1.08/0.67    inference(superposition,[],[f98,f78])).
% 1.08/0.67  fof(f78,plain,(
% 1.08/0.67    k1_relat_1(sK4) = k1_relset_1(sK3,sK3,sK4)),
% 1.08/0.67    inference(resolution,[],[f45,f40])).
% 1.08/0.67  fof(f40,plain,(
% 1.08/0.67    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))),
% 1.08/0.67    inference(cnf_transformation,[],[f24])).
% 1.08/0.67  fof(f24,plain,(
% 1.08/0.67    ~r2_hidden(sK4,k1_funct_2(sK3,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) & v1_funct_2(sK4,sK3,sK3) & v1_funct_1(sK4)),
% 1.08/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f11,f23])).
% 1.08/0.67  fof(f23,plain,(
% 1.08/0.67    ? [X0,X1] : (~r2_hidden(X1,k1_funct_2(X0,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (~r2_hidden(sK4,k1_funct_2(sK3,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) & v1_funct_2(sK4,sK3,sK3) & v1_funct_1(sK4))),
% 1.08/0.67    introduced(choice_axiom,[])).
% 1.08/0.67  fof(f11,plain,(
% 1.08/0.67    ? [X0,X1] : (~r2_hidden(X1,k1_funct_2(X0,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.08/0.67    inference(flattening,[],[f10])).
% 1.08/0.67  fof(f10,plain,(
% 1.08/0.67    ? [X0,X1] : (~r2_hidden(X1,k1_funct_2(X0,X0)) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 1.08/0.67    inference(ennf_transformation,[],[f8])).
% 1.08/0.67  fof(f8,negated_conjecture,(
% 1.08/0.67    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => r2_hidden(X1,k1_funct_2(X0,X0)))),
% 1.08/0.67    inference(negated_conjecture,[],[f7])).
% 1.08/0.67  fof(f7,conjecture,(
% 1.08/0.67    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => r2_hidden(X1,k1_funct_2(X0,X0)))),
% 1.08/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_2)).
% 1.08/0.67  fof(f45,plain,(
% 1.08/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.08/0.67    inference(cnf_transformation,[],[f14])).
% 1.08/0.67  fof(f14,plain,(
% 1.08/0.67    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.08/0.67    inference(ennf_transformation,[],[f4])).
% 1.08/0.67  % (23830)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.08/0.67  fof(f4,axiom,(
% 1.08/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.08/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.08/0.67  fof(f98,plain,(
% 1.08/0.67    sK3 = k1_relset_1(sK3,sK3,sK4) | k1_xboole_0 = sK3),
% 1.08/0.67    inference(subsumption_resolution,[],[f97,f39])).
% 1.08/0.67  fof(f39,plain,(
% 1.08/0.67    v1_funct_2(sK4,sK3,sK3)),
% 1.08/0.67    inference(cnf_transformation,[],[f24])).
% 1.08/0.67  fof(f97,plain,(
% 1.08/0.67    ~v1_funct_2(sK4,sK3,sK3) | k1_xboole_0 = sK3 | sK3 = k1_relset_1(sK3,sK3,sK4)),
% 1.08/0.67    inference(resolution,[],[f47,f77])).
% 1.08/0.67  fof(f77,plain,(
% 1.08/0.67    sP0(sK3,sK4,sK3)),
% 1.08/0.67    inference(resolution,[],[f51,f40])).
% 1.08/0.67  fof(f51,plain,(
% 1.08/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X2,X1)) )),
% 1.08/0.67    inference(cnf_transformation,[],[f28])).
% 1.08/0.67  fof(f28,plain,(
% 1.08/0.67    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.08/0.67    inference(nnf_transformation,[],[f19])).
% 1.08/0.67  fof(f19,plain,(
% 1.08/0.67    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.08/0.67    inference(definition_folding,[],[f17,f18])).
% 1.08/0.67  fof(f18,plain,(
% 1.08/0.67    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.08/0.67    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.08/0.67  fof(f17,plain,(
% 1.08/0.67    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.08/0.67    inference(flattening,[],[f16])).
% 1.08/0.67  fof(f16,plain,(
% 1.08/0.67    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.08/0.67    inference(ennf_transformation,[],[f5])).
% 1.08/0.67  fof(f5,axiom,(
% 1.08/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.08/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.08/0.67  fof(f47,plain,(
% 1.08/0.67    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 = X2 | k1_relset_1(X0,X2,X1) = X0) )),
% 1.08/0.67    inference(cnf_transformation,[],[f27])).
% 1.08/0.67  fof(f27,plain,(
% 1.08/0.67    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 1.08/0.67    inference(rectify,[],[f26])).
% 1.08/0.67  fof(f26,plain,(
% 1.08/0.67    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.08/0.67    inference(nnf_transformation,[],[f18])).
% 1.08/0.67  fof(f94,plain,(
% 1.08/0.67    r2_hidden(sK4,k1_funct_2(k1_relat_1(sK4),sK3))),
% 1.08/0.67    inference(resolution,[],[f87,f73])).
% 1.08/0.67  fof(f73,plain,(
% 1.08/0.67    ( ! [X0,X1] : (sP2(X0,X1,k1_funct_2(X0,X1))) )),
% 1.08/0.67    inference(equality_resolution,[],[f64])).
% 1.08/0.67  fof(f64,plain,(
% 1.08/0.67    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | k1_funct_2(X0,X1) != X2) )),
% 1.08/0.67    inference(cnf_transformation,[],[f37])).
% 1.08/0.67  fof(f37,plain,(
% 1.08/0.67    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ~sP2(X0,X1,X2)) & (sP2(X0,X1,X2) | k1_funct_2(X0,X1) != X2))),
% 1.08/0.67    inference(nnf_transformation,[],[f22])).
% 1.08/0.67  fof(f22,plain,(
% 1.08/0.67    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> sP2(X0,X1,X2))),
% 1.08/0.67    inference(definition_folding,[],[f6,f21,f20])).
% 1.08/0.67  fof(f20,plain,(
% 1.08/0.67    ! [X1,X0,X3] : (sP1(X1,X0,X3) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)))),
% 1.08/0.67    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.08/0.67  fof(f21,plain,(
% 1.08/0.67    ! [X0,X1,X2] : (sP2(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP1(X1,X0,X3)))),
% 1.08/0.67    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.08/0.67  fof(f6,axiom,(
% 1.08/0.67    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 1.08/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_funct_2)).
% 1.08/0.67  fof(f87,plain,(
% 1.08/0.67    ( ! [X0] : (~sP2(k1_relat_1(sK4),sK3,X0) | r2_hidden(sK4,X0)) )),
% 1.08/0.67    inference(resolution,[],[f85,f55])).
% 1.08/0.67  fof(f55,plain,(
% 1.08/0.67    ( ! [X4,X2,X0,X1] : (~sP1(X1,X0,X4) | r2_hidden(X4,X2) | ~sP2(X0,X1,X2)) )),
% 1.08/0.67    inference(cnf_transformation,[],[f32])).
% 1.08/0.67  fof(f32,plain,(
% 1.08/0.67    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ((~sP1(X1,X0,sK5(X0,X1,X2)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sP1(X1,X0,sK5(X0,X1,X2)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP1(X1,X0,X4)) & (sP1(X1,X0,X4) | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 1.08/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f31])).
% 1.08/0.67  fof(f31,plain,(
% 1.08/0.67    ! [X2,X1,X0] : (? [X3] : ((~sP1(X1,X0,X3) | ~r2_hidden(X3,X2)) & (sP1(X1,X0,X3) | r2_hidden(X3,X2))) => ((~sP1(X1,X0,sK5(X0,X1,X2)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sP1(X1,X0,sK5(X0,X1,X2)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.08/0.67    introduced(choice_axiom,[])).
% 1.08/0.67  fof(f30,plain,(
% 1.08/0.67    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : ((~sP1(X1,X0,X3) | ~r2_hidden(X3,X2)) & (sP1(X1,X0,X3) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP1(X1,X0,X4)) & (sP1(X1,X0,X4) | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 1.08/0.67    inference(rectify,[],[f29])).
% 1.08/0.67  fof(f29,plain,(
% 1.08/0.67    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : ((~sP1(X1,X0,X3) | ~r2_hidden(X3,X2)) & (sP1(X1,X0,X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP1(X1,X0,X3)) & (sP1(X1,X0,X3) | ~r2_hidden(X3,X2))) | ~sP2(X0,X1,X2)))),
% 1.08/0.67    inference(nnf_transformation,[],[f21])).
% 1.08/0.67  fof(f85,plain,(
% 1.08/0.67    sP1(sK3,k1_relat_1(sK4),sK4)),
% 1.08/0.67    inference(resolution,[],[f84,f75])).
% 1.08/0.67  fof(f75,plain,(
% 1.08/0.67    v5_relat_1(sK4,sK3)),
% 1.08/0.67    inference(resolution,[],[f46,f40])).
% 1.08/0.67  fof(f46,plain,(
% 1.08/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.08/0.67    inference(cnf_transformation,[],[f15])).
% 1.08/0.67  fof(f15,plain,(
% 1.08/0.67    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.08/0.67    inference(ennf_transformation,[],[f9])).
% 1.08/0.67  fof(f9,plain,(
% 1.08/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.08/0.67    inference(pure_predicate_removal,[],[f3])).
% 1.08/0.67  % (23828)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.08/0.67  fof(f3,axiom,(
% 1.08/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.08/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.08/0.67  fof(f84,plain,(
% 1.08/0.67    ( ! [X0] : (~v5_relat_1(sK4,X0) | sP1(X0,k1_relat_1(sK4),sK4)) )),
% 1.08/0.67    inference(subsumption_resolution,[],[f83,f74])).
% 1.08/0.67  % (23834)Refutation not found, incomplete strategy% (23834)------------------------------
% 1.08/0.67  % (23834)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.08/0.67  fof(f74,plain,(
% 1.08/0.67    v1_relat_1(sK4)),
% 1.08/0.67    inference(resolution,[],[f44,f40])).
% 1.08/0.67  fof(f44,plain,(
% 1.08/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.08/0.67    inference(cnf_transformation,[],[f13])).
% 1.08/0.67  fof(f13,plain,(
% 1.08/0.67    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.08/0.67    inference(ennf_transformation,[],[f2])).
% 1.08/0.67  fof(f2,axiom,(
% 1.08/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.08/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.08/0.67  fof(f83,plain,(
% 1.08/0.67    ( ! [X0] : (sP1(X0,k1_relat_1(sK4),sK4) | ~v5_relat_1(sK4,X0) | ~v1_relat_1(sK4)) )),
% 1.08/0.67    inference(resolution,[],[f81,f42])).
% 1.08/0.67  fof(f42,plain,(
% 1.08/0.67    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.08/0.67    inference(cnf_transformation,[],[f25])).
% 1.08/0.67  fof(f25,plain,(
% 1.08/0.67    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.08/0.67    inference(nnf_transformation,[],[f12])).
% 1.08/0.67  fof(f12,plain,(
% 1.08/0.67    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.08/0.67    inference(ennf_transformation,[],[f1])).
% 1.08/0.67  fof(f1,axiom,(
% 1.08/0.67    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.08/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 1.08/0.67  fof(f81,plain,(
% 1.08/0.67    ( ! [X0] : (~r1_tarski(k2_relat_1(sK4),X0) | sP1(X0,k1_relat_1(sK4),sK4)) )),
% 1.08/0.67    inference(subsumption_resolution,[],[f79,f74])).
% 1.08/0.67  fof(f79,plain,(
% 1.08/0.67    ( ! [X0] : (~r1_tarski(k2_relat_1(sK4),X0) | sP1(X0,k1_relat_1(sK4),sK4) | ~v1_relat_1(sK4)) )),
% 1.08/0.67    inference(resolution,[],[f72,f38])).
% 1.08/0.67  fof(f38,plain,(
% 1.08/0.67    v1_funct_1(sK4)),
% 1.08/0.67    inference(cnf_transformation,[],[f24])).
% 1.08/0.67  fof(f72,plain,(
% 1.08/0.67    ( ! [X0,X3] : (~v1_funct_1(X3) | ~r1_tarski(k2_relat_1(X3),X0) | sP1(X0,k1_relat_1(X3),X3) | ~v1_relat_1(X3)) )),
% 1.08/0.67    inference(equality_resolution,[],[f71])).
% 1.08/0.67  fof(f71,plain,(
% 1.08/0.67    ( ! [X2,X0,X3] : (sP1(X0,k1_relat_1(X3),X2) | ~r1_tarski(k2_relat_1(X3),X0) | X2 != X3 | ~v1_funct_1(X3) | ~v1_relat_1(X3)) )),
% 1.08/0.67    inference(equality_resolution,[],[f63])).
% 1.08/0.67  fof(f63,plain,(
% 1.08/0.67    ( ! [X2,X0,X3,X1] : (sP1(X0,X1,X2) | ~r1_tarski(k2_relat_1(X3),X0) | k1_relat_1(X3) != X1 | X2 != X3 | ~v1_funct_1(X3) | ~v1_relat_1(X3)) )),
% 1.08/0.67    inference(cnf_transformation,[],[f36])).
% 1.08/0.67  fof(f36,plain,(
% 1.08/0.67    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ! [X3] : (~r1_tarski(k2_relat_1(X3),X0) | k1_relat_1(X3) != X1 | X2 != X3 | ~v1_funct_1(X3) | ~v1_relat_1(X3))) & ((r1_tarski(k2_relat_1(sK6(X0,X1,X2)),X0) & k1_relat_1(sK6(X0,X1,X2)) = X1 & sK6(X0,X1,X2) = X2 & v1_funct_1(sK6(X0,X1,X2)) & v1_relat_1(sK6(X0,X1,X2))) | ~sP1(X0,X1,X2)))),
% 1.08/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f34,f35])).
% 1.08/0.67  fof(f35,plain,(
% 1.08/0.67    ! [X2,X1,X0] : (? [X4] : (r1_tarski(k2_relat_1(X4),X0) & k1_relat_1(X4) = X1 & X2 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) => (r1_tarski(k2_relat_1(sK6(X0,X1,X2)),X0) & k1_relat_1(sK6(X0,X1,X2)) = X1 & sK6(X0,X1,X2) = X2 & v1_funct_1(sK6(X0,X1,X2)) & v1_relat_1(sK6(X0,X1,X2))))),
% 1.08/0.67    introduced(choice_axiom,[])).
% 1.08/0.67  fof(f34,plain,(
% 1.08/0.67    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ! [X3] : (~r1_tarski(k2_relat_1(X3),X0) | k1_relat_1(X3) != X1 | X2 != X3 | ~v1_funct_1(X3) | ~v1_relat_1(X3))) & (? [X4] : (r1_tarski(k2_relat_1(X4),X0) & k1_relat_1(X4) = X1 & X2 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | ~sP1(X0,X1,X2)))),
% 1.08/0.67    inference(rectify,[],[f33])).
% 1.08/0.67  fof(f33,plain,(
% 1.08/0.67    ! [X1,X0,X3] : ((sP1(X1,X0,X3) | ! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4))) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | ~sP1(X1,X0,X3)))),
% 1.08/0.67    inference(nnf_transformation,[],[f20])).
% 1.08/0.67  fof(f41,plain,(
% 1.08/0.67    ~r2_hidden(sK4,k1_funct_2(sK3,sK3))),
% 1.08/0.67    inference(cnf_transformation,[],[f24])).
% 1.08/0.67  fof(f129,plain,(
% 1.08/0.67    r2_hidden(sK4,k1_funct_2(k1_xboole_0,k1_xboole_0))),
% 1.08/0.67    inference(backward_demodulation,[],[f117,f123])).
% 1.08/0.67  fof(f123,plain,(
% 1.08/0.67    k1_xboole_0 = k1_relat_1(sK4)),
% 1.08/0.67    inference(backward_demodulation,[],[f112,f122])).
% 1.08/0.67  fof(f122,plain,(
% 1.08/0.67    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK4)),
% 1.08/0.67    inference(subsumption_resolution,[],[f120,f107])).
% 1.08/0.67  fof(f107,plain,(
% 1.08/0.67    v1_funct_2(sK4,k1_xboole_0,k1_xboole_0)),
% 1.08/0.67    inference(backward_demodulation,[],[f39,f106])).
% 1.08/0.67  fof(f120,plain,(
% 1.08/0.67    ~v1_funct_2(sK4,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK4)),
% 1.08/0.67    inference(resolution,[],[f111,f67])).
% 1.08/0.68  fof(f67,plain,(
% 1.08/0.68    ( ! [X2,X1] : (~sP0(k1_xboole_0,X1,X2) | ~v1_funct_2(X1,k1_xboole_0,X2) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,X1)) )),
% 1.08/0.68    inference(equality_resolution,[],[f48])).
% 1.08/0.68  fof(f48,plain,(
% 1.08/0.68    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 != X0 | ~sP0(X0,X1,X2)) )),
% 1.08/0.68    inference(cnf_transformation,[],[f27])).
% 1.08/0.68  fof(f111,plain,(
% 1.08/0.68    sP0(k1_xboole_0,sK4,k1_xboole_0)),
% 1.08/0.68    inference(backward_demodulation,[],[f77,f106])).
% 1.08/0.68  fof(f112,plain,(
% 1.08/0.68    k1_relat_1(sK4) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK4)),
% 1.08/0.68    inference(backward_demodulation,[],[f78,f106])).
% 1.08/0.68  fof(f117,plain,(
% 1.08/0.68    r2_hidden(sK4,k1_funct_2(k1_relat_1(sK4),k1_xboole_0))),
% 1.08/0.68    inference(backward_demodulation,[],[f94,f106])).
% 1.08/0.68  % SZS output end Proof for theBenchmark
% 1.08/0.68  % (23829)------------------------------
% 1.08/0.68  % (23829)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.08/0.68  % (23829)Termination reason: Refutation
% 1.08/0.68  
% 1.08/0.68  % (23829)Memory used [KB]: 6268
% 1.08/0.68  % (23829)Time elapsed: 0.092 s
% 1.08/0.68  % (23829)------------------------------
% 1.08/0.68  % (23829)------------------------------
% 1.08/0.68  % (23834)Termination reason: Refutation not found, incomplete strategy
% 1.08/0.68  
% 1.08/0.68  % (23834)Memory used [KB]: 1663
% 1.08/0.68  % (23834)Time elapsed: 0.028 s
% 1.08/0.68  % (23834)------------------------------
% 1.08/0.68  % (23834)------------------------------
% 1.08/0.68  % (23838)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.08/0.68  % (23599)Success in time 0.318 s
%------------------------------------------------------------------------------
