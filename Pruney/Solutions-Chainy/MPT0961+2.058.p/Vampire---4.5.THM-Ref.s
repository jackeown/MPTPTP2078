%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:19 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 240 expanded)
%              Number of leaves         :   19 (  72 expanded)
%              Depth                    :   14
%              Number of atoms          :  320 ( 927 expanded)
%              Number of equality atoms :   67 ( 125 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f279,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f78,f104,f107,f258,f267,f275,f278])).

fof(f278,plain,
    ( ~ spl5_6
    | spl5_13 ),
    inference(avatar_contradiction_clause,[],[f277])).

fof(f277,plain,
    ( $false
    | ~ spl5_6
    | spl5_13 ),
    inference(subsumption_resolution,[],[f276,f40])).

fof(f40,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f276,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl5_6
    | spl5_13 ),
    inference(forward_demodulation,[],[f266,f102])).

fof(f102,plain,
    ( k1_xboole_0 = k2_relat_1(sK3)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl5_6
  <=> k1_xboole_0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f266,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0)
    | spl5_13 ),
    inference(avatar_component_clause,[],[f264])).

fof(f264,plain,
    ( spl5_13
  <=> r1_tarski(k2_relat_1(sK3),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f275,plain,
    ( spl5_6
    | spl5_2 ),
    inference(avatar_split_clause,[],[f244,f70,f101])).

fof(f70,plain,
    ( spl5_2
  <=> v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f244,plain,
    ( k1_xboole_0 = k2_relat_1(sK3)
    | spl5_2 ),
    inference(resolution,[],[f243,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f243,plain,
    ( sP0(k1_relat_1(sK3),k2_relat_1(sK3))
    | spl5_2 ),
    inference(subsumption_resolution,[],[f242,f37])).

fof(f37,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
      | ~ v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3))
      | ~ v1_funct_1(sK3) )
    & v1_funct_1(sK3)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f11,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          | ~ v1_funct_1(X0) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
        | ~ v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3))
        | ~ v1_funct_1(sK3) )
      & v1_funct_1(sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          & v1_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f242,plain,
    ( sP0(k1_relat_1(sK3),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f241,f80])).

fof(f80,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f79])).

fof(f79,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f45,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
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

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f241,plain,
    ( sP0(k1_relat_1(sK3),k2_relat_1(sK3))
    | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f240,f80])).

fof(f240,plain,
    ( sP0(k1_relat_1(sK3),k2_relat_1(sK3))
    | ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3))
    | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl5_2 ),
    inference(trivial_inequality_removal,[],[f230])).

fof(f230,plain,
    ( sP0(k1_relat_1(sK3),k2_relat_1(sK3))
    | k1_relat_1(sK3) != k1_relat_1(sK3)
    | ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3))
    | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl5_2 ),
    inference(resolution,[],[f181,f72])).

fof(f72,plain,
    ( ~ v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f181,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X0,X1,X2)
      | sP0(X1,X2)
      | k1_relat_1(X0) != X1
      | ~ r1_tarski(k2_relat_1(X0),X2)
      | ~ r1_tarski(k1_relat_1(X0),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f173,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f173,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | v1_funct_2(X5,X3,X4)
      | sP0(X3,X4)
      | k1_relat_1(X5) != X3 ) ),
    inference(subsumption_resolution,[],[f171,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X2,X1,X0)
        & sP1(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f18,f21,f20,f19])).

fof(f20,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP2(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f171,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) != X3
      | v1_funct_2(X5,X3,X4)
      | sP0(X3,X4)
      | ~ sP1(X3,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f54,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) != X0
      | v1_funct_2(X1,X0,X2)
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f34])).

% (31573)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
fof(f34,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f267,plain,
    ( ~ spl5_13
    | ~ spl5_4
    | spl5_5 ),
    inference(avatar_split_clause,[],[f262,f90,f86,f264])).

fof(f86,plain,
    ( spl5_4
  <=> k1_xboole_0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

% (31579)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f90,plain,
    ( spl5_5
  <=> v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

% (31576)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f262,plain,
    ( k1_xboole_0 != k1_relat_1(sK3)
    | ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0)
    | spl5_5 ),
    inference(subsumption_resolution,[],[f261,f40])).

fof(f261,plain,
    ( k1_xboole_0 != k1_relat_1(sK3)
    | ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl5_5 ),
    inference(inner_rewriting,[],[f260])).

fof(f260,plain,
    ( k1_xboole_0 != k1_relat_1(sK3)
    | ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0)
    | ~ r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | spl5_5 ),
    inference(subsumption_resolution,[],[f259,f37])).

fof(f259,plain,
    ( k1_xboole_0 != k1_relat_1(sK3)
    | ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0)
    | ~ r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | ~ v1_relat_1(sK3)
    | spl5_5 ),
    inference(subsumption_resolution,[],[f231,f64])).

fof(f64,plain,(
    ! [X1] : ~ sP0(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f231,plain,
    ( sP0(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(sK3)
    | ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0)
    | ~ r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | ~ v1_relat_1(sK3)
    | spl5_5 ),
    inference(resolution,[],[f181,f92])).

fof(f92,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f90])).

fof(f258,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f257])).

fof(f257,plain,
    ( $false
    | spl5_3 ),
    inference(subsumption_resolution,[],[f256,f37])).

fof(f256,plain,
    ( ~ v1_relat_1(sK3)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f255,f80])).

fof(f255,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f252,f80])).

fof(f252,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3))
    | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl5_3 ),
    inference(resolution,[],[f76,f49])).

fof(f76,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl5_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f107,plain,
    ( ~ spl5_6
    | spl5_4 ),
    inference(avatar_split_clause,[],[f97,f86,f101])).

fof(f97,plain,
    ( k1_xboole_0 != k2_relat_1(sK3)
    | spl5_4 ),
    inference(subsumption_resolution,[],[f96,f37])).

fof(f96,plain,
    ( k1_xboole_0 != k2_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl5_4 ),
    inference(trivial_inequality_removal,[],[f94])).

fof(f94,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k2_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl5_4 ),
    inference(superposition,[],[f88,f42])).

fof(f42,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(f88,plain,
    ( k1_xboole_0 != k1_relat_1(sK3)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f86])).

fof(f104,plain,
    ( ~ spl5_6
    | ~ spl5_5
    | spl5_2 ),
    inference(avatar_split_clause,[],[f99,f70,f90,f101])).

fof(f99,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k2_relat_1(sK3)
    | spl5_2 ),
    inference(inner_rewriting,[],[f98])).

fof(f98,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,k2_relat_1(sK3))
    | k1_xboole_0 != k2_relat_1(sK3)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f95,f37])).

fof(f95,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,k2_relat_1(sK3))
    | k1_xboole_0 != k2_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl5_2 ),
    inference(superposition,[],[f72,f42])).

fof(f78,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f38,f66])).

fof(f66,plain,
    ( spl5_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f38,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f77,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f39,f74,f70,f66])).

fof(f39,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
    | ~ v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.08  % Command    : run_vampire %s %d
% 0.08/0.27  % Computer   : n015.cluster.edu
% 0.08/0.27  % Model      : x86_64 x86_64
% 0.08/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.27  % Memory     : 8042.1875MB
% 0.08/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.27  % CPULimit   : 60
% 0.08/0.27  % WCLimit    : 600
% 0.08/0.27  % DateTime   : Tue Dec  1 10:00:23 EST 2020
% 0.08/0.27  % CPUTime    : 
% 0.12/0.38  % (31578)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.12/0.40  % (31578)Refutation not found, incomplete strategy% (31578)------------------------------
% 0.12/0.40  % (31578)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.40  % (31570)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.12/0.40  % (31578)Termination reason: Refutation not found, incomplete strategy
% 0.12/0.40  
% 0.12/0.40  % (31578)Memory used [KB]: 10746
% 0.12/0.40  % (31578)Time elapsed: 0.085 s
% 0.12/0.40  % (31578)------------------------------
% 0.12/0.40  % (31578)------------------------------
% 0.12/0.42  % (31594)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.12/0.42  % (31586)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.12/0.43  % (31571)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.12/0.43  % (31571)Refutation not found, incomplete strategy% (31571)------------------------------
% 0.12/0.43  % (31571)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.43  % (31571)Termination reason: Refutation not found, incomplete strategy
% 0.12/0.43  
% 0.12/0.43  % (31571)Memory used [KB]: 6140
% 0.12/0.43  % (31571)Time elapsed: 0.094 s
% 0.12/0.43  % (31571)------------------------------
% 0.12/0.43  % (31571)------------------------------
% 0.12/0.43  % (31572)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.12/0.43  % (31595)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.12/0.44  % (31594)Refutation found. Thanks to Tanya!
% 0.12/0.44  % SZS status Theorem for theBenchmark
% 0.12/0.44  % SZS output start Proof for theBenchmark
% 0.12/0.44  fof(f279,plain,(
% 0.12/0.44    $false),
% 0.12/0.44    inference(avatar_sat_refutation,[],[f77,f78,f104,f107,f258,f267,f275,f278])).
% 0.12/0.44  fof(f278,plain,(
% 0.12/0.44    ~spl5_6 | spl5_13),
% 0.12/0.44    inference(avatar_contradiction_clause,[],[f277])).
% 0.12/0.44  fof(f277,plain,(
% 0.12/0.44    $false | (~spl5_6 | spl5_13)),
% 0.12/0.44    inference(subsumption_resolution,[],[f276,f40])).
% 0.12/0.44  fof(f40,plain,(
% 0.12/0.44    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.12/0.44    inference(cnf_transformation,[],[f2])).
% 0.12/0.44  fof(f2,axiom,(
% 0.12/0.44    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.12/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.12/0.44  fof(f276,plain,(
% 0.12/0.44    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl5_6 | spl5_13)),
% 0.12/0.44    inference(forward_demodulation,[],[f266,f102])).
% 0.12/0.44  fof(f102,plain,(
% 0.12/0.44    k1_xboole_0 = k2_relat_1(sK3) | ~spl5_6),
% 0.12/0.44    inference(avatar_component_clause,[],[f101])).
% 0.12/0.44  fof(f101,plain,(
% 0.12/0.44    spl5_6 <=> k1_xboole_0 = k2_relat_1(sK3)),
% 0.12/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.12/0.44  fof(f266,plain,(
% 0.12/0.44    ~r1_tarski(k2_relat_1(sK3),k1_xboole_0) | spl5_13),
% 0.12/0.44    inference(avatar_component_clause,[],[f264])).
% 0.12/0.44  fof(f264,plain,(
% 0.12/0.44    spl5_13 <=> r1_tarski(k2_relat_1(sK3),k1_xboole_0)),
% 0.12/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.12/0.44  fof(f275,plain,(
% 0.12/0.44    spl5_6 | spl5_2),
% 0.12/0.44    inference(avatar_split_clause,[],[f244,f70,f101])).
% 0.12/0.44  fof(f70,plain,(
% 0.12/0.44    spl5_2 <=> v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3))),
% 0.12/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.12/0.44  fof(f244,plain,(
% 0.12/0.44    k1_xboole_0 = k2_relat_1(sK3) | spl5_2),
% 0.12/0.44    inference(resolution,[],[f243,f55])).
% 0.12/0.44  fof(f55,plain,(
% 0.12/0.44    ( ! [X0,X1] : (~sP0(X0,X1) | k1_xboole_0 = X1) )),
% 0.12/0.44    inference(cnf_transformation,[],[f36])).
% 0.12/0.44  fof(f36,plain,(
% 0.12/0.44    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 0.12/0.44    inference(nnf_transformation,[],[f19])).
% 0.12/0.44  fof(f19,plain,(
% 0.12/0.44    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 0.12/0.44    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.12/0.44  fof(f243,plain,(
% 0.12/0.44    sP0(k1_relat_1(sK3),k2_relat_1(sK3)) | spl5_2),
% 0.12/0.44    inference(subsumption_resolution,[],[f242,f37])).
% 0.12/0.44  fof(f37,plain,(
% 0.12/0.44    v1_relat_1(sK3)),
% 0.12/0.44    inference(cnf_transformation,[],[f24])).
% 0.12/0.44  fof(f24,plain,(
% 0.12/0.44    (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | ~v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) | ~v1_funct_1(sK3)) & v1_funct_1(sK3) & v1_relat_1(sK3)),
% 0.12/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f11,f23])).
% 0.12/0.44  fof(f23,plain,(
% 0.12/0.44    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0)) => ((~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | ~v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) | ~v1_funct_1(sK3)) & v1_funct_1(sK3) & v1_relat_1(sK3))),
% 0.12/0.44    introduced(choice_axiom,[])).
% 0.12/0.44  fof(f11,plain,(
% 0.12/0.44    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.12/0.44    inference(flattening,[],[f10])).
% 0.12/0.44  fof(f10,plain,(
% 0.12/0.44    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.12/0.44    inference(ennf_transformation,[],[f9])).
% 0.12/0.44  fof(f9,negated_conjecture,(
% 0.12/0.44    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.12/0.44    inference(negated_conjecture,[],[f8])).
% 0.12/0.44  fof(f8,conjecture,(
% 0.12/0.44    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.12/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 0.12/0.44  fof(f242,plain,(
% 0.12/0.44    sP0(k1_relat_1(sK3),k2_relat_1(sK3)) | ~v1_relat_1(sK3) | spl5_2),
% 0.12/0.44    inference(subsumption_resolution,[],[f241,f80])).
% 0.12/0.44  fof(f80,plain,(
% 0.12/0.44    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.12/0.44    inference(duplicate_literal_removal,[],[f79])).
% 0.12/0.44  fof(f79,plain,(
% 0.12/0.44    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 0.12/0.44    inference(resolution,[],[f45,f44])).
% 0.12/0.44  fof(f44,plain,(
% 0.12/0.44    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.12/0.44    inference(cnf_transformation,[],[f29])).
% 0.12/0.44  fof(f29,plain,(
% 0.12/0.44    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.12/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f28])).
% 0.12/0.44  fof(f28,plain,(
% 0.12/0.44    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.12/0.44    introduced(choice_axiom,[])).
% 0.12/0.44  fof(f27,plain,(
% 0.12/0.44    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.12/0.44    inference(rectify,[],[f26])).
% 0.12/0.44  fof(f26,plain,(
% 0.12/0.44    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.12/0.44    inference(nnf_transformation,[],[f13])).
% 0.12/0.44  fof(f13,plain,(
% 0.12/0.44    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.12/0.44    inference(ennf_transformation,[],[f1])).
% 0.12/0.44  fof(f1,axiom,(
% 0.12/0.44    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.12/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.12/0.44  fof(f45,plain,(
% 0.12/0.44    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.12/0.44    inference(cnf_transformation,[],[f29])).
% 0.12/0.44  fof(f241,plain,(
% 0.12/0.44    sP0(k1_relat_1(sK3),k2_relat_1(sK3)) | ~r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) | ~v1_relat_1(sK3) | spl5_2),
% 0.12/0.44    inference(subsumption_resolution,[],[f240,f80])).
% 0.12/0.44  fof(f240,plain,(
% 0.12/0.44    sP0(k1_relat_1(sK3),k2_relat_1(sK3)) | ~r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3)) | ~r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) | ~v1_relat_1(sK3) | spl5_2),
% 0.12/0.44    inference(trivial_inequality_removal,[],[f230])).
% 0.12/0.44  fof(f230,plain,(
% 0.12/0.44    sP0(k1_relat_1(sK3),k2_relat_1(sK3)) | k1_relat_1(sK3) != k1_relat_1(sK3) | ~r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3)) | ~r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) | ~v1_relat_1(sK3) | spl5_2),
% 0.12/0.44    inference(resolution,[],[f181,f72])).
% 0.12/0.44  fof(f72,plain,(
% 0.12/0.44    ~v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) | spl5_2),
% 0.12/0.44    inference(avatar_component_clause,[],[f70])).
% 0.12/0.44  fof(f181,plain,(
% 0.12/0.44    ( ! [X2,X0,X1] : (v1_funct_2(X0,X1,X2) | sP0(X1,X2) | k1_relat_1(X0) != X1 | ~r1_tarski(k2_relat_1(X0),X2) | ~r1_tarski(k1_relat_1(X0),X1) | ~v1_relat_1(X0)) )),
% 0.12/0.44    inference(resolution,[],[f173,f49])).
% 0.12/0.44  fof(f49,plain,(
% 0.12/0.44    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 0.12/0.44    inference(cnf_transformation,[],[f15])).
% 0.12/0.44  fof(f15,plain,(
% 0.12/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.12/0.44    inference(flattening,[],[f14])).
% 0.12/0.44  fof(f14,plain,(
% 0.12/0.44    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.12/0.44    inference(ennf_transformation,[],[f6])).
% 0.12/0.44  fof(f6,axiom,(
% 0.12/0.44    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.12/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 0.12/0.44  fof(f173,plain,(
% 0.12/0.44    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | v1_funct_2(X5,X3,X4) | sP0(X3,X4) | k1_relat_1(X5) != X3) )),
% 0.12/0.44    inference(subsumption_resolution,[],[f171,f57])).
% 0.12/0.44  fof(f57,plain,(
% 0.12/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP1(X0,X2,X1)) )),
% 0.12/0.44    inference(cnf_transformation,[],[f22])).
% 0.12/0.44  fof(f22,plain,(
% 0.12/0.44    ! [X0,X1,X2] : ((sP2(X2,X1,X0) & sP1(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.12/0.44    inference(definition_folding,[],[f18,f21,f20,f19])).
% 0.12/0.44  fof(f20,plain,(
% 0.12/0.44    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 0.12/0.44    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.12/0.44  fof(f21,plain,(
% 0.12/0.44    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP2(X2,X1,X0))),
% 0.12/0.44    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.12/0.44  fof(f18,plain,(
% 0.12/0.44    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.12/0.44    inference(flattening,[],[f17])).
% 0.12/0.44  fof(f17,plain,(
% 0.12/0.44    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.12/0.44    inference(ennf_transformation,[],[f7])).
% 0.12/0.44  fof(f7,axiom,(
% 0.12/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.12/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.12/0.44  fof(f171,plain,(
% 0.12/0.44    ( ! [X4,X5,X3] : (k1_relat_1(X5) != X3 | v1_funct_2(X5,X3,X4) | sP0(X3,X4) | ~sP1(X3,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.12/0.44    inference(superposition,[],[f54,f50])).
% 0.12/0.44  fof(f50,plain,(
% 0.12/0.44    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.12/0.44    inference(cnf_transformation,[],[f16])).
% 0.12/0.44  fof(f16,plain,(
% 0.12/0.44    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.12/0.44    inference(ennf_transformation,[],[f5])).
% 0.12/0.44  fof(f5,axiom,(
% 0.12/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.12/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.12/0.44  fof(f54,plain,(
% 0.12/0.44    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) != X0 | v1_funct_2(X1,X0,X2) | sP0(X0,X2) | ~sP1(X0,X1,X2)) )),
% 0.12/0.44    inference(cnf_transformation,[],[f35])).
% 0.12/0.44  fof(f35,plain,(
% 0.12/0.44    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP0(X0,X2) | ~sP1(X0,X1,X2))),
% 0.12/0.44    inference(rectify,[],[f34])).
% 0.12/0.44  % (31573)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.12/0.44  fof(f34,plain,(
% 0.12/0.44    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 0.12/0.44    inference(nnf_transformation,[],[f20])).
% 0.12/0.44  fof(f267,plain,(
% 0.12/0.44    ~spl5_13 | ~spl5_4 | spl5_5),
% 0.12/0.44    inference(avatar_split_clause,[],[f262,f90,f86,f264])).
% 0.12/0.44  fof(f86,plain,(
% 0.12/0.44    spl5_4 <=> k1_xboole_0 = k1_relat_1(sK3)),
% 0.12/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.12/0.44  % (31579)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.12/0.44  fof(f90,plain,(
% 0.12/0.44    spl5_5 <=> v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)),
% 0.12/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.12/0.44  % (31576)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.12/0.44  fof(f262,plain,(
% 0.12/0.44    k1_xboole_0 != k1_relat_1(sK3) | ~r1_tarski(k2_relat_1(sK3),k1_xboole_0) | spl5_5),
% 0.12/0.44    inference(subsumption_resolution,[],[f261,f40])).
% 0.12/0.44  fof(f261,plain,(
% 0.12/0.44    k1_xboole_0 != k1_relat_1(sK3) | ~r1_tarski(k2_relat_1(sK3),k1_xboole_0) | ~r1_tarski(k1_xboole_0,k1_xboole_0) | spl5_5),
% 0.12/0.44    inference(inner_rewriting,[],[f260])).
% 0.12/0.44  fof(f260,plain,(
% 0.12/0.44    k1_xboole_0 != k1_relat_1(sK3) | ~r1_tarski(k2_relat_1(sK3),k1_xboole_0) | ~r1_tarski(k1_relat_1(sK3),k1_xboole_0) | spl5_5),
% 0.12/0.44    inference(subsumption_resolution,[],[f259,f37])).
% 0.12/0.44  fof(f259,plain,(
% 0.12/0.44    k1_xboole_0 != k1_relat_1(sK3) | ~r1_tarski(k2_relat_1(sK3),k1_xboole_0) | ~r1_tarski(k1_relat_1(sK3),k1_xboole_0) | ~v1_relat_1(sK3) | spl5_5),
% 0.12/0.44    inference(subsumption_resolution,[],[f231,f64])).
% 0.12/0.44  fof(f64,plain,(
% 0.12/0.44    ( ! [X1] : (~sP0(k1_xboole_0,X1)) )),
% 0.12/0.44    inference(equality_resolution,[],[f56])).
% 0.12/0.44  fof(f56,plain,(
% 0.12/0.44    ( ! [X0,X1] : (k1_xboole_0 != X0 | ~sP0(X0,X1)) )),
% 0.12/0.44    inference(cnf_transformation,[],[f36])).
% 0.12/0.44  fof(f231,plain,(
% 0.12/0.44    sP0(k1_xboole_0,k1_xboole_0) | k1_xboole_0 != k1_relat_1(sK3) | ~r1_tarski(k2_relat_1(sK3),k1_xboole_0) | ~r1_tarski(k1_relat_1(sK3),k1_xboole_0) | ~v1_relat_1(sK3) | spl5_5),
% 0.12/0.44    inference(resolution,[],[f181,f92])).
% 0.12/0.44  fof(f92,plain,(
% 0.12/0.44    ~v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | spl5_5),
% 0.12/0.44    inference(avatar_component_clause,[],[f90])).
% 0.12/0.44  fof(f258,plain,(
% 0.12/0.44    spl5_3),
% 0.12/0.44    inference(avatar_contradiction_clause,[],[f257])).
% 0.12/0.44  fof(f257,plain,(
% 0.12/0.44    $false | spl5_3),
% 0.12/0.44    inference(subsumption_resolution,[],[f256,f37])).
% 0.12/0.44  fof(f256,plain,(
% 0.12/0.44    ~v1_relat_1(sK3) | spl5_3),
% 0.12/0.44    inference(subsumption_resolution,[],[f255,f80])).
% 0.12/0.44  fof(f255,plain,(
% 0.12/0.44    ~r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) | ~v1_relat_1(sK3) | spl5_3),
% 0.12/0.44    inference(subsumption_resolution,[],[f252,f80])).
% 0.12/0.44  fof(f252,plain,(
% 0.12/0.44    ~r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3)) | ~r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) | ~v1_relat_1(sK3) | spl5_3),
% 0.12/0.44    inference(resolution,[],[f76,f49])).
% 0.12/0.44  fof(f76,plain,(
% 0.12/0.44    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | spl5_3),
% 0.12/0.44    inference(avatar_component_clause,[],[f74])).
% 0.12/0.44  fof(f74,plain,(
% 0.12/0.44    spl5_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))),
% 0.12/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.12/0.44  fof(f107,plain,(
% 0.12/0.44    ~spl5_6 | spl5_4),
% 0.12/0.44    inference(avatar_split_clause,[],[f97,f86,f101])).
% 0.12/0.44  fof(f97,plain,(
% 0.12/0.44    k1_xboole_0 != k2_relat_1(sK3) | spl5_4),
% 0.12/0.44    inference(subsumption_resolution,[],[f96,f37])).
% 0.12/0.44  fof(f96,plain,(
% 0.12/0.44    k1_xboole_0 != k2_relat_1(sK3) | ~v1_relat_1(sK3) | spl5_4),
% 0.12/0.44    inference(trivial_inequality_removal,[],[f94])).
% 0.12/0.44  fof(f94,plain,(
% 0.12/0.44    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k2_relat_1(sK3) | ~v1_relat_1(sK3) | spl5_4),
% 0.12/0.44    inference(superposition,[],[f88,f42])).
% 0.12/0.44  fof(f42,plain,(
% 0.12/0.44    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.12/0.44    inference(cnf_transformation,[],[f25])).
% 0.12/0.44  fof(f25,plain,(
% 0.12/0.44    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.12/0.44    inference(nnf_transformation,[],[f12])).
% 0.12/0.44  fof(f12,plain,(
% 0.12/0.44    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.12/0.44    inference(ennf_transformation,[],[f4])).
% 0.12/0.44  fof(f4,axiom,(
% 0.12/0.44    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.12/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).
% 0.12/0.44  fof(f88,plain,(
% 0.12/0.44    k1_xboole_0 != k1_relat_1(sK3) | spl5_4),
% 0.12/0.44    inference(avatar_component_clause,[],[f86])).
% 0.12/0.44  fof(f104,plain,(
% 0.12/0.44    ~spl5_6 | ~spl5_5 | spl5_2),
% 0.12/0.44    inference(avatar_split_clause,[],[f99,f70,f90,f101])).
% 0.12/0.44  fof(f99,plain,(
% 0.12/0.44    ~v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | k1_xboole_0 != k2_relat_1(sK3) | spl5_2),
% 0.12/0.44    inference(inner_rewriting,[],[f98])).
% 0.12/0.44  fof(f98,plain,(
% 0.12/0.44    ~v1_funct_2(sK3,k1_xboole_0,k2_relat_1(sK3)) | k1_xboole_0 != k2_relat_1(sK3) | spl5_2),
% 0.12/0.44    inference(subsumption_resolution,[],[f95,f37])).
% 0.12/0.44  fof(f95,plain,(
% 0.12/0.44    ~v1_funct_2(sK3,k1_xboole_0,k2_relat_1(sK3)) | k1_xboole_0 != k2_relat_1(sK3) | ~v1_relat_1(sK3) | spl5_2),
% 0.12/0.44    inference(superposition,[],[f72,f42])).
% 0.12/0.44  fof(f78,plain,(
% 0.12/0.44    spl5_1),
% 0.12/0.44    inference(avatar_split_clause,[],[f38,f66])).
% 0.12/0.44  fof(f66,plain,(
% 0.12/0.44    spl5_1 <=> v1_funct_1(sK3)),
% 0.12/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.12/0.44  fof(f38,plain,(
% 0.12/0.44    v1_funct_1(sK3)),
% 0.12/0.44    inference(cnf_transformation,[],[f24])).
% 0.12/0.44  fof(f77,plain,(
% 0.12/0.44    ~spl5_1 | ~spl5_2 | ~spl5_3),
% 0.12/0.44    inference(avatar_split_clause,[],[f39,f74,f70,f66])).
% 0.12/0.44  fof(f39,plain,(
% 0.12/0.44    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | ~v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) | ~v1_funct_1(sK3)),
% 0.12/0.44    inference(cnf_transformation,[],[f24])).
% 0.12/0.44  % SZS output end Proof for theBenchmark
% 0.12/0.44  % (31594)------------------------------
% 0.12/0.44  % (31594)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.44  % (31594)Termination reason: Refutation
% 0.12/0.44  
% 0.12/0.44  % (31594)Memory used [KB]: 6268
% 0.12/0.44  % (31594)Time elapsed: 0.117 s
% 0.12/0.44  % (31594)------------------------------
% 0.12/0.44  % (31594)------------------------------
% 0.12/0.44  % (31566)Success in time 0.158 s
%------------------------------------------------------------------------------
