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
% DateTime   : Thu Dec  3 13:00:25 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 362 expanded)
%              Number of leaves         :   14 (  95 expanded)
%              Depth                    :   18
%              Number of atoms          :  316 (1581 expanded)
%              Number of equality atoms :   75 ( 412 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (13432)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f233,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f85,f107,f144,f155,f156,f230])).

fof(f230,plain,
    ( spl4_2
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f229])).

fof(f229,plain,
    ( $false
    | spl4_2
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f184,f228])).

fof(f228,plain,
    ( v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | spl4_2
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f221,f198])).

fof(f198,plain,
    ( ! [X2] : k1_xboole_0 = k1_relset_1(X2,k1_xboole_0,sK1)
    | spl4_2
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f197,f182])).

fof(f182,plain,
    ( k1_xboole_0 = k1_relat_1(sK1)
    | spl4_2
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f179,f37])).

fof(f37,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
      | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
      | ~ v1_funct_1(sK1) )
    & r1_tarski(k2_relat_1(sK1),sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f24])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
          | ~ v1_funct_1(X1) )
        & r1_tarski(k2_relat_1(X1),X0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
        | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
        | ~ v1_funct_1(sK1) )
      & r1_tarski(k2_relat_1(sK1),sK0)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(k2_relat_1(X1),X0)
         => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
            & v1_funct_2(X1,k1_relat_1(X1),X0)
            & v1_funct_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f179,plain,
    ( k1_xboole_0 = k1_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_2
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(trivial_inequality_removal,[],[f178])).

fof(f178,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_2
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(superposition,[],[f43,f173])).

% (13434)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f173,plain,
    ( k1_xboole_0 = k2_relat_1(sK1)
    | spl4_2
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f96,f158])).

fof(f158,plain,
    ( k1_xboole_0 = sK0
    | spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f157,f78])).

fof(f78,plain,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl4_2
  <=> v1_funct_2(sK1,k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f157,plain,
    ( k1_xboole_0 = sK0
    | v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f149,f150])).

fof(f150,plain,
    ( k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1)
    | ~ spl4_3 ),
    inference(resolution,[],[f81,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f81,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl4_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f149,plain,
    ( k1_relat_1(sK1) != k1_relset_1(k1_relat_1(sK1),sK0,sK1)
    | k1_xboole_0 = sK0
    | v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f81,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f96,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl4_5
  <=> sK0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f43,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f197,plain,
    ( ! [X2] : k1_relat_1(sK1) = k1_relset_1(X2,k1_xboole_0,sK1)
    | spl4_2
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f187,f41])).

fof(f41,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f187,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k1_xboole_0,X2)
        | k1_relat_1(sK1) = k1_relset_1(X2,k1_xboole_0,sK1) )
    | spl4_2
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f163,f182])).

fof(f163,plain,
    ( ! [X2] :
        ( k1_relat_1(sK1) = k1_relset_1(X2,k1_xboole_0,sK1)
        | ~ r1_tarski(k1_relat_1(sK1),X2) )
    | spl4_2
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f102,f158])).

fof(f102,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_relat_1(sK1),X2)
      | k1_relat_1(sK1) = k1_relset_1(X2,sK0,sK1) ) ),
    inference(resolution,[],[f88,f57])).

fof(f88,plain,(
    ! [X0] :
      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
      | ~ r1_tarski(k1_relat_1(sK1),X0) ) ),
    inference(subsumption_resolution,[],[f86,f37])).

fof(f86,plain,(
    ! [X0] :
      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
      | ~ r1_tarski(k1_relat_1(sK1),X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f39,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f39,plain,(
    r1_tarski(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f221,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)
    | v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | spl4_2
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(resolution,[],[f196,f69])).

fof(f69,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f196,plain,
    ( ! [X0] : m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | spl4_2
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f186,f41])).

fof(f186,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) )
    | spl4_2
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f162,f182])).

fof(f162,plain,
    ( ! [X0] :
        ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
        | ~ r1_tarski(k1_relat_1(sK1),X0) )
    | spl4_2
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f88,f158])).

fof(f184,plain,
    ( ~ v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | spl4_2
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f160,f182])).

fof(f160,plain,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0)
    | spl4_2
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f78,f158])).

fof(f156,plain,
    ( ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f147,f94,f90])).

fof(f90,plain,
    ( spl4_4
  <=> r1_tarski(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f147,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(resolution,[],[f39,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f155,plain,
    ( spl4_2
    | ~ spl4_3
    | spl4_6 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | spl4_2
    | ~ spl4_3
    | spl4_6 ),
    inference(subsumption_resolution,[],[f150,f153])).

fof(f153,plain,
    ( k1_relat_1(sK1) != k1_relset_1(k1_relat_1(sK1),sK0,sK1)
    | spl4_2
    | ~ spl4_3
    | spl4_6 ),
    inference(subsumption_resolution,[],[f152,f78])).

fof(f152,plain,
    ( k1_relat_1(sK1) != k1_relset_1(k1_relat_1(sK1),sK0,sK1)
    | v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ spl4_3
    | spl4_6 ),
    inference(subsumption_resolution,[],[f149,f110])).

fof(f110,plain,
    ( k1_xboole_0 != sK0
    | spl4_6 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl4_6
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

% (13445)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f144,plain,
    ( spl4_4
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f143])).

fof(f143,plain,
    ( $false
    | spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f137,f41])).

fof(f137,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK1))
    | spl4_4
    | ~ spl4_6 ),
    inference(backward_demodulation,[],[f92,f111])).

fof(f111,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f109])).

fof(f92,plain,
    ( ~ r1_tarski(sK0,k2_relat_1(sK1))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f107,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f106])).

fof(f106,plain,
    ( $false
    | spl4_3 ),
    inference(subsumption_resolution,[],[f99,f65])).

fof(f65,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f99,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))
    | spl4_3 ),
    inference(resolution,[],[f88,f82])).

fof(f82,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f85,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f84])).

fof(f84,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f74,f38])).

fof(f38,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f74,plain,
    ( ~ v1_funct_1(sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl4_1
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f83,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f40,f80,f76,f72])).

fof(f40,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:29:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.53  % (13424)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (13431)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (13425)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (13428)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (13447)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (13426)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (13431)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % (13427)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  % (13432)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  fof(f233,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f83,f85,f107,f144,f155,f156,f230])).
% 0.22/0.54  fof(f230,plain,(
% 0.22/0.54    spl4_2 | ~spl4_3 | ~spl4_5),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f229])).
% 0.22/0.54  fof(f229,plain,(
% 0.22/0.54    $false | (spl4_2 | ~spl4_3 | ~spl4_5)),
% 0.22/0.54    inference(subsumption_resolution,[],[f184,f228])).
% 0.22/0.54  fof(f228,plain,(
% 0.22/0.54    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | (spl4_2 | ~spl4_3 | ~spl4_5)),
% 0.22/0.54    inference(subsumption_resolution,[],[f221,f198])).
% 0.22/0.54  fof(f198,plain,(
% 0.22/0.54    ( ! [X2] : (k1_xboole_0 = k1_relset_1(X2,k1_xboole_0,sK1)) ) | (spl4_2 | ~spl4_3 | ~spl4_5)),
% 0.22/0.54    inference(forward_demodulation,[],[f197,f182])).
% 0.22/0.54  fof(f182,plain,(
% 0.22/0.54    k1_xboole_0 = k1_relat_1(sK1) | (spl4_2 | ~spl4_3 | ~spl4_5)),
% 0.22/0.54    inference(subsumption_resolution,[],[f179,f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    v1_relat_1(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)) & r1_tarski(k2_relat_1(sK1),sK0) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1)) => ((~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)) & r1_tarski(k2_relat_1(sK1),sK0) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.54    inference(flattening,[],[f13])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ? [X0,X1] : (((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.22/0.54    inference(negated_conjecture,[],[f11])).
% 0.22/0.54  fof(f11,conjecture,(
% 0.22/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 0.22/0.54  fof(f179,plain,(
% 0.22/0.54    k1_xboole_0 = k1_relat_1(sK1) | ~v1_relat_1(sK1) | (spl4_2 | ~spl4_3 | ~spl4_5)),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f178])).
% 0.22/0.54  fof(f178,plain,(
% 0.22/0.54    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k1_relat_1(sK1) | ~v1_relat_1(sK1) | (spl4_2 | ~spl4_3 | ~spl4_5)),
% 0.22/0.54    inference(superposition,[],[f43,f173])).
% 0.22/0.54  % (13434)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  fof(f173,plain,(
% 0.22/0.54    k1_xboole_0 = k2_relat_1(sK1) | (spl4_2 | ~spl4_3 | ~spl4_5)),
% 0.22/0.54    inference(forward_demodulation,[],[f96,f158])).
% 0.22/0.54  fof(f158,plain,(
% 0.22/0.54    k1_xboole_0 = sK0 | (spl4_2 | ~spl4_3)),
% 0.22/0.54    inference(subsumption_resolution,[],[f157,f78])).
% 0.22/0.54  fof(f78,plain,(
% 0.22/0.54    ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | spl4_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f76])).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    spl4_2 <=> v1_funct_2(sK1,k1_relat_1(sK1),sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.54  fof(f157,plain,(
% 0.22/0.54    k1_xboole_0 = sK0 | v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~spl4_3),
% 0.22/0.54    inference(subsumption_resolution,[],[f149,f150])).
% 0.22/0.54  fof(f150,plain,(
% 0.22/0.54    k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1) | ~spl4_3),
% 0.22/0.54    inference(resolution,[],[f81,f57])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.54  fof(f81,plain,(
% 0.22/0.54    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~spl4_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f80])).
% 0.22/0.54  fof(f80,plain,(
% 0.22/0.54    spl4_3 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.54  fof(f149,plain,(
% 0.22/0.54    k1_relat_1(sK1) != k1_relset_1(k1_relat_1(sK1),sK0,sK1) | k1_xboole_0 = sK0 | v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~spl4_3),
% 0.22/0.54    inference(resolution,[],[f81,f60])).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | v1_funct_2(X2,X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(nnf_transformation,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(flattening,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.54  fof(f96,plain,(
% 0.22/0.54    sK0 = k2_relat_1(sK1) | ~spl4_5),
% 0.22/0.54    inference(avatar_component_clause,[],[f94])).
% 0.22/0.54  fof(f94,plain,(
% 0.22/0.54    spl4_5 <=> sK0 = k2_relat_1(sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(nnf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 0.22/0.54  fof(f197,plain,(
% 0.22/0.54    ( ! [X2] : (k1_relat_1(sK1) = k1_relset_1(X2,k1_xboole_0,sK1)) ) | (spl4_2 | ~spl4_3 | ~spl4_5)),
% 0.22/0.54    inference(subsumption_resolution,[],[f187,f41])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.54  fof(f187,plain,(
% 0.22/0.54    ( ! [X2] : (~r1_tarski(k1_xboole_0,X2) | k1_relat_1(sK1) = k1_relset_1(X2,k1_xboole_0,sK1)) ) | (spl4_2 | ~spl4_3 | ~spl4_5)),
% 0.22/0.54    inference(backward_demodulation,[],[f163,f182])).
% 0.22/0.54  fof(f163,plain,(
% 0.22/0.54    ( ! [X2] : (k1_relat_1(sK1) = k1_relset_1(X2,k1_xboole_0,sK1) | ~r1_tarski(k1_relat_1(sK1),X2)) ) | (spl4_2 | ~spl4_3)),
% 0.22/0.54    inference(backward_demodulation,[],[f102,f158])).
% 0.22/0.54  fof(f102,plain,(
% 0.22/0.54    ( ! [X2] : (~r1_tarski(k1_relat_1(sK1),X2) | k1_relat_1(sK1) = k1_relset_1(X2,sK0,sK1)) )),
% 0.22/0.54    inference(resolution,[],[f88,f57])).
% 0.22/0.54  fof(f88,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | ~r1_tarski(k1_relat_1(sK1),X0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f86,f37])).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | ~r1_tarski(k1_relat_1(sK1),X0) | ~v1_relat_1(sK1)) )),
% 0.22/0.54    inference(resolution,[],[f39,f56])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.22/0.54    inference(flattening,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    r1_tarski(k2_relat_1(sK1),sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  fof(f221,plain,(
% 0.22/0.54    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) | v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | (spl4_2 | ~spl4_3 | ~spl4_5)),
% 0.22/0.54    inference(resolution,[],[f196,f69])).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.22/0.54    inference(equality_resolution,[],[f61])).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f36])).
% 0.22/0.54  fof(f196,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) ) | (spl4_2 | ~spl4_3 | ~spl4_5)),
% 0.22/0.54    inference(subsumption_resolution,[],[f186,f41])).
% 0.22/0.54  fof(f186,plain,(
% 0.22/0.54    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) ) | (spl4_2 | ~spl4_3 | ~spl4_5)),
% 0.22/0.54    inference(backward_demodulation,[],[f162,f182])).
% 0.22/0.54  fof(f162,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | ~r1_tarski(k1_relat_1(sK1),X0)) ) | (spl4_2 | ~spl4_3)),
% 0.22/0.54    inference(backward_demodulation,[],[f88,f158])).
% 0.22/0.54  fof(f184,plain,(
% 0.22/0.54    ~v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | (spl4_2 | ~spl4_3 | ~spl4_5)),
% 0.22/0.54    inference(backward_demodulation,[],[f160,f182])).
% 0.22/0.54  fof(f160,plain,(
% 0.22/0.54    ~v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0) | (spl4_2 | ~spl4_3)),
% 0.22/0.54    inference(backward_demodulation,[],[f78,f158])).
% 0.22/0.54  fof(f156,plain,(
% 0.22/0.54    ~spl4_4 | spl4_5),
% 0.22/0.54    inference(avatar_split_clause,[],[f147,f94,f90])).
% 0.22/0.54  fof(f90,plain,(
% 0.22/0.54    spl4_4 <=> r1_tarski(sK0,k2_relat_1(sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.54  fof(f147,plain,(
% 0.22/0.54    sK0 = k2_relat_1(sK1) | ~r1_tarski(sK0,k2_relat_1(sK1))),
% 0.22/0.54    inference(resolution,[],[f39,f49])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(flattening,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.54  fof(f155,plain,(
% 0.22/0.54    spl4_2 | ~spl4_3 | spl4_6),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f154])).
% 0.22/0.54  fof(f154,plain,(
% 0.22/0.54    $false | (spl4_2 | ~spl4_3 | spl4_6)),
% 0.22/0.54    inference(subsumption_resolution,[],[f150,f153])).
% 0.22/0.54  fof(f153,plain,(
% 0.22/0.54    k1_relat_1(sK1) != k1_relset_1(k1_relat_1(sK1),sK0,sK1) | (spl4_2 | ~spl4_3 | spl4_6)),
% 0.22/0.54    inference(subsumption_resolution,[],[f152,f78])).
% 0.22/0.54  fof(f152,plain,(
% 0.22/0.54    k1_relat_1(sK1) != k1_relset_1(k1_relat_1(sK1),sK0,sK1) | v1_funct_2(sK1,k1_relat_1(sK1),sK0) | (~spl4_3 | spl4_6)),
% 0.22/0.54    inference(subsumption_resolution,[],[f149,f110])).
% 0.22/0.54  fof(f110,plain,(
% 0.22/0.54    k1_xboole_0 != sK0 | spl4_6),
% 0.22/0.54    inference(avatar_component_clause,[],[f109])).
% 0.22/0.54  fof(f109,plain,(
% 0.22/0.54    spl4_6 <=> k1_xboole_0 = sK0),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.54  % (13445)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  fof(f144,plain,(
% 0.22/0.54    spl4_4 | ~spl4_6),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f143])).
% 0.22/0.54  fof(f143,plain,(
% 0.22/0.54    $false | (spl4_4 | ~spl4_6)),
% 0.22/0.54    inference(subsumption_resolution,[],[f137,f41])).
% 0.22/0.54  fof(f137,plain,(
% 0.22/0.54    ~r1_tarski(k1_xboole_0,k2_relat_1(sK1)) | (spl4_4 | ~spl4_6)),
% 0.22/0.54    inference(backward_demodulation,[],[f92,f111])).
% 0.22/0.54  fof(f111,plain,(
% 0.22/0.54    k1_xboole_0 = sK0 | ~spl4_6),
% 0.22/0.54    inference(avatar_component_clause,[],[f109])).
% 0.22/0.54  fof(f92,plain,(
% 0.22/0.54    ~r1_tarski(sK0,k2_relat_1(sK1)) | spl4_4),
% 0.22/0.54    inference(avatar_component_clause,[],[f90])).
% 0.22/0.54  fof(f107,plain,(
% 0.22/0.54    spl4_3),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f106])).
% 0.22/0.54  fof(f106,plain,(
% 0.22/0.54    $false | spl4_3),
% 0.22/0.54    inference(subsumption_resolution,[],[f99,f65])).
% 0.22/0.54  fof(f65,plain,(
% 0.22/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.54    inference(equality_resolution,[],[f47])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f30])).
% 0.22/0.54  fof(f99,plain,(
% 0.22/0.54    ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) | spl4_3),
% 0.22/0.54    inference(resolution,[],[f88,f82])).
% 0.22/0.54  fof(f82,plain,(
% 0.22/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | spl4_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f80])).
% 0.22/0.54  fof(f85,plain,(
% 0.22/0.54    spl4_1),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f84])).
% 0.22/0.54  fof(f84,plain,(
% 0.22/0.54    $false | spl4_1),
% 0.22/0.54    inference(subsumption_resolution,[],[f74,f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    v1_funct_1(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  fof(f74,plain,(
% 0.22/0.54    ~v1_funct_1(sK1) | spl4_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f72])).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    spl4_1 <=> v1_funct_1(sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.54  fof(f83,plain,(
% 0.22/0.54    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f40,f80,f76,f72])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (13431)------------------------------
% 0.22/0.54  % (13431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (13431)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (13431)Memory used [KB]: 10746
% 0.22/0.54  % (13452)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (13431)Time elapsed: 0.083 s
% 0.22/0.54  % (13431)------------------------------
% 0.22/0.54  % (13431)------------------------------
% 0.22/0.54  % (13435)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (13439)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.54  % (13434)Refutation not found, incomplete strategy% (13434)------------------------------
% 0.22/0.54  % (13434)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (13434)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (13434)Memory used [KB]: 10746
% 0.22/0.54  % (13434)Time elapsed: 0.124 s
% 0.22/0.54  % (13434)------------------------------
% 0.22/0.54  % (13434)------------------------------
% 0.22/0.54  % (13437)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (13422)Success in time 0.184 s
%------------------------------------------------------------------------------
