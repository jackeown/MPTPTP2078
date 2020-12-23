%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:26 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 268 expanded)
%              Number of leaves         :   20 (  73 expanded)
%              Depth                    :   18
%              Number of atoms          :  314 (1172 expanded)
%              Number of equality atoms :   73 ( 184 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f385,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f84,f277,f308,f315,f384])).

fof(f384,plain,
    ( spl6_2
    | ~ spl6_10 ),
    inference(avatar_contradiction_clause,[],[f383])).

fof(f383,plain,
    ( $false
    | spl6_2
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f382,f70])).

fof(f70,plain,(
    ! [X1] : ~ sP0(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f382,plain,
    ( sP0(k1_xboole_0,k1_xboole_0)
    | spl6_2
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f381,f43])).

fof(f43,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f381,plain,
    ( sP0(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | spl6_2
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f269,f168])).

fof(f168,plain,
    ( k1_xboole_0 = sK4
    | ~ spl6_10 ),
    inference(resolution,[],[f149,f45])).

fof(f45,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f14,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f149,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK4)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl6_10
  <=> ! [X0] : ~ r2_hidden(X0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f269,plain,
    ( sP0(k1_relat_1(sK4),k1_xboole_0)
    | spl6_2 ),
    inference(backward_demodulation,[],[f267,f268])).

fof(f268,plain,
    ( k1_xboole_0 = sK3
    | spl6_2 ),
    inference(resolution,[],[f267,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f267,plain,
    ( sP0(k1_relat_1(sK4),sK3)
    | spl6_2 ),
    inference(subsumption_resolution,[],[f266,f38])).

fof(f38,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3)))
      | ~ v1_funct_2(sK4,k1_relat_1(sK4),sK3)
      | ~ v1_funct_1(sK4) )
    & r1_tarski(k2_relat_1(sK4),sK3)
    & v1_funct_1(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f13,f25])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
          | ~ v1_funct_1(X1) )
        & r1_tarski(k2_relat_1(X1),X0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3)))
        | ~ v1_funct_2(sK4,k1_relat_1(sK4),sK3)
        | ~ v1_funct_1(sK4) )
      & r1_tarski(k2_relat_1(sK4),sK3)
      & v1_funct_1(sK4)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(k2_relat_1(X1),X0)
         => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
            & v1_funct_2(X1,k1_relat_1(X1),X0)
            & v1_funct_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f266,plain,
    ( sP0(k1_relat_1(sK4),sK3)
    | ~ v1_relat_1(sK4)
    | spl6_2 ),
    inference(subsumption_resolution,[],[f265,f63])).

fof(f63,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f265,plain,
    ( sP0(k1_relat_1(sK4),sK3)
    | ~ r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | spl6_2 ),
    inference(subsumption_resolution,[],[f261,f40])).

fof(f40,plain,(
    r1_tarski(k2_relat_1(sK4),sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f261,plain,
    ( sP0(k1_relat_1(sK4),sK3)
    | ~ r1_tarski(k2_relat_1(sK4),sK3)
    | ~ r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | spl6_2 ),
    inference(trivial_inequality_removal,[],[f260])).

fof(f260,plain,
    ( sP0(k1_relat_1(sK4),sK3)
    | k1_relat_1(sK4) != k1_relat_1(sK4)
    | ~ r1_tarski(k2_relat_1(sK4),sK3)
    | ~ r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | spl6_2 ),
    inference(resolution,[],[f229,f78])).

fof(f78,plain,
    ( ~ v1_funct_2(sK4,k1_relat_1(sK4),sK3)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl6_2
  <=> v1_funct_2(sK4,k1_relat_1(sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f229,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X0,X1,X2)
      | sP0(X1,X2)
      | k1_relat_1(X0) != X1
      | ~ r1_tarski(k2_relat_1(X0),X2)
      | ~ r1_tarski(k1_relat_1(X0),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f159,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
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

fof(f159,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | v1_funct_2(X5,X3,X4)
      | sP0(X3,X4)
      | k1_relat_1(X5) != X3 ) ),
    inference(subsumption_resolution,[],[f157,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X2,X1,X0)
        & sP1(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f19,f23,f22,f21])).

fof(f22,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP2(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

% (12259)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% (12238)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% (12250)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f157,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) != X3
      | v1_funct_2(X5,X3,X4)
      | sP0(X3,X4)
      | ~ sP1(X3,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f57,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) != X0
      | v1_funct_2(X1,X0,X2)
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f315,plain,(
    spl6_3 ),
    inference(avatar_contradiction_clause,[],[f314])).

fof(f314,plain,
    ( $false
    | spl6_3 ),
    inference(subsumption_resolution,[],[f313,f38])).

fof(f313,plain,
    ( ~ v1_relat_1(sK4)
    | spl6_3 ),
    inference(subsumption_resolution,[],[f312,f63])).

% (12244)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
fof(f312,plain,
    ( ~ r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | spl6_3 ),
    inference(subsumption_resolution,[],[f311,f40])).

fof(f311,plain,
    ( ~ r1_tarski(k2_relat_1(sK4),sK3)
    | ~ r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | spl6_3 ),
    inference(resolution,[],[f82,f52])).

fof(f82,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3)))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl6_3
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f308,plain,
    ( spl6_10
    | spl6_12 ),
    inference(avatar_split_clause,[],[f307,f165,f148])).

fof(f165,plain,
    ( spl6_12
  <=> ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK4),X0)
        | ~ v1_xboole_0(k2_zfmisc_1(X0,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f307,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(sK4),X0)
      | ~ v1_xboole_0(k2_zfmisc_1(X0,sK3))
      | ~ r2_hidden(X1,sK4) ) ),
    inference(subsumption_resolution,[],[f304,f38])).

fof(f304,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(sK4),X0)
      | ~ v1_relat_1(sK4)
      | ~ v1_xboole_0(k2_zfmisc_1(X0,sK3))
      | ~ r2_hidden(X1,sK4) ) ),
    inference(resolution,[],[f40,f116])).

fof(f116,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ r1_tarski(k2_relat_1(X6),X7)
      | ~ r1_tarski(k1_relat_1(X6),X8)
      | ~ v1_relat_1(X6)
      | ~ v1_xboole_0(k2_zfmisc_1(X8,X7))
      | ~ r2_hidden(X9,X6) ) ),
    inference(resolution,[],[f52,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f277,plain,
    ( spl6_2
    | ~ spl6_12 ),
    inference(avatar_contradiction_clause,[],[f276])).

fof(f276,plain,
    ( $false
    | spl6_2
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f275,f42])).

fof(f42,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f275,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl6_2
    | ~ spl6_12 ),
    inference(forward_demodulation,[],[f270,f65])).

fof(f65,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f270,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1(sK4),k1_xboole_0))
    | spl6_2
    | ~ spl6_12 ),
    inference(backward_demodulation,[],[f222,f268])).

fof(f222,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1(sK4),sK3))
    | ~ spl6_12 ),
    inference(resolution,[],[f166,f63])).

fof(f166,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK4),X0)
        | ~ v1_xboole_0(k2_zfmisc_1(X0,sK3)) )
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f165])).

fof(f84,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f39,f72])).

fof(f72,plain,
    ( spl6_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f39,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f83,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f41,f80,f76,f72])).

fof(f41,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3)))
    | ~ v1_funct_2(sK4,k1_relat_1(sK4),sK3)
    | ~ v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:44:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.49  % (12241)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.50  % (12241)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % (12258)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f385,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f83,f84,f277,f308,f315,f384])).
% 0.20/0.50  fof(f384,plain,(
% 0.20/0.50    spl6_2 | ~spl6_10),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f383])).
% 0.20/0.50  fof(f383,plain,(
% 0.20/0.50    $false | (spl6_2 | ~spl6_10)),
% 0.20/0.50    inference(subsumption_resolution,[],[f382,f70])).
% 0.20/0.50  fof(f70,plain,(
% 0.20/0.50    ( ! [X1] : (~sP0(k1_xboole_0,X1)) )),
% 0.20/0.50    inference(equality_resolution,[],[f59])).
% 0.20/0.50  fof(f59,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_xboole_0 != X0 | ~sP0(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 0.20/0.50    inference(nnf_transformation,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 0.20/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.50  fof(f382,plain,(
% 0.20/0.50    sP0(k1_xboole_0,k1_xboole_0) | (spl6_2 | ~spl6_10)),
% 0.20/0.50    inference(forward_demodulation,[],[f381,f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.50    inference(cnf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.50  fof(f381,plain,(
% 0.20/0.50    sP0(k1_relat_1(k1_xboole_0),k1_xboole_0) | (spl6_2 | ~spl6_10)),
% 0.20/0.50    inference(forward_demodulation,[],[f269,f168])).
% 0.20/0.50  fof(f168,plain,(
% 0.20/0.50    k1_xboole_0 = sK4 | ~spl6_10),
% 0.20/0.50    inference(resolution,[],[f149,f45])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ( ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f14,f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK5(X0),X0))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.50  fof(f149,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(X0,sK4)) ) | ~spl6_10),
% 0.20/0.50    inference(avatar_component_clause,[],[f148])).
% 0.20/0.50  fof(f148,plain,(
% 0.20/0.50    spl6_10 <=> ! [X0] : ~r2_hidden(X0,sK4)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.20/0.50  fof(f269,plain,(
% 0.20/0.50    sP0(k1_relat_1(sK4),k1_xboole_0) | spl6_2),
% 0.20/0.50    inference(backward_demodulation,[],[f267,f268])).
% 0.20/0.50  fof(f268,plain,(
% 0.20/0.50    k1_xboole_0 = sK3 | spl6_2),
% 0.20/0.50    inference(resolution,[],[f267,f58])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~sP0(X0,X1) | k1_xboole_0 = X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f37])).
% 0.20/0.50  fof(f267,plain,(
% 0.20/0.50    sP0(k1_relat_1(sK4),sK3) | spl6_2),
% 0.20/0.50    inference(subsumption_resolution,[],[f266,f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    v1_relat_1(sK4)),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3))) | ~v1_funct_2(sK4,k1_relat_1(sK4),sK3) | ~v1_funct_1(sK4)) & r1_tarski(k2_relat_1(sK4),sK3) & v1_funct_1(sK4) & v1_relat_1(sK4)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f13,f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1)) => ((~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3))) | ~v1_funct_2(sK4,k1_relat_1(sK4),sK3) | ~v1_funct_1(sK4)) & r1_tarski(k2_relat_1(sK4),sK3) & v1_funct_1(sK4) & v1_relat_1(sK4))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.50    inference(flattening,[],[f12])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ? [X0,X1] : (((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.20/0.50    inference(negated_conjecture,[],[f10])).
% 0.20/0.50  fof(f10,conjecture,(
% 0.20/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 0.20/0.50  fof(f266,plain,(
% 0.20/0.50    sP0(k1_relat_1(sK4),sK3) | ~v1_relat_1(sK4) | spl6_2),
% 0.20/0.50    inference(subsumption_resolution,[],[f265,f63])).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.50    inference(equality_resolution,[],[f47])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.50    inference(flattening,[],[f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.50    inference(nnf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.50  fof(f265,plain,(
% 0.20/0.50    sP0(k1_relat_1(sK4),sK3) | ~r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) | ~v1_relat_1(sK4) | spl6_2),
% 0.20/0.50    inference(subsumption_resolution,[],[f261,f40])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    r1_tarski(k2_relat_1(sK4),sK3)),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f261,plain,(
% 0.20/0.50    sP0(k1_relat_1(sK4),sK3) | ~r1_tarski(k2_relat_1(sK4),sK3) | ~r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) | ~v1_relat_1(sK4) | spl6_2),
% 0.20/0.50    inference(trivial_inequality_removal,[],[f260])).
% 0.20/0.50  fof(f260,plain,(
% 0.20/0.50    sP0(k1_relat_1(sK4),sK3) | k1_relat_1(sK4) != k1_relat_1(sK4) | ~r1_tarski(k2_relat_1(sK4),sK3) | ~r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) | ~v1_relat_1(sK4) | spl6_2),
% 0.20/0.50    inference(resolution,[],[f229,f78])).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    ~v1_funct_2(sK4,k1_relat_1(sK4),sK3) | spl6_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f76])).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    spl6_2 <=> v1_funct_2(sK4,k1_relat_1(sK4),sK3)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.50  fof(f229,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (v1_funct_2(X0,X1,X2) | sP0(X1,X2) | k1_relat_1(X0) != X1 | ~r1_tarski(k2_relat_1(X0),X2) | ~r1_tarski(k1_relat_1(X0),X1) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(resolution,[],[f159,f52])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.20/0.50    inference(flattening,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 0.20/0.50  fof(f159,plain,(
% 0.20/0.50    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | v1_funct_2(X5,X3,X4) | sP0(X3,X4) | k1_relat_1(X5) != X3) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f157,f60])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP1(X0,X2,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((sP2(X2,X1,X0) & sP1(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(definition_folding,[],[f19,f23,f22,f21])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 0.20/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP2(X2,X1,X0))),
% 0.20/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(flattening,[],[f18])).
% 0.20/0.50  % (12259)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.50  % (12238)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (12250)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.50  fof(f157,plain,(
% 0.20/0.50    ( ! [X4,X5,X3] : (k1_relat_1(X5) != X3 | v1_funct_2(X5,X3,X4) | sP0(X3,X4) | ~sP1(X3,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.20/0.50    inference(superposition,[],[f57,f53])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) != X0 | v1_funct_2(X1,X0,X2) | sP0(X0,X2) | ~sP1(X0,X1,X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP0(X0,X2) | ~sP1(X0,X1,X2))),
% 0.20/0.50    inference(rectify,[],[f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 0.20/0.50    inference(nnf_transformation,[],[f22])).
% 0.20/0.50  fof(f315,plain,(
% 0.20/0.50    spl6_3),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f314])).
% 0.20/0.50  fof(f314,plain,(
% 0.20/0.50    $false | spl6_3),
% 0.20/0.50    inference(subsumption_resolution,[],[f313,f38])).
% 0.20/0.50  fof(f313,plain,(
% 0.20/0.50    ~v1_relat_1(sK4) | spl6_3),
% 0.20/0.50    inference(subsumption_resolution,[],[f312,f63])).
% 0.20/0.50  % (12244)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.50  fof(f312,plain,(
% 0.20/0.50    ~r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) | ~v1_relat_1(sK4) | spl6_3),
% 0.20/0.50    inference(subsumption_resolution,[],[f311,f40])).
% 0.20/0.50  fof(f311,plain,(
% 0.20/0.50    ~r1_tarski(k2_relat_1(sK4),sK3) | ~r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) | ~v1_relat_1(sK4) | spl6_3),
% 0.20/0.50    inference(resolution,[],[f82,f52])).
% 0.20/0.50  fof(f82,plain,(
% 0.20/0.50    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3))) | spl6_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f80])).
% 0.20/0.50  fof(f80,plain,(
% 0.20/0.50    spl6_3 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.50  fof(f308,plain,(
% 0.20/0.50    spl6_10 | spl6_12),
% 0.20/0.50    inference(avatar_split_clause,[],[f307,f165,f148])).
% 0.20/0.50  fof(f165,plain,(
% 0.20/0.50    spl6_12 <=> ! [X0] : (~r1_tarski(k1_relat_1(sK4),X0) | ~v1_xboole_0(k2_zfmisc_1(X0,sK3)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.20/0.50  fof(f307,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(sK4),X0) | ~v1_xboole_0(k2_zfmisc_1(X0,sK3)) | ~r2_hidden(X1,sK4)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f304,f38])).
% 0.20/0.50  fof(f304,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(sK4),X0) | ~v1_relat_1(sK4) | ~v1_xboole_0(k2_zfmisc_1(X0,sK3)) | ~r2_hidden(X1,sK4)) )),
% 0.20/0.50    inference(resolution,[],[f40,f116])).
% 0.20/0.50  fof(f116,plain,(
% 0.20/0.50    ( ! [X6,X8,X7,X9] : (~r1_tarski(k2_relat_1(X6),X7) | ~r1_tarski(k1_relat_1(X6),X8) | ~v1_relat_1(X6) | ~v1_xboole_0(k2_zfmisc_1(X8,X7)) | ~r2_hidden(X9,X6)) )),
% 0.20/0.50    inference(resolution,[],[f52,f62])).
% 0.20/0.50  fof(f62,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.20/0.50  fof(f277,plain,(
% 0.20/0.50    spl6_2 | ~spl6_12),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f276])).
% 0.20/0.50  fof(f276,plain,(
% 0.20/0.50    $false | (spl6_2 | ~spl6_12)),
% 0.20/0.50    inference(subsumption_resolution,[],[f275,f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    v1_xboole_0(k1_xboole_0)),
% 0.20/0.50    inference(cnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    v1_xboole_0(k1_xboole_0)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.50  fof(f275,plain,(
% 0.20/0.50    ~v1_xboole_0(k1_xboole_0) | (spl6_2 | ~spl6_12)),
% 0.20/0.50    inference(forward_demodulation,[],[f270,f65])).
% 0.20/0.50  fof(f65,plain,(
% 0.20/0.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.50    inference(equality_resolution,[],[f51])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.50    inference(flattening,[],[f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.50    inference(nnf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.50  fof(f270,plain,(
% 0.20/0.50    ~v1_xboole_0(k2_zfmisc_1(k1_relat_1(sK4),k1_xboole_0)) | (spl6_2 | ~spl6_12)),
% 0.20/0.50    inference(backward_demodulation,[],[f222,f268])).
% 0.20/0.50  fof(f222,plain,(
% 0.20/0.50    ~v1_xboole_0(k2_zfmisc_1(k1_relat_1(sK4),sK3)) | ~spl6_12),
% 0.20/0.50    inference(resolution,[],[f166,f63])).
% 0.20/0.50  fof(f166,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_tarski(k1_relat_1(sK4),X0) | ~v1_xboole_0(k2_zfmisc_1(X0,sK3))) ) | ~spl6_12),
% 0.20/0.50    inference(avatar_component_clause,[],[f165])).
% 0.20/0.50  fof(f84,plain,(
% 0.20/0.50    spl6_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f39,f72])).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    spl6_1 <=> v1_funct_1(sK4)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    v1_funct_1(sK4)),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f83,plain,(
% 0.20/0.50    ~spl6_1 | ~spl6_2 | ~spl6_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f41,f80,f76,f72])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3))) | ~v1_funct_2(sK4,k1_relat_1(sK4),sK3) | ~v1_funct_1(sK4)),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (12241)------------------------------
% 0.20/0.50  % (12241)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (12241)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (12241)Memory used [KB]: 6268
% 0.20/0.50  % (12241)Time elapsed: 0.096 s
% 0.20/0.50  % (12241)------------------------------
% 0.20/0.50  % (12241)------------------------------
% 0.20/0.50  % (12251)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.50  % (12236)Success in time 0.143 s
%------------------------------------------------------------------------------
