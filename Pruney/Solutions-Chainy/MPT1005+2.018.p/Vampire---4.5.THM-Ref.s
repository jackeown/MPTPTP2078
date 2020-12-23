%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:41 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 130 expanded)
%              Number of leaves         :   15 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :  168 ( 318 expanded)
%              Number of equality atoms :   56 ( 135 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f124,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f38,f43,f48,f53,f64,f68,f95,f119])).

fof(f119,plain,
    ( ~ spl3_3
    | ~ spl3_5
    | spl3_7
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f118])).

fof(f118,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_5
    | spl3_7
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f63,f117])).

fof(f117,plain,
    ( ! [X0,X1] : k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,k1_xboole_0,X1)
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f116,f93])).

fof(f93,plain,
    ( ! [X3] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X3)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl3_9
  <=> ! [X3] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f116,plain,
    ( ! [X0,X1] : k9_relat_1(k1_xboole_0,X1) = k7_relset_1(k1_xboole_0,X0,k1_xboole_0,X1)
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f112,f52])).

fof(f52,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl3_5
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f112,plain,
    ( ! [X0,X1] : k9_relat_1(sK2,X1) = k7_relset_1(k1_xboole_0,X0,sK2,X1)
    | ~ spl3_3 ),
    inference(resolution,[],[f80,f42])).

fof(f42,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f80,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0))
      | k7_relset_1(k1_xboole_0,X3,X4,X5) = k9_relat_1(X4,X5) ) ),
    inference(superposition,[],[f28,f30])).

fof(f30,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f63,plain,
    ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl3_7
  <=> k1_xboole_0 = k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f95,plain,
    ( ~ spl3_8
    | spl3_9
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f87,f51,f41,f92,f66])).

fof(f66,plain,
    ( spl3_8
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f87,plain,
    ( ! [X1] :
        ( k1_xboole_0 = k9_relat_1(k1_xboole_0,X1)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(superposition,[],[f75,f84])).

fof(f84,plain,
    ( ! [X0,X1] : k7_relset_1(X0,k1_xboole_0,k1_xboole_0,X1) = k9_relat_1(k1_xboole_0,X1)
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f81,f52])).

fof(f81,plain,
    ( ! [X0,X1] : k7_relset_1(X0,k1_xboole_0,sK2,X1) = k9_relat_1(sK2,X1)
    | ~ spl3_3 ),
    inference(resolution,[],[f79,f42])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | k7_relset_1(X0,k1_xboole_0,X1,X2) = k9_relat_1(X1,X2) ) ),
    inference(superposition,[],[f28,f29])).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k7_relset_1(X1,k1_xboole_0,X0,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f74,f29])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
      | k1_xboole_0 = k7_relset_1(X1,k1_xboole_0,X0,X2) ) ),
    inference(resolution,[],[f73,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k7_relset_1(X1,X2,X0,X3),X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f27,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(f68,plain,
    ( spl3_8
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f56,f51,f41,f66])).

fof(f56,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(superposition,[],[f42,f52])).

fof(f64,plain,
    ( ~ spl3_7
    | spl3_1
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f55,f51,f32,f62])).

fof(f32,plain,
    ( spl3_1
  <=> k1_xboole_0 = k7_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f55,plain,
    ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)
    | spl3_1
    | ~ spl3_5 ),
    inference(superposition,[],[f33,f52])).

fof(f33,plain,
    ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f53,plain,
    ( spl3_5
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f49,f46,f51])).

fof(f46,plain,
    ( spl3_4
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f49,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_4 ),
    inference(resolution,[],[f47,f22])).

fof(f47,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f46])).

fof(f48,plain,
    ( spl3_4
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f44,f41,f46])).

fof(f44,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl3_3 ),
    inference(resolution,[],[f23,f42])).

fof(f43,plain,
    ( spl3_3
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f39,f36,f41])).

fof(f36,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f39,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f37,f30])).

fof(f37,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f38,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f20,f36])).

fof(f20,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) )
   => ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
       => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_1(X2) )
       => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_2(X2,k1_xboole_0,X0)
          & v1_funct_1(X2) )
       => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
     => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_2)).

fof(f34,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f21,f32])).

fof(f21,plain,(
    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:42:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (1963)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.48  % (1964)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.49  % (1971)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (1972)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  % (1963)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % (1975)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.50  % (1967)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f124,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f34,f38,f43,f48,f53,f64,f68,f95,f119])).
% 0.22/0.51  fof(f119,plain,(
% 0.22/0.51    ~spl3_3 | ~spl3_5 | spl3_7 | ~spl3_9),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f118])).
% 0.22/0.51  fof(f118,plain,(
% 0.22/0.51    $false | (~spl3_3 | ~spl3_5 | spl3_7 | ~spl3_9)),
% 0.22/0.51    inference(subsumption_resolution,[],[f63,f117])).
% 0.22/0.51  fof(f117,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,k1_xboole_0,X1)) ) | (~spl3_3 | ~spl3_5 | ~spl3_9)),
% 0.22/0.51    inference(forward_demodulation,[],[f116,f93])).
% 0.22/0.51  fof(f93,plain,(
% 0.22/0.51    ( ! [X3] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X3)) ) | ~spl3_9),
% 0.22/0.51    inference(avatar_component_clause,[],[f92])).
% 0.22/0.51  fof(f92,plain,(
% 0.22/0.51    spl3_9 <=> ! [X3] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.51  fof(f116,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k9_relat_1(k1_xboole_0,X1) = k7_relset_1(k1_xboole_0,X0,k1_xboole_0,X1)) ) | (~spl3_3 | ~spl3_5)),
% 0.22/0.51    inference(forward_demodulation,[],[f112,f52])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    k1_xboole_0 = sK2 | ~spl3_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f51])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    spl3_5 <=> k1_xboole_0 = sK2),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.51  fof(f112,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k9_relat_1(sK2,X1) = k7_relset_1(k1_xboole_0,X0,sK2,X1)) ) | ~spl3_3),
% 0.22/0.51    inference(resolution,[],[f80,f42])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl3_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.51  fof(f80,plain,(
% 0.22/0.51    ( ! [X4,X5,X3] : (~m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0)) | k7_relset_1(k1_xboole_0,X3,X4,X5) = k9_relat_1(X4,X5)) )),
% 0.22/0.51    inference(superposition,[],[f28,f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.22/0.51    inference(equality_resolution,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.51    inference(flattening,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.51    inference(nnf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) | spl3_7),
% 0.22/0.51    inference(avatar_component_clause,[],[f62])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    spl3_7 <=> k1_xboole_0 = k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.51  fof(f95,plain,(
% 0.22/0.51    ~spl3_8 | spl3_9 | ~spl3_3 | ~spl3_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f87,f51,f41,f92,f66])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    spl3_8 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.51  fof(f87,plain,(
% 0.22/0.51    ( ! [X1] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))) ) | (~spl3_3 | ~spl3_5)),
% 0.22/0.51    inference(superposition,[],[f75,f84])).
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k7_relset_1(X0,k1_xboole_0,k1_xboole_0,X1) = k9_relat_1(k1_xboole_0,X1)) ) | (~spl3_3 | ~spl3_5)),
% 0.22/0.51    inference(forward_demodulation,[],[f81,f52])).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k7_relset_1(X0,k1_xboole_0,sK2,X1) = k9_relat_1(sK2,X1)) ) | ~spl3_3),
% 0.22/0.51    inference(resolution,[],[f79,f42])).
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | k7_relset_1(X0,k1_xboole_0,X1,X2) = k9_relat_1(X1,X2)) )),
% 0.22/0.51    inference(superposition,[],[f28,f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.51    inference(equality_resolution,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k1_xboole_0 = k7_relset_1(X1,k1_xboole_0,X0,X2) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))) )),
% 0.22/0.51    inference(forward_demodulation,[],[f74,f29])).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) | k1_xboole_0 = k7_relset_1(X1,k1_xboole_0,X0,X2)) )),
% 0.22/0.51    inference(resolution,[],[f73,f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.22/0.51    inference(ennf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (r1_tarski(k7_relset_1(X1,X2,X0,X3),X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.22/0.51    inference(resolution,[],[f27,f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,plain,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.22/0.51    inference(unused_predicate_definition_removal,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    spl3_8 | ~spl3_3 | ~spl3_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f56,f51,f41,f66])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl3_3 | ~spl3_5)),
% 0.22/0.51    inference(superposition,[],[f42,f52])).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    ~spl3_7 | spl3_1 | ~spl3_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f55,f51,f32,f62])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    spl3_1 <=> k1_xboole_0 = k7_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) | (spl3_1 | ~spl3_5)),
% 0.22/0.51    inference(superposition,[],[f33,f52])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) | spl3_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f32])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    spl3_5 | ~spl3_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f49,f46,f51])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    spl3_4 <=> r1_tarski(sK2,k1_xboole_0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    k1_xboole_0 = sK2 | ~spl3_4),
% 0.22/0.51    inference(resolution,[],[f47,f22])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    r1_tarski(sK2,k1_xboole_0) | ~spl3_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f46])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    spl3_4 | ~spl3_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f44,f41,f46])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    r1_tarski(sK2,k1_xboole_0) | ~spl3_3),
% 0.22/0.51    inference(resolution,[],[f23,f42])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    spl3_3 | ~spl3_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f39,f36,f41])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    spl3_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl3_2),
% 0.22/0.51    inference(forward_demodulation,[],[f37,f30])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | ~spl3_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f36])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    spl3_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f20,f36])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ? [X0,X1,X2] : (k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) => (k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ? [X0,X1,X2] : (k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))))),
% 0.22/0.51    inference(ennf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.22/0.51    inference(pure_predicate_removal,[],[f9])).
% 0.22/0.51  fof(f9,plain,(
% 0.22/0.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_1(X2)) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.22/0.51    inference(pure_predicate_removal,[],[f7])).
% 0.22/0.51  fof(f7,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.22/0.51    inference(negated_conjecture,[],[f6])).
% 0.22/0.51  fof(f6,conjecture,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_2)).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ~spl3_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f21,f32])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (1963)------------------------------
% 0.22/0.51  % (1963)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (1963)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (1963)Memory used [KB]: 10618
% 0.22/0.51  % (1963)Time elapsed: 0.066 s
% 0.22/0.51  % (1963)------------------------------
% 0.22/0.51  % (1963)------------------------------
% 0.22/0.51  % (1955)Success in time 0.146 s
%------------------------------------------------------------------------------
