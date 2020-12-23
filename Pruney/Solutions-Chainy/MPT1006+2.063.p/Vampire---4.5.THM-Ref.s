%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   43 (  69 expanded)
%              Number of leaves         :   10 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :  108 ( 192 expanded)
%              Number of equality atoms :   36 (  72 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (2565)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
fof(f55,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f33,f37,f42,f52,f54])).

fof(f54,plain,
    ( spl3_1
    | ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f53])).

fof(f53,plain,
    ( $false
    | spl3_1
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f28,f50])).

fof(f50,plain,
    ( ! [X0,X1] : k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,sK2,X1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl3_5
  <=> ! [X1,X0] : k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,sK2,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f28,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl3_1
  <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f52,plain,
    ( spl3_5
    | ~ spl3_4
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f47,f35,f40,f49])).

fof(f40,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f35,plain,
    ( spl3_3
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f47,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,sK2,X1) )
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f46,f25])).

fof(f25,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
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

fof(f46,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        | k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,sK2,X1) )
    | ~ spl3_3 ),
    inference(resolution,[],[f45,f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f45,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k8_relset_1(X0,X1,sK2,X2),X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl3_3 ),
    inference(resolution,[],[f23,f36])).

fof(f36,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k8_relset_1(X0,X1,X3,X2),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k8_relset_1(X0,X1,X3,X2),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X3) )
     => r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_2)).

fof(f42,plain,
    ( spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f38,f31,f40])).

fof(f31,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f38,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f32,f25])).

fof(f32,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f37,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f16,f35])).

fof(f16,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_1(X2) )
   => ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_1(X2) )
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_2(X2,k1_xboole_0,X0)
          & v1_funct_1(X2) )
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
     => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_2)).

fof(f33,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f17,f31])).

fof(f17,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f29,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f18,f27])).

fof(f18,plain,(
    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:39:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (2548)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.47  % (2552)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.48  % (2554)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.48  % (2552)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % (2546)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (2547)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  % (2565)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f29,f33,f37,f42,f52,f54])).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    spl3_1 | ~spl3_5),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f53])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    $false | (spl3_1 | ~spl3_5)),
% 0.20/0.48    inference(subsumption_resolution,[],[f28,f50])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,sK2,X1)) ) | ~spl3_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f49])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    spl3_5 <=> ! [X1,X0] : k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,sK2,X1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) | spl3_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    spl3_1 <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    spl3_5 | ~spl3_4 | ~spl3_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f47,f35,f40,f49])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    spl3_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    spl3_3 <=> v1_funct_1(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,sK2,X1)) ) | ~spl3_3),
% 0.20/0.48    inference(forward_demodulation,[],[f46,f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.48    inference(equality_resolution,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.48    inference(flattening,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.48    inference(nnf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) | k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,sK2,X1)) ) | ~spl3_3),
% 0.20/0.48    inference(resolution,[],[f45,f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r1_tarski(k8_relset_1(X0,X1,sK2,X2),X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl3_3),
% 0.20/0.48    inference(resolution,[],[f23,f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    v1_funct_1(sK2) | ~spl3_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f35])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r1_tarski(k8_relset_1(X0,X1,X3,X2),X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3] : (r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))),
% 0.20/0.48    inference(flattening,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3] : (r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => r1_tarski(k8_relset_1(X0,X1,X3,X2),X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_2)).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    spl3_4 | ~spl3_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f38,f31,f40])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    spl3_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl3_2),
% 0.20/0.48    inference(forward_demodulation,[],[f32,f25])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | ~spl3_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f31])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    spl3_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f16,f35])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    v1_funct_1(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) & v1_funct_1(sK2)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_1(X2)) => (k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) & v1_funct_1(sK2))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f8,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_1(X2))),
% 0.20/0.48    inference(flattening,[],[f7])).
% 0.20/0.48  fof(f7,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_1(X2)))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,plain,(
% 0.20/0.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.20/0.48    inference(pure_predicate_removal,[],[f5])).
% 0.20/0.48  fof(f5,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.20/0.48    inference(negated_conjecture,[],[f4])).
% 0.20/0.48  fof(f4,conjecture,(
% 0.20/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_2)).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    spl3_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f17,f31])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ~spl3_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f18,f27])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (2552)------------------------------
% 0.20/0.48  % (2552)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (2552)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (2552)Memory used [KB]: 10618
% 0.20/0.48  % (2552)Time elapsed: 0.066 s
% 0.20/0.48  % (2552)------------------------------
% 0.20/0.48  % (2552)------------------------------
% 0.20/0.48  % (2545)Success in time 0.126 s
%------------------------------------------------------------------------------
