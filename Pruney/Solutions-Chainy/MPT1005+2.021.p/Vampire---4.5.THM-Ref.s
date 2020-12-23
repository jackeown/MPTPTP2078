%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:42 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   60 (  87 expanded)
%              Number of leaves         :   15 (  31 expanded)
%              Depth                    :   11
%              Number of atoms          :  145 ( 214 expanded)
%              Number of equality atoms :   49 (  82 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f82,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f41,f45,f50,f57,f64,f80])).

fof(f80,plain,
    ( ~ spl4_4
    | ~ spl4_5
    | spl4_6 ),
    inference(avatar_contradiction_clause,[],[f79])).

fof(f79,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_5
    | spl4_6 ),
    inference(subsumption_resolution,[],[f63,f78])).

fof(f78,plain,
    ( ! [X0,X1] : k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,k1_xboole_0,X1)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f77,f25])).

fof(f25,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

fof(f77,plain,
    ( ! [X0,X1] : k7_relset_1(k1_xboole_0,X0,k1_xboole_0,X1) = k9_relat_1(k1_xboole_0,X1)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f75,f56])).

fof(f56,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f75,plain,
    ( ! [X0,X1] : k7_relset_1(k1_xboole_0,X0,sK2,X1) = k9_relat_1(sK2,X1)
    | ~ spl4_4 ),
    inference(resolution,[],[f74,f49])).

fof(f49,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl4_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f74,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0))
      | k7_relset_1(k1_xboole_0,X3,X4,X5) = k9_relat_1(X4,X5) ) ),
    inference(superposition,[],[f31,f33])).

fof(f33,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f31,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f63,plain,
    ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl4_6
  <=> k1_xboole_0 = k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f64,plain,
    ( ~ spl4_6
    | spl4_1
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f59,f55,f35,f62])).

fof(f35,plain,
    ( spl4_1
  <=> k1_xboole_0 = k7_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f59,plain,
    ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)
    | spl4_1
    | ~ spl4_5 ),
    inference(superposition,[],[f36,f56])).

fof(f36,plain,
    ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f57,plain,
    ( spl4_5
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f53,f48,f43,f55])).

fof(f43,plain,
    ( spl4_3
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f53,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(resolution,[],[f52,f26])).

fof(f26,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5,X6] :
                  ( ( r2_hidden(X6,X1)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

fof(f52,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(resolution,[],[f51,f49])).

fof(f51,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl4_3 ),
    inference(resolution,[],[f30,f44])).

fof(f44,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f50,plain,
    ( spl4_4
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f46,f39,f48])).

fof(f39,plain,
    ( spl4_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f46,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f40,f33])).

fof(f40,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f45,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f24,f43])).

fof(f24,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f41,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f22,f39])).

fof(f22,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) )
   => ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
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
    inference(pure_predicate_removal,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_2(X2,k1_xboole_0,X0)
          & v1_funct_1(X2) )
       => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
     => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_2)).

fof(f37,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f23,f35])).

fof(f23,plain,(
    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:42:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.46  % (7271)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.47  % (7278)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.47  % (7286)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.19/0.47  % (7280)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.19/0.48  % (7279)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.19/0.48  % (7279)Refutation not found, incomplete strategy% (7279)------------------------------
% 0.19/0.48  % (7279)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.48  % (7279)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.48  
% 0.19/0.48  % (7279)Memory used [KB]: 1663
% 0.19/0.48  % (7279)Time elapsed: 0.071 s
% 0.19/0.48  % (7279)------------------------------
% 0.19/0.48  % (7279)------------------------------
% 0.19/0.48  % (7272)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.19/0.48  % (7286)Refutation not found, incomplete strategy% (7286)------------------------------
% 0.19/0.48  % (7286)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.48  % (7286)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.48  
% 0.19/0.48  % (7286)Memory used [KB]: 10490
% 0.19/0.48  % (7286)Time elapsed: 0.081 s
% 0.19/0.48  % (7286)------------------------------
% 0.19/0.48  % (7286)------------------------------
% 0.19/0.49  % (7274)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.19/0.49  % (7272)Refutation found. Thanks to Tanya!
% 0.19/0.49  % SZS status Theorem for theBenchmark
% 0.19/0.49  % SZS output start Proof for theBenchmark
% 0.19/0.49  fof(f82,plain,(
% 0.19/0.49    $false),
% 0.19/0.49    inference(avatar_sat_refutation,[],[f37,f41,f45,f50,f57,f64,f80])).
% 0.19/0.49  fof(f80,plain,(
% 0.19/0.49    ~spl4_4 | ~spl4_5 | spl4_6),
% 0.19/0.49    inference(avatar_contradiction_clause,[],[f79])).
% 0.19/0.49  fof(f79,plain,(
% 0.19/0.49    $false | (~spl4_4 | ~spl4_5 | spl4_6)),
% 0.19/0.49    inference(subsumption_resolution,[],[f63,f78])).
% 0.19/0.49  fof(f78,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,k1_xboole_0,X1)) ) | (~spl4_4 | ~spl4_5)),
% 0.19/0.49    inference(forward_demodulation,[],[f77,f25])).
% 0.19/0.49  fof(f25,plain,(
% 0.19/0.49    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f4])).
% 0.19/0.49  fof(f4,axiom,(
% 0.19/0.49    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
% 0.19/0.49  fof(f77,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k7_relset_1(k1_xboole_0,X0,k1_xboole_0,X1) = k9_relat_1(k1_xboole_0,X1)) ) | (~spl4_4 | ~spl4_5)),
% 0.19/0.49    inference(forward_demodulation,[],[f75,f56])).
% 0.19/0.49  fof(f56,plain,(
% 0.19/0.49    k1_xboole_0 = sK2 | ~spl4_5),
% 0.19/0.49    inference(avatar_component_clause,[],[f55])).
% 0.19/0.49  fof(f55,plain,(
% 0.19/0.49    spl4_5 <=> k1_xboole_0 = sK2),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.19/0.49  fof(f75,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k7_relset_1(k1_xboole_0,X0,sK2,X1) = k9_relat_1(sK2,X1)) ) | ~spl4_4),
% 0.19/0.49    inference(resolution,[],[f74,f49])).
% 0.19/0.49  fof(f49,plain,(
% 0.19/0.49    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl4_4),
% 0.19/0.49    inference(avatar_component_clause,[],[f48])).
% 0.19/0.49  fof(f48,plain,(
% 0.19/0.49    spl4_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.19/0.49  fof(f74,plain,(
% 0.19/0.49    ( ! [X4,X5,X3] : (~m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0)) | k7_relset_1(k1_xboole_0,X3,X4,X5) = k9_relat_1(X4,X5)) )),
% 0.19/0.49    inference(superposition,[],[f31,f33])).
% 0.19/0.49  fof(f33,plain,(
% 0.19/0.49    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.19/0.49    inference(equality_resolution,[],[f28])).
% 0.19/0.49  fof(f28,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.19/0.49    inference(cnf_transformation,[],[f21])).
% 0.19/0.49  fof(f21,plain,(
% 0.19/0.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.19/0.49    inference(flattening,[],[f20])).
% 0.19/0.49  fof(f20,plain,(
% 0.19/0.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.19/0.49    inference(nnf_transformation,[],[f2])).
% 0.19/0.49  fof(f2,axiom,(
% 0.19/0.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.19/0.49  fof(f31,plain,(
% 0.19/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f15])).
% 0.19/0.49  fof(f15,plain,(
% 0.19/0.49    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.49    inference(ennf_transformation,[],[f5])).
% 0.19/0.49  fof(f5,axiom,(
% 0.19/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.19/0.49  fof(f63,plain,(
% 0.19/0.49    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) | spl4_6),
% 0.19/0.49    inference(avatar_component_clause,[],[f62])).
% 0.19/0.49  fof(f62,plain,(
% 0.19/0.49    spl4_6 <=> k1_xboole_0 = k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.19/0.49  fof(f64,plain,(
% 0.19/0.49    ~spl4_6 | spl4_1 | ~spl4_5),
% 0.19/0.49    inference(avatar_split_clause,[],[f59,f55,f35,f62])).
% 0.19/0.49  fof(f35,plain,(
% 0.19/0.49    spl4_1 <=> k1_xboole_0 = k7_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.19/0.49  fof(f59,plain,(
% 0.19/0.49    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) | (spl4_1 | ~spl4_5)),
% 0.19/0.49    inference(superposition,[],[f36,f56])).
% 0.19/0.49  fof(f36,plain,(
% 0.19/0.49    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) | spl4_1),
% 0.19/0.49    inference(avatar_component_clause,[],[f35])).
% 0.19/0.49  fof(f57,plain,(
% 0.19/0.49    spl4_5 | ~spl4_3 | ~spl4_4),
% 0.19/0.49    inference(avatar_split_clause,[],[f53,f48,f43,f55])).
% 0.19/0.49  fof(f43,plain,(
% 0.19/0.49    spl4_3 <=> v1_xboole_0(k1_xboole_0)),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.19/0.49  fof(f53,plain,(
% 0.19/0.49    k1_xboole_0 = sK2 | (~spl4_3 | ~spl4_4)),
% 0.19/0.49    inference(resolution,[],[f52,f26])).
% 0.19/0.49  fof(f26,plain,(
% 0.19/0.49    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.19/0.49    inference(cnf_transformation,[],[f19])).
% 0.19/0.49  fof(f19,plain,(
% 0.19/0.49    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 0.19/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f18])).
% 0.19/0.49  fof(f18,plain,(
% 0.19/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.19/0.49    introduced(choice_axiom,[])).
% 0.19/0.49  fof(f13,plain,(
% 0.19/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.19/0.49    inference(ennf_transformation,[],[f11])).
% 0.19/0.49  fof(f11,plain,(
% 0.19/0.49    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.19/0.49    inference(pure_predicate_removal,[],[f6])).
% 0.19/0.49  fof(f6,axiom,(
% 0.19/0.49    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).
% 0.19/0.49  fof(f52,plain,(
% 0.19/0.49    ( ! [X0] : (~r2_hidden(X0,sK2)) ) | (~spl4_3 | ~spl4_4)),
% 0.19/0.49    inference(resolution,[],[f51,f49])).
% 0.19/0.49  fof(f51,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~r2_hidden(X1,X0)) ) | ~spl4_3),
% 0.19/0.49    inference(resolution,[],[f30,f44])).
% 0.19/0.49  fof(f44,plain,(
% 0.19/0.49    v1_xboole_0(k1_xboole_0) | ~spl4_3),
% 0.19/0.49    inference(avatar_component_clause,[],[f43])).
% 0.19/0.49  fof(f30,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f14])).
% 0.19/0.49  fof(f14,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.19/0.49    inference(ennf_transformation,[],[f3])).
% 0.19/0.49  fof(f3,axiom,(
% 0.19/0.49    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.19/0.49  fof(f50,plain,(
% 0.19/0.49    spl4_4 | ~spl4_2),
% 0.19/0.49    inference(avatar_split_clause,[],[f46,f39,f48])).
% 0.19/0.49  fof(f39,plain,(
% 0.19/0.49    spl4_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.19/0.49  fof(f46,plain,(
% 0.19/0.49    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl4_2),
% 0.19/0.49    inference(forward_demodulation,[],[f40,f33])).
% 0.19/0.49  fof(f40,plain,(
% 0.19/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | ~spl4_2),
% 0.19/0.49    inference(avatar_component_clause,[],[f39])).
% 0.19/0.49  fof(f45,plain,(
% 0.19/0.49    spl4_3),
% 0.19/0.49    inference(avatar_split_clause,[],[f24,f43])).
% 0.19/0.49  fof(f24,plain,(
% 0.19/0.49    v1_xboole_0(k1_xboole_0)),
% 0.19/0.49    inference(cnf_transformation,[],[f1])).
% 0.19/0.49  fof(f1,axiom,(
% 0.19/0.49    v1_xboole_0(k1_xboole_0)),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.19/0.49  fof(f41,plain,(
% 0.19/0.49    spl4_2),
% 0.19/0.49    inference(avatar_split_clause,[],[f22,f39])).
% 0.19/0.49  fof(f22,plain,(
% 0.19/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.19/0.49    inference(cnf_transformation,[],[f17])).
% 0.19/0.49  fof(f17,plain,(
% 0.19/0.49    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.19/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f16])).
% 0.19/0.49  fof(f16,plain,(
% 0.19/0.49    ? [X0,X1,X2] : (k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) => (k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))))),
% 0.19/0.49    introduced(choice_axiom,[])).
% 0.19/0.49  fof(f12,plain,(
% 0.19/0.49    ? [X0,X1,X2] : (k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))))),
% 0.19/0.49    inference(ennf_transformation,[],[f10])).
% 0.19/0.49  fof(f10,plain,(
% 0.19/0.49    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.19/0.49    inference(pure_predicate_removal,[],[f9])).
% 0.19/0.49  fof(f9,plain,(
% 0.19/0.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_1(X2)) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.19/0.49    inference(pure_predicate_removal,[],[f8])).
% 0.19/0.49  fof(f8,negated_conjecture,(
% 0.19/0.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.19/0.49    inference(negated_conjecture,[],[f7])).
% 0.19/0.49  fof(f7,conjecture,(
% 0.19/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_2)).
% 0.19/0.49  fof(f37,plain,(
% 0.19/0.49    ~spl4_1),
% 0.19/0.49    inference(avatar_split_clause,[],[f23,f35])).
% 0.19/0.49  fof(f23,plain,(
% 0.19/0.49    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.19/0.49    inference(cnf_transformation,[],[f17])).
% 0.19/0.49  % SZS output end Proof for theBenchmark
% 0.19/0.49  % (7272)------------------------------
% 0.19/0.49  % (7272)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (7272)Termination reason: Refutation
% 0.19/0.49  
% 0.19/0.49  % (7272)Memory used [KB]: 10618
% 0.19/0.49  % (7272)Time elapsed: 0.005 s
% 0.19/0.49  % (7272)------------------------------
% 0.19/0.49  % (7272)------------------------------
% 0.19/0.49  % (7270)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.19/0.49  % (7264)Success in time 0.141 s
%------------------------------------------------------------------------------
