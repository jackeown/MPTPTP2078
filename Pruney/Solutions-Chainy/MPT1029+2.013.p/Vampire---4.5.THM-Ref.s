%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:41 EST 2020

% Result     : Theorem 1.27s
% Output     : Refutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 140 expanded)
%              Number of leaves         :   16 (  42 expanded)
%              Depth                    :   13
%              Number of atoms          :  214 ( 608 expanded)
%              Number of equality atoms :   37 ( 137 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f120,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f67,f69,f83,f85,f119])).

fof(f119,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f118])).

fof(f118,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(resolution,[],[f112,f51])).

fof(f51,plain,(
    v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f41,f30])).

fof(f30,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f41,plain,(
    ! [X0] : v1_partfun1(k6_relat_1(X0),X0) ),
    inference(definition_unfolding,[],[f32,f31])).

fof(f31,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f32,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f112,plain,
    ( ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f88,f108])).

fof(f108,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(resolution,[],[f107,f98])).

fof(f98,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f89,f97])).

fof(f97,plain,
    ( ! [X5] : k1_xboole_0 = k2_zfmisc_1(X5,k1_xboole_0)
    | ~ spl4_3 ),
    inference(resolution,[],[f93,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f93,plain,
    ( ! [X2] : v1_xboole_0(k2_zfmisc_1(X2,k1_xboole_0))
    | ~ spl4_3 ),
    inference(resolution,[],[f75,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

fof(f75,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f58,f72])).

fof(f72,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_3 ),
    inference(resolution,[],[f58,f34])).

fof(f58,plain,
    ( v1_xboole_0(sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl4_3
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f89,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f87,f44])).

fof(f44,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl4_1
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f87,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f27,f49])).

fof(f49,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f27,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ v1_partfun1(sK2,sK0)
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( ~ v1_partfun1(X2,X0)
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ~ v1_partfun1(sK2,sK0)
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ v1_partfun1(X2,X0)
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ v1_partfun1(X2,X0)
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X2,X0,X1)
            & v1_funct_1(X2) )
         => ( v1_partfun1(X2,X0)
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

fof(f107,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0 )
    | ~ spl4_3 ),
    inference(resolution,[],[f92,f35])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f21])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f92,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl4_3 ),
    inference(resolution,[],[f75,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

% (11511)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f88,plain,
    ( ~ v1_partfun1(sK2,k1_xboole_0)
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f29,f49])).

fof(f29,plain,(
    ~ v1_partfun1(sK2,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f85,plain,(
    ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f84])).

fof(f84,plain,
    ( $false
    | ~ spl4_5 ),
    inference(resolution,[],[f66,f29])).

fof(f66,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl4_5
  <=> v1_partfun1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f83,plain,
    ( spl4_1
    | ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f82])).

fof(f82,plain,
    ( $false
    | spl4_1
    | ~ spl4_3 ),
    inference(trivial_inequality_removal,[],[f81])).

fof(f81,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl4_1
    | ~ spl4_3 ),
    inference(superposition,[],[f45,f72])).

fof(f45,plain,
    ( k1_xboole_0 != sK1
    | spl4_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f69,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f68])).

fof(f68,plain,
    ( $false
    | spl4_4 ),
    inference(resolution,[],[f62,f26])).

fof(f26,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f62,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl4_4
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f67,plain,
    ( spl4_3
    | ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f54,f64,f60,f56])).

fof(f54,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f53,f27])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_partfun1(sK2,X0)
      | ~ v1_funct_2(sK2,X0,X1)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f37,f25])).

fof(f25,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f50,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f28,f47,f43])).

% (11524)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
fof(f28,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:07:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.52  % (11516)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (11518)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (11520)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (11518)Refutation not found, incomplete strategy% (11518)------------------------------
% 0.21/0.53  % (11518)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (11518)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (11518)Memory used [KB]: 10618
% 0.21/0.53  % (11518)Time elapsed: 0.105 s
% 0.21/0.53  % (11518)------------------------------
% 0.21/0.53  % (11518)------------------------------
% 0.21/0.53  % (11508)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (11510)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.27/0.53  % (11523)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.27/0.53  % (11517)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.27/0.53  % (11523)Refutation not found, incomplete strategy% (11523)------------------------------
% 1.27/0.53  % (11523)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.54  % (11531)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.27/0.54  % (11523)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.54  
% 1.27/0.54  % (11523)Memory used [KB]: 6140
% 1.27/0.54  % (11523)Time elapsed: 0.004 s
% 1.27/0.54  % (11523)------------------------------
% 1.27/0.54  % (11523)------------------------------
% 1.27/0.54  % (11519)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.27/0.54  % (11509)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.27/0.54  % (11516)Refutation not found, incomplete strategy% (11516)------------------------------
% 1.27/0.54  % (11516)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.54  % (11516)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.54  
% 1.27/0.54  % (11516)Memory used [KB]: 10746
% 1.27/0.54  % (11516)Time elapsed: 0.125 s
% 1.27/0.54  % (11516)------------------------------
% 1.27/0.54  % (11516)------------------------------
% 1.27/0.54  % (11520)Refutation found. Thanks to Tanya!
% 1.27/0.54  % SZS status Theorem for theBenchmark
% 1.27/0.54  % (11512)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.27/0.54  % (11532)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.27/0.54  % (11533)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.27/0.54  % SZS output start Proof for theBenchmark
% 1.27/0.54  fof(f120,plain,(
% 1.27/0.54    $false),
% 1.27/0.54    inference(avatar_sat_refutation,[],[f50,f67,f69,f83,f85,f119])).
% 1.27/0.54  fof(f119,plain,(
% 1.27/0.54    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 1.27/0.54    inference(avatar_contradiction_clause,[],[f118])).
% 1.27/0.54  fof(f118,plain,(
% 1.27/0.54    $false | (~spl4_1 | ~spl4_2 | ~spl4_3)),
% 1.27/0.54    inference(resolution,[],[f112,f51])).
% 1.27/0.54  fof(f51,plain,(
% 1.27/0.54    v1_partfun1(k1_xboole_0,k1_xboole_0)),
% 1.27/0.54    inference(superposition,[],[f41,f30])).
% 1.27/0.54  fof(f30,plain,(
% 1.27/0.54    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.27/0.54    inference(cnf_transformation,[],[f5])).
% 1.27/0.54  fof(f5,axiom,(
% 1.27/0.54    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 1.27/0.54  fof(f41,plain,(
% 1.27/0.54    ( ! [X0] : (v1_partfun1(k6_relat_1(X0),X0)) )),
% 1.27/0.54    inference(definition_unfolding,[],[f32,f31])).
% 1.27/0.54  fof(f31,plain,(
% 1.27/0.54    ( ! [X0] : (k6_partfun1(X0) = k6_relat_1(X0)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f8])).
% 1.27/0.54  fof(f8,axiom,(
% 1.27/0.54    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0)),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.27/0.54  fof(f32,plain,(
% 1.27/0.54    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f7])).
% 1.27/0.54  fof(f7,axiom,(
% 1.27/0.54    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.27/0.54  fof(f112,plain,(
% 1.27/0.54    ~v1_partfun1(k1_xboole_0,k1_xboole_0) | (~spl4_1 | ~spl4_2 | ~spl4_3)),
% 1.27/0.54    inference(backward_demodulation,[],[f88,f108])).
% 1.27/0.54  fof(f108,plain,(
% 1.27/0.54    k1_xboole_0 = sK2 | (~spl4_1 | ~spl4_2 | ~spl4_3)),
% 1.27/0.54    inference(resolution,[],[f107,f98])).
% 1.27/0.54  fof(f98,plain,(
% 1.27/0.54    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl4_1 | ~spl4_2 | ~spl4_3)),
% 1.27/0.54    inference(backward_demodulation,[],[f89,f97])).
% 1.27/0.54  fof(f97,plain,(
% 1.27/0.54    ( ! [X5] : (k1_xboole_0 = k2_zfmisc_1(X5,k1_xboole_0)) ) | ~spl4_3),
% 1.27/0.54    inference(resolution,[],[f93,f34])).
% 1.27/0.54  fof(f34,plain,(
% 1.27/0.54    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.27/0.54    inference(cnf_transformation,[],[f13])).
% 1.27/0.54  fof(f13,plain,(
% 1.27/0.54    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.27/0.54    inference(ennf_transformation,[],[f1])).
% 1.27/0.54  fof(f1,axiom,(
% 1.27/0.54    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.27/0.54  fof(f93,plain,(
% 1.27/0.54    ( ! [X2] : (v1_xboole_0(k2_zfmisc_1(X2,k1_xboole_0))) ) | ~spl4_3),
% 1.27/0.54    inference(resolution,[],[f75,f38])).
% 1.27/0.54  fof(f38,plain,(
% 1.27/0.54    ( ! [X0,X1] : (~v1_xboole_0(X1) | v1_xboole_0(k2_zfmisc_1(X0,X1))) )),
% 1.27/0.54    inference(cnf_transformation,[],[f17])).
% 1.27/0.54  fof(f17,plain,(
% 1.27/0.54    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 1.27/0.54    inference(ennf_transformation,[],[f3])).
% 1.27/0.54  fof(f3,axiom,(
% 1.27/0.54    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).
% 1.27/0.54  fof(f75,plain,(
% 1.27/0.54    v1_xboole_0(k1_xboole_0) | ~spl4_3),
% 1.27/0.54    inference(backward_demodulation,[],[f58,f72])).
% 1.27/0.54  fof(f72,plain,(
% 1.27/0.54    k1_xboole_0 = sK1 | ~spl4_3),
% 1.27/0.54    inference(resolution,[],[f58,f34])).
% 1.27/0.54  fof(f58,plain,(
% 1.27/0.54    v1_xboole_0(sK1) | ~spl4_3),
% 1.27/0.54    inference(avatar_component_clause,[],[f56])).
% 1.27/0.54  fof(f56,plain,(
% 1.27/0.54    spl4_3 <=> v1_xboole_0(sK1)),
% 1.27/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.27/0.54  fof(f89,plain,(
% 1.27/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl4_1 | ~spl4_2)),
% 1.27/0.54    inference(backward_demodulation,[],[f87,f44])).
% 1.27/0.54  fof(f44,plain,(
% 1.27/0.54    k1_xboole_0 = sK1 | ~spl4_1),
% 1.27/0.54    inference(avatar_component_clause,[],[f43])).
% 1.27/0.54  fof(f43,plain,(
% 1.27/0.54    spl4_1 <=> k1_xboole_0 = sK1),
% 1.27/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.27/0.54  fof(f87,plain,(
% 1.27/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~spl4_2),
% 1.27/0.54    inference(backward_demodulation,[],[f27,f49])).
% 1.27/0.54  fof(f49,plain,(
% 1.27/0.54    k1_xboole_0 = sK0 | ~spl4_2),
% 1.27/0.54    inference(avatar_component_clause,[],[f47])).
% 1.27/0.54  fof(f47,plain,(
% 1.27/0.54    spl4_2 <=> k1_xboole_0 = sK0),
% 1.27/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.27/0.54  fof(f27,plain,(
% 1.27/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.27/0.54    inference(cnf_transformation,[],[f20])).
% 1.27/0.54  fof(f20,plain,(
% 1.27/0.54    ~v1_partfun1(sK2,sK0) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 1.27/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f19])).
% 1.27/0.54  fof(f19,plain,(
% 1.27/0.54    ? [X0,X1,X2] : (~v1_partfun1(X2,X0) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (~v1_partfun1(sK2,sK0) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 1.27/0.54    introduced(choice_axiom,[])).
% 1.27/0.54  fof(f12,plain,(
% 1.27/0.54    ? [X0,X1,X2] : (~v1_partfun1(X2,X0) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 1.27/0.54    inference(flattening,[],[f11])).
% 1.27/0.54  fof(f11,plain,(
% 1.27/0.54    ? [X0,X1,X2] : (((~v1_partfun1(X2,X0) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 1.27/0.54    inference(ennf_transformation,[],[f10])).
% 1.27/0.54  fof(f10,negated_conjecture,(
% 1.27/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.27/0.54    inference(negated_conjecture,[],[f9])).
% 1.27/0.54  fof(f9,conjecture,(
% 1.27/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).
% 1.27/0.54  fof(f107,plain,(
% 1.27/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) ) | ~spl4_3),
% 1.27/0.54    inference(resolution,[],[f92,f35])).
% 1.27/0.54  fof(f35,plain,(
% 1.27/0.54    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.27/0.54    inference(cnf_transformation,[],[f22])).
% 1.27/0.54  fof(f22,plain,(
% 1.27/0.54    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 1.27/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f21])).
% 1.27/0.54  fof(f21,plain,(
% 1.27/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.27/0.54    introduced(choice_axiom,[])).
% 1.27/0.54  fof(f14,plain,(
% 1.27/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.27/0.54    inference(ennf_transformation,[],[f2])).
% 1.27/0.54  fof(f2,axiom,(
% 1.27/0.54    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.27/0.54  fof(f92,plain,(
% 1.27/0.54    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))) ) | ~spl4_3),
% 1.27/0.54    inference(resolution,[],[f75,f39])).
% 1.27/0.54  fof(f39,plain,(
% 1.27/0.54    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f18])).
% 1.27/0.54  fof(f18,plain,(
% 1.27/0.54    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.27/0.54    inference(ennf_transformation,[],[f4])).
% 1.27/0.54  % (11511)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.27/0.55  fof(f4,axiom,(
% 1.27/0.55    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.27/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 1.27/0.55  fof(f88,plain,(
% 1.27/0.55    ~v1_partfun1(sK2,k1_xboole_0) | ~spl4_2),
% 1.27/0.55    inference(backward_demodulation,[],[f29,f49])).
% 1.27/0.55  fof(f29,plain,(
% 1.27/0.55    ~v1_partfun1(sK2,sK0)),
% 1.27/0.55    inference(cnf_transformation,[],[f20])).
% 1.27/0.55  fof(f85,plain,(
% 1.27/0.55    ~spl4_5),
% 1.27/0.55    inference(avatar_contradiction_clause,[],[f84])).
% 1.27/0.55  fof(f84,plain,(
% 1.27/0.55    $false | ~spl4_5),
% 1.27/0.55    inference(resolution,[],[f66,f29])).
% 1.27/0.55  fof(f66,plain,(
% 1.27/0.55    v1_partfun1(sK2,sK0) | ~spl4_5),
% 1.27/0.55    inference(avatar_component_clause,[],[f64])).
% 1.27/0.55  fof(f64,plain,(
% 1.27/0.55    spl4_5 <=> v1_partfun1(sK2,sK0)),
% 1.27/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.27/0.55  fof(f83,plain,(
% 1.27/0.55    spl4_1 | ~spl4_3),
% 1.27/0.55    inference(avatar_contradiction_clause,[],[f82])).
% 1.27/0.55  fof(f82,plain,(
% 1.27/0.55    $false | (spl4_1 | ~spl4_3)),
% 1.27/0.55    inference(trivial_inequality_removal,[],[f81])).
% 1.27/0.55  fof(f81,plain,(
% 1.27/0.55    k1_xboole_0 != k1_xboole_0 | (spl4_1 | ~spl4_3)),
% 1.27/0.55    inference(superposition,[],[f45,f72])).
% 1.27/0.55  fof(f45,plain,(
% 1.27/0.55    k1_xboole_0 != sK1 | spl4_1),
% 1.27/0.55    inference(avatar_component_clause,[],[f43])).
% 1.27/0.55  fof(f69,plain,(
% 1.27/0.55    spl4_4),
% 1.27/0.55    inference(avatar_contradiction_clause,[],[f68])).
% 1.27/0.55  fof(f68,plain,(
% 1.27/0.55    $false | spl4_4),
% 1.27/0.55    inference(resolution,[],[f62,f26])).
% 1.27/0.55  fof(f26,plain,(
% 1.27/0.55    v1_funct_2(sK2,sK0,sK1)),
% 1.27/0.55    inference(cnf_transformation,[],[f20])).
% 1.27/0.55  fof(f62,plain,(
% 1.27/0.55    ~v1_funct_2(sK2,sK0,sK1) | spl4_4),
% 1.27/0.55    inference(avatar_component_clause,[],[f60])).
% 1.27/0.55  fof(f60,plain,(
% 1.27/0.55    spl4_4 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.27/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.27/0.55  fof(f67,plain,(
% 1.27/0.55    spl4_3 | ~spl4_4 | spl4_5),
% 1.27/0.55    inference(avatar_split_clause,[],[f54,f64,f60,f56])).
% 1.27/0.55  fof(f54,plain,(
% 1.27/0.55    v1_partfun1(sK2,sK0) | ~v1_funct_2(sK2,sK0,sK1) | v1_xboole_0(sK1)),
% 1.27/0.55    inference(resolution,[],[f53,f27])).
% 1.27/0.55  fof(f53,plain,(
% 1.27/0.55    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_partfun1(sK2,X0) | ~v1_funct_2(sK2,X0,X1) | v1_xboole_0(X1)) )),
% 1.27/0.55    inference(resolution,[],[f37,f25])).
% 1.27/0.55  fof(f25,plain,(
% 1.27/0.55    v1_funct_1(sK2)),
% 1.27/0.55    inference(cnf_transformation,[],[f20])).
% 1.27/0.55  fof(f37,plain,(
% 1.27/0.55    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 1.27/0.55    inference(cnf_transformation,[],[f16])).
% 1.27/0.55  fof(f16,plain,(
% 1.27/0.55    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.27/0.55    inference(flattening,[],[f15])).
% 1.27/0.55  fof(f15,plain,(
% 1.27/0.55    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.27/0.55    inference(ennf_transformation,[],[f6])).
% 1.27/0.55  fof(f6,axiom,(
% 1.27/0.55    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 1.27/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 1.27/0.55  fof(f50,plain,(
% 1.27/0.55    ~spl4_1 | spl4_2),
% 1.27/0.55    inference(avatar_split_clause,[],[f28,f47,f43])).
% 1.27/0.55  % (11524)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.27/0.55  fof(f28,plain,(
% 1.27/0.55    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 1.27/0.55    inference(cnf_transformation,[],[f20])).
% 1.27/0.55  % SZS output end Proof for theBenchmark
% 1.27/0.55  % (11520)------------------------------
% 1.27/0.55  % (11520)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.55  % (11520)Termination reason: Refutation
% 1.27/0.55  
% 1.27/0.55  % (11520)Memory used [KB]: 6268
% 1.27/0.55  % (11520)Time elapsed: 0.115 s
% 1.27/0.55  % (11520)------------------------------
% 1.27/0.55  % (11520)------------------------------
% 1.27/0.55  % (11534)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.51/0.55  % (11507)Success in time 0.185 s
%------------------------------------------------------------------------------
