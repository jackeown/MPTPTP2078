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
% DateTime   : Thu Dec  3 13:10:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   31 (  54 expanded)
%              Number of leaves         :    6 (  15 expanded)
%              Depth                    :    8
%              Number of atoms          :   70 ( 152 expanded)
%              Number of equality atoms :   23 (  58 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f39,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f16,f20,f24,f35,f38])).

% (28815)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
fof(f38,plain,
    ( spl3_1
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f37])).

fof(f37,plain,
    ( $false
    | spl3_1
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f36,f15])).

fof(f15,plain,
    ( sK1 != sK2
    | spl3_1 ),
    inference(avatar_component_clause,[],[f14])).

fof(f14,plain,
    ( spl3_1
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f36,plain,
    ( sK1 = sK2
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f34,f27])).

fof(f27,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl3_3 ),
    inference(resolution,[],[f23,f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f23,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f22])).

fof(f22,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f34,plain,
    ( sK2 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl3_5
  <=> sK2 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f35,plain,
    ( spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f26,f18,f33])).

fof(f18,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f26,plain,
    ( sK2 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f25,f9])).

fof(f9,plain,(
    k3_subset_1(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k3_subset_1(u1_struct_0(X0),X1) = k3_subset_1(u1_struct_0(X0),X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k3_subset_1(u1_struct_0(X0),X1) = k3_subset_1(u1_struct_0(X0),X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,plain,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
           => ( k3_subset_1(u1_struct_0(X0),X1) = k3_subset_1(u1_struct_0(X0),X2)
             => X1 = X2 ) ) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( k3_subset_1(u1_struct_0(X0),X1) = k3_subset_1(u1_struct_0(X0),X2)
                 => X1 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k3_subset_1(u1_struct_0(X0),X1) = k3_subset_1(u1_struct_0(X0),X2)
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_tops_1)).

fof(f25,plain,
    ( sK2 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2))
    | ~ spl3_2 ),
    inference(resolution,[],[f19,f12])).

fof(f19,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f18])).

fof(f24,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f11,f22])).

fof(f11,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f6])).

fof(f20,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f8,f18])).

fof(f8,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f6])).

fof(f16,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f10,f14])).

fof(f10,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:49:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.48  % (28818)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (28818)Refutation not found, incomplete strategy% (28818)------------------------------
% 0.20/0.48  % (28818)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (28818)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (28818)Memory used [KB]: 6012
% 0.20/0.48  % (28818)Time elapsed: 0.002 s
% 0.20/0.48  % (28818)------------------------------
% 0.20/0.48  % (28818)------------------------------
% 0.20/0.49  % (28819)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.49  % (28806)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.49  % (28809)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (28806)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f16,f20,f24,f35,f38])).
% 0.20/0.49  % (28815)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    spl3_1 | ~spl3_3 | ~spl3_5),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    $false | (spl3_1 | ~spl3_3 | ~spl3_5)),
% 0.20/0.49    inference(subsumption_resolution,[],[f36,f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    sK1 != sK2 | spl3_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    spl3_1 <=> sK1 = sK2),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    sK1 = sK2 | (~spl3_3 | ~spl3_5)),
% 0.20/0.49    inference(forward_demodulation,[],[f34,f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl3_3),
% 0.20/0.49    inference(resolution,[],[f23,f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,plain,(
% 0.20/0.49    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    sK2 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl3_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    spl3_5 <=> sK2 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    spl3_5 | ~spl3_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f26,f18,f33])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    spl3_2 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    sK2 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl3_2),
% 0.20/0.49    inference(forward_demodulation,[],[f25,f9])).
% 0.20/0.49  fof(f9,plain,(
% 0.20/0.49    k3_subset_1(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,plain,(
% 0.20/0.49    ? [X0,X1] : (? [X2] : (X1 != X2 & k3_subset_1(u1_struct_0(X0),X1) = k3_subset_1(u1_struct_0(X0),X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.49    inference(flattening,[],[f5])).
% 0.20/0.49  fof(f5,plain,(
% 0.20/0.49    ? [X0,X1] : (? [X2] : ((X1 != X2 & k3_subset_1(u1_struct_0(X0),X1) = k3_subset_1(u1_struct_0(X0),X2)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,plain,(
% 0.20/0.49    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (k3_subset_1(u1_struct_0(X0),X1) = k3_subset_1(u1_struct_0(X0),X2) => X1 = X2)))),
% 0.20/0.49    inference(pure_predicate_removal,[],[f3])).
% 0.20/0.49  fof(f3,negated_conjecture,(
% 0.20/0.49    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (k3_subset_1(u1_struct_0(X0),X1) = k3_subset_1(u1_struct_0(X0),X2) => X1 = X2))))),
% 0.20/0.49    inference(negated_conjecture,[],[f2])).
% 0.20/0.49  fof(f2,conjecture,(
% 0.20/0.49    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (k3_subset_1(u1_struct_0(X0),X1) = k3_subset_1(u1_struct_0(X0),X2) => X1 = X2))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_tops_1)).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    sK2 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)) | ~spl3_2),
% 0.20/0.49    inference(resolution,[],[f19,f12])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f18])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    spl3_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f11,f22])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.49    inference(cnf_transformation,[],[f6])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    spl3_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f8,f18])).
% 0.20/0.49  fof(f8,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.49    inference(cnf_transformation,[],[f6])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ~spl3_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f10,f14])).
% 0.20/0.49  fof(f10,plain,(
% 0.20/0.49    sK1 != sK2),
% 0.20/0.49    inference(cnf_transformation,[],[f6])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (28806)------------------------------
% 0.20/0.49  % (28806)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (28806)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (28806)Memory used [KB]: 6140
% 0.20/0.49  % (28806)Time elapsed: 0.074 s
% 0.20/0.49  % (28806)------------------------------
% 0.20/0.49  % (28806)------------------------------
% 0.20/0.49  % (28811)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.50  % (28805)Success in time 0.134 s
%------------------------------------------------------------------------------
