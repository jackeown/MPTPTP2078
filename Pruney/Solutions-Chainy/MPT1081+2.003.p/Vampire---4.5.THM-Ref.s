%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   44 (  70 expanded)
%              Number of leaves         :   11 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :  114 ( 196 expanded)
%              Number of equality atoms :   11 (  13 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f99,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f39,f44,f49,f67,f71,f98])).

fof(f98,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_6
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f97,f60,f46,f64,f41,f36,f31])).

fof(f31,plain,
    ( spl5_1
  <=> m1_funct_2(k1_tarski(sK2),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f36,plain,
    ( spl5_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f41,plain,
    ( spl5_3
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f64,plain,
    ( spl5_6
  <=> v1_xboole_0(k1_tarski(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f46,plain,
    ( spl5_4
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f60,plain,
    ( spl5_5
  <=> sK2 = sK4(sK0,sK1,k1_tarski(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f97,plain,
    ( ~ v1_funct_1(sK2)
    | v1_xboole_0(k1_tarski(sK2))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | m1_funct_2(k1_tarski(sK2),sK0,sK1)
    | ~ spl5_5 ),
    inference(superposition,[],[f22,f62])).

fof(f62,plain,
    ( sK2 = sK4(sK0,sK1,k1_tarski(sK2))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f60])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(sK4(X0,X1,X2))
      | v1_xboole_0(X2)
      | ~ v1_funct_2(sK4(X0,X1,X2),X0,X1)
      | ~ m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( m1_funct_2(X2,X0,X1)
      <=> ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
            | ~ m1_subset_1(X3,X2) ) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ( m1_funct_2(X2,X0,X1)
      <=> ! [X3] :
            ( m1_subset_1(X3,X2)
           => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_2)).

fof(f71,plain,(
    ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f68])).

fof(f68,plain,
    ( $false
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f16,f66])).

fof(f66,plain,
    ( v1_xboole_0(k1_tarski(sK2))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f64])).

fof(f16,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f67,plain,
    ( spl5_5
    | spl5_6
    | spl5_1 ),
    inference(avatar_split_clause,[],[f58,f31,f64,f60])).

fof(f58,plain,
    ( v1_xboole_0(k1_tarski(sK2))
    | sK2 = sK4(sK0,sK1,k1_tarski(sK2))
    | spl5_1 ),
    inference(resolution,[],[f53,f33])).

fof(f33,plain,
    ( ~ m1_funct_2(k1_tarski(sK2),sK0,sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_funct_2(k1_tarski(X0),X1,X2)
      | v1_xboole_0(k1_tarski(X0))
      | sK4(X1,X2,k1_tarski(X0)) = X0 ) ),
    inference(resolution,[],[f26,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_tarski(X1))
      | X0 = X1 ) ),
    inference(resolution,[],[f51,f16])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_tarski(X0))
      | ~ m1_subset_1(X1,k1_tarski(X0))
      | X0 = X1 ) ),
    inference(resolution,[],[f17,f27])).

fof(f27,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),X2)
      | v1_xboole_0(X2)
      | m1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f49,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f12,f46])).

fof(f12,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ m1_funct_2(k1_tarski(X2),X0,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ m1_funct_2(k1_tarski(X2),X0,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => m1_funct_2(k1_tarski(X2),X0,X1) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => m1_funct_2(k1_tarski(X2),X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t198_funct_2)).

fof(f44,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f13,f41])).

fof(f13,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f39,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f14,f36])).

fof(f14,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f8])).

fof(f34,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f15,f31])).

fof(f15,plain,(
    ~ m1_funct_2(k1_tarski(sK2),sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:28:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.54  % (19990)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.54  % (19995)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.54  % (20005)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.54  % (19990)Refutation not found, incomplete strategy% (19990)------------------------------
% 0.21/0.54  % (19990)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (19998)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.55  % (19994)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.55  % (19990)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (19990)Memory used [KB]: 10490
% 0.21/0.55  % (19990)Time elapsed: 0.129 s
% 0.21/0.55  % (19990)------------------------------
% 0.21/0.55  % (19990)------------------------------
% 0.21/0.56  % (19996)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.56  % (20005)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f99,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(avatar_sat_refutation,[],[f34,f39,f44,f49,f67,f71,f98])).
% 0.21/0.56  fof(f98,plain,(
% 0.21/0.56    spl5_1 | ~spl5_2 | ~spl5_3 | spl5_6 | ~spl5_4 | ~spl5_5),
% 0.21/0.56    inference(avatar_split_clause,[],[f97,f60,f46,f64,f41,f36,f31])).
% 0.21/0.56  fof(f31,plain,(
% 0.21/0.56    spl5_1 <=> m1_funct_2(k1_tarski(sK2),sK0,sK1)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.56  fof(f36,plain,(
% 0.21/0.56    spl5_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.56  fof(f41,plain,(
% 0.21/0.56    spl5_3 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.56  fof(f64,plain,(
% 0.21/0.56    spl5_6 <=> v1_xboole_0(k1_tarski(sK2))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.56  fof(f46,plain,(
% 0.21/0.56    spl5_4 <=> v1_funct_1(sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.56  fof(f60,plain,(
% 0.21/0.56    spl5_5 <=> sK2 = sK4(sK0,sK1,k1_tarski(sK2))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.56  fof(f97,plain,(
% 0.21/0.56    ~v1_funct_1(sK2) | v1_xboole_0(k1_tarski(sK2)) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | m1_funct_2(k1_tarski(sK2),sK0,sK1) | ~spl5_5),
% 0.21/0.56    inference(superposition,[],[f22,f62])).
% 0.21/0.56  fof(f62,plain,(
% 0.21/0.56    sK2 = sK4(sK0,sK1,k1_tarski(sK2)) | ~spl5_5),
% 0.21/0.56    inference(avatar_component_clause,[],[f60])).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~v1_funct_1(sK4(X0,X1,X2)) | v1_xboole_0(X2) | ~v1_funct_2(sK4(X0,X1,X2),X0,X1) | ~m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_funct_2(X2,X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f11])).
% 0.21/0.56  fof(f11,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((m1_funct_2(X2,X0,X1) <=> ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~m1_subset_1(X3,X2))) | v1_xboole_0(X2))),
% 0.21/0.56    inference(ennf_transformation,[],[f4])).
% 0.21/0.56  fof(f4,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (~v1_xboole_0(X2) => (m1_funct_2(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,X2) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_2)).
% 0.21/0.56  fof(f71,plain,(
% 0.21/0.56    ~spl5_6),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f68])).
% 0.21/0.56  fof(f68,plain,(
% 0.21/0.56    $false | ~spl5_6),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f16,f66])).
% 0.21/0.56  fof(f66,plain,(
% 0.21/0.56    v1_xboole_0(k1_tarski(sK2)) | ~spl5_6),
% 0.21/0.56    inference(avatar_component_clause,[],[f64])).
% 0.21/0.56  fof(f16,plain,(
% 0.21/0.56    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f2])).
% 0.21/0.56  fof(f2,axiom,(
% 0.21/0.56    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).
% 0.21/0.56  fof(f67,plain,(
% 0.21/0.56    spl5_5 | spl5_6 | spl5_1),
% 0.21/0.56    inference(avatar_split_clause,[],[f58,f31,f64,f60])).
% 0.21/0.56  fof(f58,plain,(
% 0.21/0.56    v1_xboole_0(k1_tarski(sK2)) | sK2 = sK4(sK0,sK1,k1_tarski(sK2)) | spl5_1),
% 0.21/0.56    inference(resolution,[],[f53,f33])).
% 0.21/0.56  fof(f33,plain,(
% 0.21/0.56    ~m1_funct_2(k1_tarski(sK2),sK0,sK1) | spl5_1),
% 0.21/0.56    inference(avatar_component_clause,[],[f31])).
% 0.21/0.56  fof(f53,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (m1_funct_2(k1_tarski(X0),X1,X2) | v1_xboole_0(k1_tarski(X0)) | sK4(X1,X2,k1_tarski(X0)) = X0) )),
% 0.21/0.56    inference(resolution,[],[f26,f52])).
% 0.21/0.56  fof(f52,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_tarski(X1)) | X0 = X1) )),
% 0.21/0.56    inference(resolution,[],[f51,f16])).
% 0.21/0.56  fof(f51,plain,(
% 0.21/0.56    ( ! [X0,X1] : (v1_xboole_0(k1_tarski(X0)) | ~m1_subset_1(X1,k1_tarski(X0)) | X0 = X1) )),
% 0.21/0.56    inference(resolution,[],[f17,f27])).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    ( ! [X2,X0] : (~r2_hidden(X2,k1_tarski(X0)) | X0 = X2) )),
% 0.21/0.56    inference(equality_resolution,[],[f19])).
% 0.21/0.56  fof(f19,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.21/0.56  fof(f17,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f10])).
% 0.21/0.56  fof(f10,plain,(
% 0.21/0.56    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.56    inference(flattening,[],[f9])).
% 0.21/0.56  fof(f9,plain,(
% 0.21/0.56    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (m1_subset_1(sK4(X0,X1,X2),X2) | v1_xboole_0(X2) | m1_funct_2(X2,X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f11])).
% 0.21/0.56  fof(f49,plain,(
% 0.21/0.56    spl5_4),
% 0.21/0.56    inference(avatar_split_clause,[],[f12,f46])).
% 0.21/0.56  fof(f12,plain,(
% 0.21/0.56    v1_funct_1(sK2)),
% 0.21/0.56    inference(cnf_transformation,[],[f8])).
% 0.21/0.56  fof(f8,plain,(
% 0.21/0.56    ? [X0,X1,X2] : (~m1_funct_2(k1_tarski(X2),X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.56    inference(flattening,[],[f7])).
% 0.21/0.56  fof(f7,plain,(
% 0.21/0.56    ? [X0,X1,X2] : (~m1_funct_2(k1_tarski(X2),X0,X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.56    inference(ennf_transformation,[],[f6])).
% 0.21/0.56  fof(f6,negated_conjecture,(
% 0.21/0.56    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => m1_funct_2(k1_tarski(X2),X0,X1))),
% 0.21/0.56    inference(negated_conjecture,[],[f5])).
% 0.21/0.56  fof(f5,conjecture,(
% 0.21/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => m1_funct_2(k1_tarski(X2),X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t198_funct_2)).
% 0.21/0.56  fof(f44,plain,(
% 0.21/0.56    spl5_3),
% 0.21/0.56    inference(avatar_split_clause,[],[f13,f41])).
% 0.21/0.56  fof(f13,plain,(
% 0.21/0.56    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.56    inference(cnf_transformation,[],[f8])).
% 0.21/0.56  fof(f39,plain,(
% 0.21/0.56    spl5_2),
% 0.21/0.56    inference(avatar_split_clause,[],[f14,f36])).
% 0.21/0.56  fof(f14,plain,(
% 0.21/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.56    inference(cnf_transformation,[],[f8])).
% 0.21/0.56  fof(f34,plain,(
% 0.21/0.56    ~spl5_1),
% 0.21/0.56    inference(avatar_split_clause,[],[f15,f31])).
% 0.21/0.56  fof(f15,plain,(
% 0.21/0.56    ~m1_funct_2(k1_tarski(sK2),sK0,sK1)),
% 0.21/0.56    inference(cnf_transformation,[],[f8])).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (20005)------------------------------
% 0.21/0.56  % (20005)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (20005)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (20005)Memory used [KB]: 6140
% 0.21/0.56  % (20005)Time elapsed: 0.144 s
% 0.21/0.56  % (20005)------------------------------
% 0.21/0.56  % (20005)------------------------------
% 0.21/0.56  % (20013)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.56  % (20014)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.56  % (19984)Success in time 0.198 s
%------------------------------------------------------------------------------
