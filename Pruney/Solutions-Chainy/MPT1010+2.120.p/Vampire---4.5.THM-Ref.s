%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:08 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 111 expanded)
%              Number of leaves         :   14 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :  141 ( 260 expanded)
%              Number of equality atoms :   46 (  93 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f119,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f80,f82,f104,f118])).

% (12282)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f118,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f105])).

fof(f105,plain,
    ( $false
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f50,f66,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ) ),
    inference(superposition,[],[f43,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f43,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
    inference(definition_unfolding,[],[f23,f40])).

fof(f40,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f22,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f24,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f29,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f24,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f22,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f66,plain,
    ( k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl5_1
  <=> k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f50,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f104,plain,(
    ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f99])).

fof(f99,plain,
    ( $false
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f20,f21,f84])).

fof(f84,plain,
    ( ! [X0] :
        ( sK1 = k1_funct_1(sK3,X0)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl5_2 ),
    inference(duplicate_literal_removal,[],[f83])).

fof(f83,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | sK1 = k1_funct_1(sK3,X0)
        | sK1 = k1_funct_1(sK3,X0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f69,f56])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X1))
      | X1 = X3
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k3_enumset1(X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f33,f39])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f69,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK3,X0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))
        | ~ r2_hidden(X0,sK0) )
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl5_2
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k1_funct_1(sK3,X0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f21,plain,(
    sK1 != k1_funct_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

fof(f20,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f82,plain,(
    spl5_4 ),
    inference(avatar_contradiction_clause,[],[f81])).

fof(f81,plain,
    ( $false
    | spl5_4 ),
    inference(subsumption_resolution,[],[f42,f77])).

fof(f77,plain,
    ( ~ v1_funct_2(sK3,sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl5_4
  <=> v1_funct_2(sK3,sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f42,plain,(
    v1_funct_2(sK3,sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f18,f40])).

fof(f18,plain,(
    v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f80,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f79])).

fof(f79,plain,
    ( $false
    | spl5_3 ),
    inference(subsumption_resolution,[],[f17,f73])).

fof(f73,plain,
    ( ~ v1_funct_1(sK3)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl5_3
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f17,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f13])).

fof(f78,plain,
    ( spl5_1
    | spl5_2
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f62,f75,f71,f68,f64])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK3,sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
      | ~ v1_funct_1(sK3)
      | ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1)
      | r2_hidden(k1_funct_1(sK3,X0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ) ),
    inference(resolution,[],[f37,f41])).

fof(f41,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) ),
    inference(definition_unfolding,[],[f19,f40])).

fof(f19,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | r2_hidden(k1_funct_1(X3,X2),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:57:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (12289)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.50  % (12281)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (12289)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f119,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f78,f80,f82,f104,f118])).
% 0.22/0.52  % (12282)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  fof(f118,plain,(
% 0.22/0.52    ~spl5_1),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f105])).
% 0.22/0.52  fof(f105,plain,(
% 0.22/0.52    $false | ~spl5_1),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f50,f66,f58])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_xboole_0 != X1 | ~r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)) )),
% 0.22/0.52    inference(superposition,[],[f43,f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)) )),
% 0.22/0.52    inference(definition_unfolding,[],[f23,f40])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.22/0.52    inference(definition_unfolding,[],[f22,f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.22/0.52    inference(definition_unfolding,[],[f24,f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.22/0.52    inference(definition_unfolding,[],[f29,f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) | ~spl5_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f64])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    spl5_1 <=> k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.52    inference(equality_resolution,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.52  fof(f104,plain,(
% 0.22/0.52    ~spl5_2),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f99])).
% 0.22/0.52  fof(f99,plain,(
% 0.22/0.52    $false | ~spl5_2),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f20,f21,f84])).
% 0.22/0.52  fof(f84,plain,(
% 0.22/0.52    ( ! [X0] : (sK1 = k1_funct_1(sK3,X0) | ~r2_hidden(X0,sK0)) ) | ~spl5_2),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f83])).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(X0,sK0) | sK1 = k1_funct_1(sK3,X0) | sK1 = k1_funct_1(sK3,X0)) ) | ~spl5_2),
% 0.22/0.52    inference(resolution,[],[f69,f56])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X1)) | X1 = X3 | X0 = X3) )),
% 0.22/0.52    inference(equality_resolution,[],[f46])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k3_enumset1(X0,X0,X0,X0,X1) != X2) )),
% 0.22/0.52    inference(definition_unfolding,[],[f33,f39])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 0.22/0.52  fof(f69,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | ~r2_hidden(X0,sK0)) ) | ~spl5_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f68])).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    spl5_2 <=> ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK3,X0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    sK1 != k1_funct_1(sK3,sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 0.22/0.52    inference(flattening,[],[f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 0.22/0.52    inference(ennf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 0.22/0.52    inference(negated_conjecture,[],[f10])).
% 0.22/0.52  fof(f10,conjecture,(
% 0.22/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    r2_hidden(sK2,sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f82,plain,(
% 0.22/0.52    spl5_4),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f81])).
% 0.22/0.52  fof(f81,plain,(
% 0.22/0.52    $false | spl5_4),
% 0.22/0.52    inference(subsumption_resolution,[],[f42,f77])).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    ~v1_funct_2(sK3,sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | spl5_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f75])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    spl5_4 <=> v1_funct_2(sK3,sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    v1_funct_2(sK3,sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 0.22/0.52    inference(definition_unfolding,[],[f18,f40])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f80,plain,(
% 0.22/0.52    spl5_3),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f79])).
% 0.22/0.52  fof(f79,plain,(
% 0.22/0.52    $false | spl5_3),
% 0.22/0.52    inference(subsumption_resolution,[],[f17,f73])).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    ~v1_funct_1(sK3) | spl5_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f71])).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    spl5_3 <=> v1_funct_1(sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    v1_funct_1(sK3)),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    spl5_1 | spl5_2 | ~spl5_3 | ~spl5_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f62,f75,f71,f68,f64])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_funct_2(sK3,sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | ~v1_funct_1(sK3) | ~r2_hidden(X0,sK0) | k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) | r2_hidden(k1_funct_1(sK3,X0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) )),
% 0.22/0.52    inference(resolution,[],[f37,f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))))),
% 0.22/0.52    inference(definition_unfolding,[],[f19,f40])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | r2_hidden(k1_funct_1(X3,X2),X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.22/0.52    inference(flattening,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (12289)------------------------------
% 0.22/0.52  % (12289)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (12289)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (12289)Memory used [KB]: 6268
% 0.22/0.52  % (12289)Time elapsed: 0.084 s
% 0.22/0.52  % (12289)------------------------------
% 0.22/0.52  % (12289)------------------------------
% 0.22/0.52  % (12277)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (12275)Success in time 0.161 s
%------------------------------------------------------------------------------
