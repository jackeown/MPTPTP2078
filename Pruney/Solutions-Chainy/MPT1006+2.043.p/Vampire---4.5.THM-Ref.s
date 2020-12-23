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
% DateTime   : Thu Dec  3 13:03:48 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   37 (  46 expanded)
%              Number of leaves         :   10 (  15 expanded)
%              Depth                    :   10
%              Number of atoms          :   83 ( 117 expanded)
%              Number of equality atoms :   13 (  21 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f80,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f70,f79])).

fof(f79,plain,(
    ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f77])).

fof(f77,plain,
    ( $false
    | ~ spl5_3 ),
    inference(resolution,[],[f63,f58])).

fof(f58,plain,(
    r2_hidden(sK3(k8_relset_1(k1_xboole_0,sK0,sK2,sK1)),k8_relset_1(k1_xboole_0,sK0,sK2,sK1)) ),
    inference(resolution,[],[f39,f40])).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | sQ4_eqProxy(k1_xboole_0,X0) ) ),
    inference(equality_proxy_replacement,[],[f29,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( sQ4_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).

fof(f29,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f19])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f39,plain,(
    ~ sQ4_eqProxy(k1_xboole_0,k8_relset_1(k1_xboole_0,sK0,sK2,sK1)) ),
    inference(equality_proxy_replacement,[],[f26,f38])).

fof(f26,plain,(
    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    & v1_funct_2(sK2,k1_xboole_0,sK0)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
   => ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
      & v1_funct_2(sK2,k1_xboole_0,sK0)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_2(X2,k1_xboole_0,X0)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_2(X2,k1_xboole_0,X0)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_2(X2,k1_xboole_0,X0)
          & v1_funct_1(X2) )
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
     => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).

fof(f63,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k8_relset_1(k1_xboole_0,sK0,sK2,X1))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl5_3
  <=> ! [X1,X0] : ~ r2_hidden(X0,k8_relset_1(k1_xboole_0,sK0,sK2,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f70,plain,(
    spl5_4 ),
    inference(avatar_contradiction_clause,[],[f69])).

fof(f69,plain,
    ( $false
    | spl5_4 ),
    inference(resolution,[],[f67,f27])).

fof(f27,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f67,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl5_4
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f68,plain,
    ( spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f59,f65,f62])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(X0,k8_relset_1(k1_xboole_0,sK0,sK2,X1)) ) ),
    inference(resolution,[],[f45,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f45,plain,(
    ! [X0] : m1_subset_1(k8_relset_1(k1_xboole_0,sK0,sK2,X0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[],[f25,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).

fof(f25,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:18:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (16305)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.47  % (16305)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f80,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f68,f70,f79])).
% 0.22/0.47  fof(f79,plain,(
% 0.22/0.47    ~spl5_3),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f77])).
% 0.22/0.47  fof(f77,plain,(
% 0.22/0.47    $false | ~spl5_3),
% 0.22/0.47    inference(resolution,[],[f63,f58])).
% 0.22/0.47  fof(f58,plain,(
% 0.22/0.47    r2_hidden(sK3(k8_relset_1(k1_xboole_0,sK0,sK2,sK1)),k8_relset_1(k1_xboole_0,sK0,sK2,sK1))),
% 0.22/0.47    inference(resolution,[],[f39,f40])).
% 0.22/0.47  fof(f40,plain,(
% 0.22/0.47    ( ! [X0] : (r2_hidden(sK3(X0),X0) | sQ4_eqProxy(k1_xboole_0,X0)) )),
% 0.22/0.47    inference(equality_proxy_replacement,[],[f29,f38])).
% 0.22/0.47  fof(f38,plain,(
% 0.22/0.47    ! [X1,X0] : (sQ4_eqProxy(X0,X1) <=> X0 = X1)),
% 0.22/0.47    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f20])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f19])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.22/0.47    inference(ennf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.22/0.47  fof(f39,plain,(
% 0.22/0.47    ~sQ4_eqProxy(k1_xboole_0,k8_relset_1(k1_xboole_0,sK0,sK2,sK1))),
% 0.22/0.47    inference(equality_proxy_replacement,[],[f26,f38])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f18])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) & v1_funct_2(sK2,k1_xboole_0,sK0) & v1_funct_1(sK2)),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => (k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) & v1_funct_2(sK2,k1_xboole_0,sK0) & v1_funct_1(sK2))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2))),
% 0.22/0.47    inference(flattening,[],[f10])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)))),
% 0.22/0.47    inference(ennf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,negated_conjecture,(
% 0.22/0.47    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.22/0.47    inference(negated_conjecture,[],[f8])).
% 0.22/0.47  fof(f8,conjecture,(
% 0.22/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).
% 0.22/0.47  fof(f63,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r2_hidden(X0,k8_relset_1(k1_xboole_0,sK0,sK2,X1))) ) | ~spl5_3),
% 0.22/0.47    inference(avatar_component_clause,[],[f62])).
% 0.22/0.47  fof(f62,plain,(
% 0.22/0.47    spl5_3 <=> ! [X1,X0] : ~r2_hidden(X0,k8_relset_1(k1_xboole_0,sK0,sK2,X1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.47  fof(f70,plain,(
% 0.22/0.47    spl5_4),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f69])).
% 0.22/0.47  fof(f69,plain,(
% 0.22/0.47    $false | spl5_4),
% 0.22/0.47    inference(resolution,[],[f67,f27])).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    v1_xboole_0(k1_xboole_0)),
% 0.22/0.47    inference(cnf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    v1_xboole_0(k1_xboole_0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.47  fof(f67,plain,(
% 0.22/0.47    ~v1_xboole_0(k1_xboole_0) | spl5_4),
% 0.22/0.47    inference(avatar_component_clause,[],[f65])).
% 0.22/0.47  fof(f65,plain,(
% 0.22/0.47    spl5_4 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.47  fof(f68,plain,(
% 0.22/0.47    spl5_3 | ~spl5_4),
% 0.22/0.47    inference(avatar_split_clause,[],[f59,f65,f62])).
% 0.22/0.47  fof(f59,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(X0,k8_relset_1(k1_xboole_0,sK0,sK2,X1))) )),
% 0.22/0.47    inference(resolution,[],[f45,f34])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    ( ! [X0] : (m1_subset_1(k8_relset_1(k1_xboole_0,sK0,sK2,X0),k1_zfmisc_1(k1_xboole_0))) )),
% 0.22/0.48    inference(resolution,[],[f25,f35])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (16305)------------------------------
% 0.22/0.48  % (16305)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (16305)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (16305)Memory used [KB]: 6140
% 0.22/0.48  % (16305)Time elapsed: 0.042 s
% 0.22/0.48  % (16305)------------------------------
% 0.22/0.48  % (16305)------------------------------
% 0.22/0.48  % (16292)Success in time 0.116 s
%------------------------------------------------------------------------------
