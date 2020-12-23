%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:31 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 111 expanded)
%              Number of leaves         :   11 (  29 expanded)
%              Depth                    :   16
%              Number of atoms          :  181 ( 524 expanded)
%              Number of equality atoms :   17 (  73 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f118,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f109,f117])).

fof(f117,plain,(
    spl5_2 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | spl5_2 ),
    inference(resolution,[],[f114,f27])).

fof(f27,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),sK1)
    & k1_xboole_0 != sK1
    & r2_hidden(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_hidden(k1_funct_1(X3,X2),X1)
        & k1_xboole_0 != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ~ r2_hidden(k1_funct_1(sK3,sK2),sK1)
      & k1_xboole_0 != sK1
      & r2_hidden(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_hidden(k1_funct_1(X3,X2),X1)
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_hidden(k1_funct_1(X3,X2),X1)
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => ( r2_hidden(k1_funct_1(X3,X2),X1)
            | k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

fof(f114,plain,
    ( ! [X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | spl5_2 ),
    inference(resolution,[],[f89,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f89,plain,
    ( ~ v5_relat_1(sK3,sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl5_2
  <=> v5_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f109,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f108])).

fof(f108,plain,
    ( $false
    | spl5_1 ),
    inference(resolution,[],[f91,f27])).

fof(f91,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl5_1 ),
    inference(resolution,[],[f85,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f85,plain,
    ( ~ v1_relat_1(sK3)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl5_1
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f90,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f80,f87,f83])).

fof(f80,plain,
    ( ~ v5_relat_1(sK3,sK1)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f79,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f79,plain,(
    ~ r1_tarski(k2_relat_1(sK3),sK1) ),
    inference(subsumption_resolution,[],[f78,f27])).

fof(f78,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f62,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f62,plain,(
    ~ r1_tarski(k2_relset_1(sK0,sK1,sK3),sK1) ),
    inference(resolution,[],[f59,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_funct_1(sK3,sK2),X0)
      | ~ r1_tarski(X0,sK1) ) ),
    inference(resolution,[],[f33,f30])).

fof(f30,plain,(
    ~ r2_hidden(k1_funct_1(sK3,sK2),sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f59,plain,(
    r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3)) ),
    inference(resolution,[],[f58,f28])).

fof(f28,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f58,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK0,sK1,sK3)) ) ),
    inference(subsumption_resolution,[],[f57,f26])).

fof(f26,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f57,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | ~ v1_funct_2(sK3,sK0,sK1)
      | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK0,sK1,sK3)) ) ),
    inference(subsumption_resolution,[],[f56,f29])).

fof(f29,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f19])).

fof(f56,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = sK1
      | ~ v1_funct_2(sK3,sK0,sK1)
      | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK0,sK1,sK3)) ) ),
    inference(resolution,[],[f55,f27])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ r2_hidden(X1,X2)
      | k1_xboole_0 = X0
      | ~ v1_funct_2(sK3,X2,X0)
      | r2_hidden(k1_funct_1(sK3,X1),k2_relset_1(X2,X0,sK3)) ) ),
    inference(resolution,[],[f40,f25])).

fof(f25,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f6])).

% (22499)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:27:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.54  % (22497)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (22496)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.56  % (22496)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % (22495)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.57  % (22512)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.57  % (22504)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.57  % (22504)Refutation not found, incomplete strategy% (22504)------------------------------
% 0.22/0.57  % (22504)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (22504)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (22504)Memory used [KB]: 10618
% 0.22/0.57  % (22504)Time elapsed: 0.145 s
% 0.22/0.57  % (22504)------------------------------
% 0.22/0.57  % (22504)------------------------------
% 0.22/0.57  % (22498)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.43/0.57  % SZS output start Proof for theBenchmark
% 1.43/0.57  fof(f118,plain,(
% 1.43/0.57    $false),
% 1.43/0.57    inference(avatar_sat_refutation,[],[f90,f109,f117])).
% 1.43/0.57  fof(f117,plain,(
% 1.43/0.57    spl5_2),
% 1.43/0.57    inference(avatar_contradiction_clause,[],[f116])).
% 1.43/0.57  fof(f116,plain,(
% 1.43/0.57    $false | spl5_2),
% 1.43/0.57    inference(resolution,[],[f114,f27])).
% 1.43/0.57  fof(f27,plain,(
% 1.43/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.43/0.57    inference(cnf_transformation,[],[f19])).
% 1.43/0.57  fof(f19,plain,(
% 1.43/0.57    ~r2_hidden(k1_funct_1(sK3,sK2),sK1) & k1_xboole_0 != sK1 & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 1.43/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f18])).
% 1.43/0.57  fof(f18,plain,(
% 1.43/0.57    ? [X0,X1,X2,X3] : (~r2_hidden(k1_funct_1(X3,X2),X1) & k1_xboole_0 != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_hidden(k1_funct_1(sK3,sK2),sK1) & k1_xboole_0 != sK1 & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.43/0.57    introduced(choice_axiom,[])).
% 1.43/0.57  fof(f10,plain,(
% 1.43/0.57    ? [X0,X1,X2,X3] : (~r2_hidden(k1_funct_1(X3,X2),X1) & k1_xboole_0 != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.43/0.57    inference(flattening,[],[f9])).
% 1.43/0.57  fof(f9,plain,(
% 1.43/0.57    ? [X0,X1,X2,X3] : (((~r2_hidden(k1_funct_1(X3,X2),X1) & k1_xboole_0 != X1) & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.43/0.57    inference(ennf_transformation,[],[f8])).
% 1.43/0.57  fof(f8,negated_conjecture,(
% 1.43/0.57    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 1.43/0.57    inference(negated_conjecture,[],[f7])).
% 1.43/0.57  fof(f7,conjecture,(
% 1.43/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).
% 1.43/0.57  fof(f114,plain,(
% 1.43/0.57    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))) ) | spl5_2),
% 1.43/0.57    inference(resolution,[],[f89,f39])).
% 1.43/0.57  fof(f39,plain,(
% 1.43/0.57    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.43/0.57    inference(cnf_transformation,[],[f15])).
% 1.43/0.57  fof(f15,plain,(
% 1.43/0.57    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.43/0.57    inference(ennf_transformation,[],[f4])).
% 1.43/0.57  fof(f4,axiom,(
% 1.43/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.43/0.57  fof(f89,plain,(
% 1.43/0.57    ~v5_relat_1(sK3,sK1) | spl5_2),
% 1.43/0.57    inference(avatar_component_clause,[],[f87])).
% 1.43/0.57  fof(f87,plain,(
% 1.43/0.57    spl5_2 <=> v5_relat_1(sK3,sK1)),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.43/0.57  fof(f109,plain,(
% 1.43/0.57    spl5_1),
% 1.43/0.57    inference(avatar_contradiction_clause,[],[f108])).
% 1.43/0.57  fof(f108,plain,(
% 1.43/0.57    $false | spl5_1),
% 1.43/0.57    inference(resolution,[],[f91,f27])).
% 1.43/0.57  fof(f91,plain,(
% 1.43/0.57    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl5_1),
% 1.43/0.57    inference(resolution,[],[f85,f36])).
% 1.43/0.57  fof(f36,plain,(
% 1.43/0.57    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.43/0.57    inference(cnf_transformation,[],[f13])).
% 1.43/0.57  fof(f13,plain,(
% 1.43/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.43/0.57    inference(ennf_transformation,[],[f3])).
% 1.43/0.57  fof(f3,axiom,(
% 1.43/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.43/0.57  fof(f85,plain,(
% 1.43/0.57    ~v1_relat_1(sK3) | spl5_1),
% 1.43/0.57    inference(avatar_component_clause,[],[f83])).
% 1.43/0.57  fof(f83,plain,(
% 1.43/0.57    spl5_1 <=> v1_relat_1(sK3)),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.43/0.57  fof(f90,plain,(
% 1.43/0.57    ~spl5_1 | ~spl5_2),
% 1.43/0.57    inference(avatar_split_clause,[],[f80,f87,f83])).
% 1.43/0.57  fof(f80,plain,(
% 1.43/0.57    ~v5_relat_1(sK3,sK1) | ~v1_relat_1(sK3)),
% 1.43/0.57    inference(resolution,[],[f79,f31])).
% 1.43/0.57  fof(f31,plain,(
% 1.43/0.57    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.43/0.57    inference(cnf_transformation,[],[f20])).
% 1.43/0.57  fof(f20,plain,(
% 1.43/0.57    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.43/0.57    inference(nnf_transformation,[],[f11])).
% 1.43/0.57  fof(f11,plain,(
% 1.43/0.57    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.43/0.57    inference(ennf_transformation,[],[f2])).
% 1.43/0.57  fof(f2,axiom,(
% 1.43/0.57    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.43/0.57  fof(f79,plain,(
% 1.43/0.57    ~r1_tarski(k2_relat_1(sK3),sK1)),
% 1.43/0.57    inference(subsumption_resolution,[],[f78,f27])).
% 1.43/0.57  fof(f78,plain,(
% 1.43/0.57    ~r1_tarski(k2_relat_1(sK3),sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.43/0.57    inference(superposition,[],[f62,f37])).
% 1.43/0.57  fof(f37,plain,(
% 1.43/0.57    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.43/0.57    inference(cnf_transformation,[],[f14])).
% 1.43/0.57  fof(f14,plain,(
% 1.43/0.57    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.43/0.57    inference(ennf_transformation,[],[f5])).
% 1.43/0.57  fof(f5,axiom,(
% 1.43/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.43/0.57  fof(f62,plain,(
% 1.43/0.57    ~r1_tarski(k2_relset_1(sK0,sK1,sK3),sK1)),
% 1.43/0.57    inference(resolution,[],[f59,f41])).
% 1.43/0.57  fof(f41,plain,(
% 1.43/0.57    ( ! [X0] : (~r2_hidden(k1_funct_1(sK3,sK2),X0) | ~r1_tarski(X0,sK1)) )),
% 1.43/0.57    inference(resolution,[],[f33,f30])).
% 1.43/0.57  fof(f30,plain,(
% 1.43/0.57    ~r2_hidden(k1_funct_1(sK3,sK2),sK1)),
% 1.43/0.57    inference(cnf_transformation,[],[f19])).
% 1.43/0.57  fof(f33,plain,(
% 1.43/0.57    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.43/0.57    inference(cnf_transformation,[],[f24])).
% 1.43/0.57  fof(f24,plain,(
% 1.43/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.43/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f23])).
% 1.43/0.57  fof(f23,plain,(
% 1.43/0.57    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.43/0.57    introduced(choice_axiom,[])).
% 1.43/0.57  fof(f22,plain,(
% 1.43/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.43/0.57    inference(rectify,[],[f21])).
% 1.43/0.57  fof(f21,plain,(
% 1.43/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.43/0.57    inference(nnf_transformation,[],[f12])).
% 1.43/0.57  fof(f12,plain,(
% 1.43/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.43/0.57    inference(ennf_transformation,[],[f1])).
% 1.43/0.57  fof(f1,axiom,(
% 1.43/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.43/0.57  fof(f59,plain,(
% 1.43/0.57    r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3))),
% 1.43/0.57    inference(resolution,[],[f58,f28])).
% 1.43/0.57  fof(f28,plain,(
% 1.43/0.57    r2_hidden(sK2,sK0)),
% 1.43/0.57    inference(cnf_transformation,[],[f19])).
% 1.43/0.57  fof(f58,plain,(
% 1.43/0.57    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK0,sK1,sK3))) )),
% 1.43/0.57    inference(subsumption_resolution,[],[f57,f26])).
% 1.43/0.57  fof(f26,plain,(
% 1.43/0.57    v1_funct_2(sK3,sK0,sK1)),
% 1.43/0.57    inference(cnf_transformation,[],[f19])).
% 1.43/0.57  fof(f57,plain,(
% 1.43/0.57    ( ! [X0] : (~r2_hidden(X0,sK0) | ~v1_funct_2(sK3,sK0,sK1) | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK0,sK1,sK3))) )),
% 1.43/0.57    inference(subsumption_resolution,[],[f56,f29])).
% 1.43/0.57  fof(f29,plain,(
% 1.43/0.57    k1_xboole_0 != sK1),
% 1.43/0.57    inference(cnf_transformation,[],[f19])).
% 1.43/0.57  fof(f56,plain,(
% 1.43/0.57    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_xboole_0 = sK1 | ~v1_funct_2(sK3,sK0,sK1) | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK0,sK1,sK3))) )),
% 1.43/0.57    inference(resolution,[],[f55,f27])).
% 1.43/0.57  fof(f55,plain,(
% 1.43/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~r2_hidden(X1,X2) | k1_xboole_0 = X0 | ~v1_funct_2(sK3,X2,X0) | r2_hidden(k1_funct_1(sK3,X1),k2_relset_1(X2,X0,sK3))) )),
% 1.43/0.57    inference(resolution,[],[f40,f25])).
% 1.43/0.57  fof(f25,plain,(
% 1.43/0.57    v1_funct_1(sK3)),
% 1.43/0.57    inference(cnf_transformation,[],[f19])).
% 1.43/0.57  fof(f40,plain,(
% 1.43/0.57    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))) )),
% 1.43/0.57    inference(cnf_transformation,[],[f17])).
% 1.43/0.57  fof(f17,plain,(
% 1.43/0.57    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.43/0.57    inference(flattening,[],[f16])).
% 1.43/0.57  fof(f16,plain,(
% 1.43/0.57    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.43/0.57    inference(ennf_transformation,[],[f6])).
% 1.43/0.57  % (22499)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.43/0.57  fof(f6,axiom,(
% 1.43/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).
% 1.43/0.57  % SZS output end Proof for theBenchmark
% 1.43/0.57  % (22496)------------------------------
% 1.43/0.57  % (22496)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.57  % (22496)Termination reason: Refutation
% 1.43/0.57  
% 1.43/0.57  % (22496)Memory used [KB]: 10874
% 1.43/0.57  % (22496)Time elapsed: 0.133 s
% 1.43/0.57  % (22496)------------------------------
% 1.43/0.57  % (22496)------------------------------
% 1.43/0.57  % (22505)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.43/0.57  % (22492)Success in time 0.207 s
%------------------------------------------------------------------------------
