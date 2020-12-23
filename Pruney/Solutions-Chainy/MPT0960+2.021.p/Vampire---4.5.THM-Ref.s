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
% DateTime   : Thu Dec  3 13:00:09 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 103 expanded)
%              Number of leaves         :   16 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :  186 ( 286 expanded)
%              Number of equality atoms :   27 (  52 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f222,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f200,f205,f221])).

fof(f221,plain,(
    spl7_8 ),
    inference(avatar_contradiction_clause,[],[f220])).

fof(f220,plain,
    ( $false
    | spl7_8 ),
    inference(subsumption_resolution,[],[f219,f70])).

fof(f70,plain,(
    ! [X0] : sP2(X0,k1_wellord2(X0)) ),
    inference(subsumption_resolution,[],[f69,f39])).

fof(f39,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f69,plain,(
    ! [X0] :
      ( sP2(X0,k1_wellord2(X0))
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(resolution,[],[f63,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( sP3(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( sP3(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f14,f21,f20,f19,f18])).

fof(f18,plain,(
    ! [X3,X2,X1] :
      ( sP0(X3,X2,X1)
    <=> ( r2_hidden(k4_tarski(X2,X3),X1)
      <=> r1_tarski(X2,X3) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f19,plain,(
    ! [X1,X0] :
      ( sP1(X1,X0)
    <=> ! [X2,X3] :
          ( sP0(X3,X2,X1)
          | ~ r2_hidden(X3,X0)
          | ~ r2_hidden(X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f20,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
    <=> ( sP1(X1,X0)
        & k3_relat_1(X1) = X0 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ( k1_wellord2(X0) = X1
      <=> sP2(X0,X1) )
      | ~ sP3(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

fof(f63,plain,(
    ! [X1] :
      ( ~ sP3(k1_wellord2(X1),X1)
      | sP2(X1,k1_wellord2(X1)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( sP2(X1,X0)
      | k1_wellord2(X1) != X0
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X1) = X0
          | ~ sP2(X1,X0) )
        & ( sP2(X1,X0)
          | k1_wellord2(X1) != X0 ) )
      | ~ sP3(X0,X1) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ( ( k1_wellord2(X0) = X1
          | ~ sP2(X0,X1) )
        & ( sP2(X0,X1)
          | k1_wellord2(X0) != X1 ) )
      | ~ sP3(X1,X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f219,plain,
    ( ~ sP2(sK4,k1_wellord2(sK4))
    | spl7_8 ),
    inference(subsumption_resolution,[],[f217,f39])).

fof(f217,plain,
    ( ~ v1_relat_1(k1_wellord2(sK4))
    | ~ sP2(sK4,k1_wellord2(sK4))
    | spl7_8 ),
    inference(resolution,[],[f199,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),X1)
      | ~ v1_relat_1(X0)
      | ~ sP2(X1,X0) ) ),
    inference(superposition,[],[f82,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ~ sP1(X1,X0)
        | k3_relat_1(X1) != X0 )
      & ( ( sP1(X1,X0)
          & k3_relat_1(X1) = X0 )
        | ~ sP2(X0,X1) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ~ sP1(X1,X0)
        | k3_relat_1(X1) != X0 )
      & ( ( sP1(X1,X0)
          & k3_relat_1(X1) = X0 )
        | ~ sP2(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f82,plain,(
    ! [X2] :
      ( r1_tarski(k1_relat_1(X2),k3_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f41,f40])).

fof(f40,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f199,plain,
    ( ~ r1_tarski(k1_relat_1(k1_wellord2(sK4)),sK4)
    | spl7_8 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl7_8
  <=> r1_tarski(k1_relat_1(k1_wellord2(sK4)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f205,plain,(
    spl7_7 ),
    inference(avatar_contradiction_clause,[],[f204])).

fof(f204,plain,
    ( $false
    | spl7_7 ),
    inference(subsumption_resolution,[],[f203,f70])).

fof(f203,plain,
    ( ~ sP2(sK4,k1_wellord2(sK4))
    | spl7_7 ),
    inference(subsumption_resolution,[],[f201,f39])).

fof(f201,plain,
    ( ~ v1_relat_1(k1_wellord2(sK4))
    | ~ sP2(sK4,k1_wellord2(sK4))
    | spl7_7 ),
    inference(resolution,[],[f195,f142])).

fof(f142,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),X1)
      | ~ v1_relat_1(X0)
      | ~ sP2(X1,X0) ) ),
    inference(resolution,[],[f129,f65])).

fof(f65,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k2_relat_1(X0))
      | r1_tarski(X2,X1)
      | ~ v1_relat_1(X0)
      | ~ sP2(X1,X0) ) ),
    inference(superposition,[],[f81,f44])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k3_relat_1(X0))
      | ~ r1_tarski(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f62,f40])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f195,plain,
    ( ~ r1_tarski(k2_relat_1(k1_wellord2(sK4)),sK4)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl7_7
  <=> r1_tarski(k2_relat_1(k1_wellord2(sK4)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f200,plain,
    ( ~ spl7_7
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f191,f197,f193])).

fof(f191,plain,
    ( ~ r1_tarski(k1_relat_1(k1_wellord2(sK4)),sK4)
    | ~ r1_tarski(k2_relat_1(k1_wellord2(sK4)),sK4) ),
    inference(subsumption_resolution,[],[f189,f39])).

fof(f189,plain,
    ( ~ r1_tarski(k1_relat_1(k1_wellord2(sK4)),sK4)
    | ~ v1_relat_1(k1_wellord2(sK4))
    | ~ r1_tarski(k2_relat_1(k1_wellord2(sK4)),sK4) ),
    inference(resolution,[],[f160,f38])).

fof(f38,plain,(
    ~ r1_tarski(k1_wellord2(sK4),k2_zfmisc_1(sK4,sK4)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ~ r1_tarski(k1_wellord2(sK4),k2_zfmisc_1(sK4,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f11,f23])).

fof(f23,plain,
    ( ? [X0] : ~ r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))
   => ~ r1_tarski(k1_wellord2(sK4),k2_zfmisc_1(sK4,sK4)) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] : ~ r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_wellord2)).

fof(f160,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(k1_relat_1(X0),X2)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),X1) ) ),
    inference(resolution,[],[f61,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f61,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:53:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (12319)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.49  % (12317)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.49  % (12321)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.50  % (12324)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.50  % (12338)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.50  % (12319)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % (12321)Refutation not found, incomplete strategy% (12321)------------------------------
% 0.20/0.50  % (12321)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (12321)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (12321)Memory used [KB]: 10490
% 0.20/0.50  % (12321)Time elapsed: 0.095 s
% 0.20/0.50  % (12321)------------------------------
% 0.20/0.50  % (12321)------------------------------
% 0.20/0.50  % (12320)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.50  % (12320)Refutation not found, incomplete strategy% (12320)------------------------------
% 0.20/0.50  % (12320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (12336)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.50  % (12325)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.50  % (12337)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.51  % (12330)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (12322)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.51  % (12323)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.51  % (12341)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.51  % (12320)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (12320)Memory used [KB]: 6012
% 0.20/0.51  % (12320)Time elapsed: 0.094 s
% 0.20/0.51  % (12320)------------------------------
% 0.20/0.51  % (12320)------------------------------
% 0.20/0.51  % (12327)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.51  % (12340)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.51  % (12339)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.51  % (12316)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (12318)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.51  % (12316)Refutation not found, incomplete strategy% (12316)------------------------------
% 0.20/0.51  % (12316)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (12316)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (12316)Memory used [KB]: 10618
% 0.20/0.51  % (12316)Time elapsed: 0.103 s
% 0.20/0.51  % (12316)------------------------------
% 0.20/0.51  % (12316)------------------------------
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f222,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f200,f205,f221])).
% 0.20/0.52  fof(f221,plain,(
% 0.20/0.52    spl7_8),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f220])).
% 0.20/0.52  fof(f220,plain,(
% 0.20/0.52    $false | spl7_8),
% 0.20/0.52    inference(subsumption_resolution,[],[f219,f70])).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    ( ! [X0] : (sP2(X0,k1_wellord2(X0))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f69,f39])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    ( ! [X0] : (sP2(X0,k1_wellord2(X0)) | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.20/0.52    inference(resolution,[],[f63,f55])).
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    ( ! [X0,X1] : (sP3(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ! [X0,X1] : (sP3(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(definition_folding,[],[f14,f21,f20,f19,f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X3,X2,X1] : (sP0(X3,X2,X1) <=> (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)))),
% 0.20/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X1,X0] : (sP1(X1,X0) <=> ! [X2,X3] : (sP0(X3,X2,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))),
% 0.20/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0,X1] : (sP2(X0,X1) <=> (sP1(X1,X0) & k3_relat_1(X1) = X0))),
% 0.20/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X1,X0] : ((k1_wellord2(X0) = X1 <=> sP2(X0,X1)) | ~sP3(X1,X0))),
% 0.20/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(flattening,[],[f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    ( ! [X1] : (~sP3(k1_wellord2(X1),X1) | sP2(X1,k1_wellord2(X1))) )),
% 0.20/0.52    inference(equality_resolution,[],[f42])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ( ! [X0,X1] : (sP2(X1,X0) | k1_wellord2(X1) != X0 | ~sP3(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X0,X1] : (((k1_wellord2(X1) = X0 | ~sP2(X1,X0)) & (sP2(X1,X0) | k1_wellord2(X1) != X0)) | ~sP3(X0,X1))),
% 0.20/0.52    inference(rectify,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X1,X0] : (((k1_wellord2(X0) = X1 | ~sP2(X0,X1)) & (sP2(X0,X1) | k1_wellord2(X0) != X1)) | ~sP3(X1,X0))),
% 0.20/0.52    inference(nnf_transformation,[],[f21])).
% 0.20/0.52  fof(f219,plain,(
% 0.20/0.52    ~sP2(sK4,k1_wellord2(sK4)) | spl7_8),
% 0.20/0.52    inference(subsumption_resolution,[],[f217,f39])).
% 0.20/0.52  fof(f217,plain,(
% 0.20/0.52    ~v1_relat_1(k1_wellord2(sK4)) | ~sP2(sK4,k1_wellord2(sK4)) | spl7_8),
% 0.20/0.52    inference(resolution,[],[f199,f84])).
% 0.20/0.52  fof(f84,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),X1) | ~v1_relat_1(X0) | ~sP2(X1,X0)) )),
% 0.20/0.52    inference(superposition,[],[f82,f44])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | ~sP2(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ! [X0,X1] : ((sP2(X0,X1) | ~sP1(X1,X0) | k3_relat_1(X1) != X0) & ((sP1(X1,X0) & k3_relat_1(X1) = X0) | ~sP2(X0,X1)))),
% 0.20/0.52    inference(flattening,[],[f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ! [X0,X1] : ((sP2(X0,X1) | (~sP1(X1,X0) | k3_relat_1(X1) != X0)) & ((sP1(X1,X0) & k3_relat_1(X1) = X0) | ~sP2(X0,X1)))),
% 0.20/0.52    inference(nnf_transformation,[],[f20])).
% 0.20/0.52  fof(f82,plain,(
% 0.20/0.52    ( ! [X2] : (r1_tarski(k1_relat_1(X2),k3_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.20/0.52    inference(superposition,[],[f41,f40])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.20/0.52  fof(f199,plain,(
% 0.20/0.52    ~r1_tarski(k1_relat_1(k1_wellord2(sK4)),sK4) | spl7_8),
% 0.20/0.52    inference(avatar_component_clause,[],[f197])).
% 0.20/0.52  fof(f197,plain,(
% 0.20/0.52    spl7_8 <=> r1_tarski(k1_relat_1(k1_wellord2(sK4)),sK4)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.20/0.52  fof(f205,plain,(
% 0.20/0.52    spl7_7),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f204])).
% 0.20/0.52  fof(f204,plain,(
% 0.20/0.52    $false | spl7_7),
% 0.20/0.52    inference(subsumption_resolution,[],[f203,f70])).
% 0.20/0.52  fof(f203,plain,(
% 0.20/0.52    ~sP2(sK4,k1_wellord2(sK4)) | spl7_7),
% 0.20/0.52    inference(subsumption_resolution,[],[f201,f39])).
% 0.20/0.52  fof(f201,plain,(
% 0.20/0.52    ~v1_relat_1(k1_wellord2(sK4)) | ~sP2(sK4,k1_wellord2(sK4)) | spl7_7),
% 0.20/0.52    inference(resolution,[],[f195,f142])).
% 0.20/0.52  fof(f142,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),X1) | ~v1_relat_1(X0) | ~sP2(X1,X0)) )),
% 0.20/0.52    inference(resolution,[],[f129,f65])).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.52    inference(equality_resolution,[],[f57])).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.52    inference(flattening,[],[f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.52    inference(nnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.52  fof(f129,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X2,k2_relat_1(X0)) | r1_tarski(X2,X1) | ~v1_relat_1(X0) | ~sP2(X1,X0)) )),
% 0.20/0.52    inference(superposition,[],[f81,f44])).
% 0.20/0.52  fof(f81,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(X1,k3_relat_1(X0)) | ~r1_tarski(X1,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(superposition,[],[f62,f40])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.20/0.52  fof(f195,plain,(
% 0.20/0.52    ~r1_tarski(k2_relat_1(k1_wellord2(sK4)),sK4) | spl7_7),
% 0.20/0.52    inference(avatar_component_clause,[],[f193])).
% 0.20/0.52  fof(f193,plain,(
% 0.20/0.52    spl7_7 <=> r1_tarski(k2_relat_1(k1_wellord2(sK4)),sK4)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.20/0.52  fof(f200,plain,(
% 0.20/0.52    ~spl7_7 | ~spl7_8),
% 0.20/0.52    inference(avatar_split_clause,[],[f191,f197,f193])).
% 0.20/0.52  fof(f191,plain,(
% 0.20/0.52    ~r1_tarski(k1_relat_1(k1_wellord2(sK4)),sK4) | ~r1_tarski(k2_relat_1(k1_wellord2(sK4)),sK4)),
% 0.20/0.52    inference(subsumption_resolution,[],[f189,f39])).
% 0.20/0.52  fof(f189,plain,(
% 0.20/0.52    ~r1_tarski(k1_relat_1(k1_wellord2(sK4)),sK4) | ~v1_relat_1(k1_wellord2(sK4)) | ~r1_tarski(k2_relat_1(k1_wellord2(sK4)),sK4)),
% 0.20/0.52    inference(resolution,[],[f160,f38])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ~r1_tarski(k1_wellord2(sK4),k2_zfmisc_1(sK4,sK4))),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ~r1_tarski(k1_wellord2(sK4),k2_zfmisc_1(sK4,sK4))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f11,f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ? [X0] : ~r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) => ~r1_tarski(k1_wellord2(sK4),k2_zfmisc_1(sK4,sK4))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f11,plain,(
% 0.20/0.52    ? [X0] : ~r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,negated_conjecture,(
% 0.20/0.52    ~! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 0.20/0.52    inference(negated_conjecture,[],[f9])).
% 0.20/0.52  fof(f9,conjecture,(
% 0.20/0.52    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_wellord2)).
% 0.20/0.52  fof(f160,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_zfmisc_1(X2,X1)) | ~r1_tarski(k1_relat_1(X0),X2) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),X1)) )),
% 0.20/0.52    inference(resolution,[],[f61,f59])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.52    inference(nnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.20/0.52    inference(flattening,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (12319)------------------------------
% 0.20/0.52  % (12319)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (12319)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (12319)Memory used [KB]: 6140
% 0.20/0.52  % (12319)Time elapsed: 0.089 s
% 0.20/0.52  % (12319)------------------------------
% 0.20/0.52  % (12319)------------------------------
% 0.20/0.52  % (12311)Success in time 0.159 s
%------------------------------------------------------------------------------
