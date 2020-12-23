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
% DateTime   : Thu Dec  3 13:04:31 EST 2020

% Result     : Theorem 1.83s
% Output     : Refutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 362 expanded)
%              Number of leaves         :   20 ( 107 expanded)
%              Depth                    :   17
%              Number of atoms          :  349 ( 986 expanded)
%              Number of equality atoms :  154 ( 437 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1432,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f945,f1122,f1431])).

fof(f1431,plain,(
    ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f1430])).

fof(f1430,plain,
    ( $false
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f1429,f110])).

fof(f110,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f66,f82])).

fof(f82,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f43,f80])).

fof(f80,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f48,f79])).

% (23100)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% (23093)Refutation not found, incomplete strategy% (23093)------------------------------
% (23093)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23105)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% (23093)Termination reason: Refutation not found, incomplete strategy

% (23093)Memory used [KB]: 1791
% (23093)Time elapsed: 0.184 s
% (23093)------------------------------
% (23093)------------------------------
% (23096)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% (23100)Refutation not found, incomplete strategy% (23100)------------------------------
% (23100)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23100)Termination reason: Refutation not found, incomplete strategy

% (23100)Memory used [KB]: 10746
% (23100)Time elapsed: 0.176 s
% (23100)------------------------------
% (23100)------------------------------
% (23105)Refutation not found, incomplete strategy% (23105)------------------------------
% (23105)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23105)Termination reason: Refutation not found, incomplete strategy

% (23105)Memory used [KB]: 1663
% (23105)Time elapsed: 0.190 s
% (23105)------------------------------
% (23105)------------------------------
% (23104)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% (23104)Refutation not found, incomplete strategy% (23104)------------------------------
% (23104)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23104)Termination reason: Refutation not found, incomplete strategy

% (23104)Memory used [KB]: 10746
% (23104)Time elapsed: 0.190 s
% (23104)------------------------------
% (23104)------------------------------
% (23088)Refutation not found, incomplete strategy% (23088)------------------------------
% (23088)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23088)Termination reason: Refutation not found, incomplete strategy

% (23088)Memory used [KB]: 10746
% (23088)Time elapsed: 0.192 s
% (23088)------------------------------
% (23088)------------------------------
% (23092)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
fof(f79,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f52,f65])).

% (23102)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
fof(f65,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f52,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

% (23092)Refutation not found, incomplete strategy% (23092)------------------------------
% (23092)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23092)Termination reason: Refutation not found, incomplete strategy

% (23092)Memory used [KB]: 10618
% (23092)Time elapsed: 0.147 s
% (23092)------------------------------
% (23092)------------------------------
fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f48,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f43,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK3,k1_tarski(sK0),sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f31])).

fof(f31,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_2(sK3,k1_tarski(sK0),sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f1429,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl4_6 ),
    inference(resolution,[],[f1398,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

fof(f1398,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ spl4_6 ),
    inference(backward_demodulation,[],[f267,f1203])).

fof(f1203,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f1202,f94])).

fof(f94,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1202,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3))
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f1201,f944])).

fof(f944,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f942])).

fof(f942,plain,
    ( spl4_6
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f1201,plain,
    ( ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k1_relat_1(sK3))
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f1200,f110])).

fof(f1200,plain,
    ( ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k1_relat_1(sK3))
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f1194,f41])).

fof(f41,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f1194,plain,
    ( ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k1_relat_1(sK3))
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_6 ),
    inference(resolution,[],[f1147,f340])).

fof(f340,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),k2_enumset1(X0,X0,X0,X0))
      | ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),k1_relat_1(X1))
      | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(extensionality_resolution,[],[f59,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0)
      | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f56,f80,f80])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

% (23102)Refutation not found, incomplete strategy% (23102)------------------------------
% (23102)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23102)Termination reason: Refutation not found, incomplete strategy

% (23102)Memory used [KB]: 6396
% (23102)Time elapsed: 0.193 s
% (23102)------------------------------
% (23102)------------------------------
fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f1147,plain,
    ( ! [X3] : r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,X3))
    | ~ spl4_6 ),
    inference(superposition,[],[f101,f944])).

fof(f101,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X3,k2_enumset1(X0,X0,X1,X2))
      | k2_enumset1(X0,X0,X0,X1) != X3 ) ),
    inference(definition_unfolding,[],[f75,f65,f79])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
      | k2_tarski(X0,X1) != X3 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
        | ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) )
      & ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
        | ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) )
      & ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3 ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ~ ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_zfmisc_1)).

fof(f267,plain,(
    ~ r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(forward_demodulation,[],[f81,f253])).

fof(f253,plain,(
    ! [X6] : k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X6) = k9_relat_1(sK3,X6) ),
    inference(resolution,[],[f69,f82])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f81,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f45,f80,f80])).

fof(f45,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f1122,plain,(
    ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f1121])).

fof(f1121,plain,
    ( $false
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f1120,f46])).

fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f1120,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)))
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f1112,f47])).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

fof(f1112,plain,
    ( ~ r1_tarski(k9_relat_1(k1_xboole_0,sK2),k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)))
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f267,f1095])).

fof(f1095,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_5 ),
    inference(resolution,[],[f986,f122])).

fof(f122,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f59,f46])).

fof(f986,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f985,f97])).

fof(f97,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f985,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3)))
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f984,f41])).

fof(f984,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3)))
    | ~ v1_funct_1(sK3)
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f957,f110])).

fof(f957,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3)))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ spl4_5 ),
    inference(superposition,[],[f233,f940])).

fof(f940,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f938])).

fof(f938,plain,
    ( spl4_5
  <=> k1_xboole_0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f233,plain,(
    ! [X3] :
      ( r1_tarski(X3,k2_zfmisc_1(k1_relat_1(X3),k2_relat_1(X3)))
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X3) ) ),
    inference(resolution,[],[f51,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f51,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f945,plain,
    ( spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f936,f942,f938])).

fof(f936,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f929,f110])).

fof(f929,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(duplicate_literal_removal,[],[f928])).

fof(f928,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f364,f142])).

fof(f142,plain,(
    v4_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f67,f82])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f364,plain,(
    ! [X26,X24,X27,X25] :
      ( ~ v4_relat_1(X26,k2_enumset1(X24,X24,X27,X25))
      | k1_relat_1(X26) = k2_enumset1(X27,X27,X27,X25)
      | k1_relat_1(X26) = k2_enumset1(X24,X24,X24,X27)
      | k1_relat_1(X26) = k2_enumset1(X25,X25,X25,X25)
      | k1_relat_1(X26) = k2_enumset1(X27,X27,X27,X27)
      | k1_relat_1(X26) = k2_enumset1(X24,X24,X24,X24)
      | k1_xboole_0 = k1_relat_1(X26)
      | k1_relat_1(X26) = k2_enumset1(X24,X24,X27,X25)
      | k2_enumset1(X24,X24,X24,X25) = k1_relat_1(X26)
      | ~ v1_relat_1(X26) ) ),
    inference(resolution,[],[f93,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X3,k2_enumset1(X0,X0,X1,X2))
      | k2_enumset1(X0,X0,X0,X2) = X3
      | k2_enumset1(X1,X1,X1,X2) = X3
      | k2_enumset1(X0,X0,X0,X1) = X3
      | k2_enumset1(X2,X2,X2,X2) = X3
      | k2_enumset1(X1,X1,X1,X1) = X3
      | k2_enumset1(X0,X0,X0,X0) = X3
      | k1_xboole_0 = X3
      | k2_enumset1(X0,X0,X1,X2) = X3 ) ),
    inference(definition_unfolding,[],[f70,f65,f79,f79,f79,f80,f80,f80,f65])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | k2_tarski(X0,X2) = X3
      | k2_tarski(X1,X2) = X3
      | k2_tarski(X0,X1) = X3
      | k1_tarski(X2) = X3
      | k1_tarski(X1) = X3
      | k1_tarski(X0) = X3
      | k1_xboole_0 = X3
      | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:50:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.54  % (23082)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (23078)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.57  % (23098)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.57  % (23090)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.55/0.58  % (23081)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.55/0.58  % (23094)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.55/0.58  % (23090)Refutation not found, incomplete strategy% (23090)------------------------------
% 1.55/0.58  % (23090)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.58  % (23086)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.55/0.58  % (23094)Refutation not found, incomplete strategy% (23094)------------------------------
% 1.55/0.58  % (23094)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.58  % (23094)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.58  
% 1.55/0.58  % (23094)Memory used [KB]: 1791
% 1.55/0.58  % (23094)Time elapsed: 0.149 s
% 1.55/0.58  % (23094)------------------------------
% 1.55/0.58  % (23094)------------------------------
% 1.55/0.59  % (23090)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.59  
% 1.55/0.59  % (23090)Memory used [KB]: 1791
% 1.55/0.59  % (23090)Time elapsed: 0.138 s
% 1.55/0.59  % (23090)------------------------------
% 1.55/0.59  % (23090)------------------------------
% 1.55/0.59  % (23086)Refutation not found, incomplete strategy% (23086)------------------------------
% 1.55/0.59  % (23086)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.59  % (23091)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.55/0.59  % (23086)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.59  
% 1.55/0.59  % (23086)Memory used [KB]: 10746
% 1.55/0.59  % (23086)Time elapsed: 0.150 s
% 1.55/0.59  % (23086)------------------------------
% 1.55/0.59  % (23086)------------------------------
% 1.83/0.59  % (23079)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.83/0.59  % (23099)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.83/0.59  % (23077)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.83/0.60  % (23076)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.83/0.60  % (23085)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.83/0.60  % (23097)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.83/0.60  % (23077)Refutation not found, incomplete strategy% (23077)------------------------------
% 1.83/0.60  % (23077)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.83/0.60  % (23077)Termination reason: Refutation not found, incomplete strategy
% 1.83/0.60  
% 1.83/0.60  % (23077)Memory used [KB]: 1791
% 1.83/0.60  % (23077)Time elapsed: 0.160 s
% 1.83/0.60  % (23077)------------------------------
% 1.83/0.60  % (23077)------------------------------
% 1.83/0.60  % (23103)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.83/0.61  % (23088)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.83/0.61  % (23093)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.83/0.61  % (23103)Refutation not found, incomplete strategy% (23103)------------------------------
% 1.83/0.61  % (23103)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.83/0.61  % (23103)Termination reason: Refutation not found, incomplete strategy
% 1.83/0.61  
% 1.83/0.61  % (23103)Memory used [KB]: 6268
% 1.83/0.61  % (23103)Time elapsed: 0.171 s
% 1.83/0.61  % (23103)------------------------------
% 1.83/0.61  % (23103)------------------------------
% 1.83/0.61  % (23083)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.83/0.61  % (23101)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.83/0.61  % (23080)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.83/0.61  % (23084)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.83/0.61  % (23087)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.83/0.61  % (23095)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.83/0.61  % (23089)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.83/0.62  % (23082)Refutation found. Thanks to Tanya!
% 1.83/0.62  % SZS status Theorem for theBenchmark
% 1.83/0.62  % SZS output start Proof for theBenchmark
% 1.83/0.62  fof(f1432,plain,(
% 1.83/0.62    $false),
% 1.83/0.62    inference(avatar_sat_refutation,[],[f945,f1122,f1431])).
% 1.83/0.62  fof(f1431,plain,(
% 1.83/0.62    ~spl4_6),
% 1.83/0.62    inference(avatar_contradiction_clause,[],[f1430])).
% 1.83/0.62  fof(f1430,plain,(
% 1.83/0.62    $false | ~spl4_6),
% 1.83/0.62    inference(subsumption_resolution,[],[f1429,f110])).
% 1.83/0.62  fof(f110,plain,(
% 1.83/0.62    v1_relat_1(sK3)),
% 1.83/0.62    inference(resolution,[],[f66,f82])).
% 1.83/0.62  fof(f82,plain,(
% 1.83/0.62    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 1.83/0.62    inference(definition_unfolding,[],[f43,f80])).
% 1.83/0.62  fof(f80,plain,(
% 1.83/0.62    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.83/0.62    inference(definition_unfolding,[],[f48,f79])).
% 1.83/0.62  % (23100)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.83/0.62  % (23093)Refutation not found, incomplete strategy% (23093)------------------------------
% 1.83/0.62  % (23093)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.83/0.62  % (23105)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.83/0.62  % (23093)Termination reason: Refutation not found, incomplete strategy
% 1.83/0.62  
% 1.83/0.62  % (23093)Memory used [KB]: 1791
% 1.83/0.62  % (23093)Time elapsed: 0.184 s
% 1.83/0.62  % (23093)------------------------------
% 1.83/0.62  % (23093)------------------------------
% 1.83/0.62  % (23096)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.83/0.62  % (23100)Refutation not found, incomplete strategy% (23100)------------------------------
% 1.83/0.62  % (23100)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.83/0.62  % (23100)Termination reason: Refutation not found, incomplete strategy
% 1.83/0.62  
% 1.83/0.62  % (23100)Memory used [KB]: 10746
% 1.83/0.62  % (23100)Time elapsed: 0.176 s
% 1.83/0.62  % (23100)------------------------------
% 1.83/0.62  % (23100)------------------------------
% 1.83/0.62  % (23105)Refutation not found, incomplete strategy% (23105)------------------------------
% 1.83/0.62  % (23105)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.83/0.62  % (23105)Termination reason: Refutation not found, incomplete strategy
% 1.83/0.62  
% 1.83/0.62  % (23105)Memory used [KB]: 1663
% 1.83/0.62  % (23105)Time elapsed: 0.190 s
% 1.83/0.62  % (23105)------------------------------
% 1.83/0.62  % (23105)------------------------------
% 1.83/0.62  % (23104)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.83/0.62  % (23104)Refutation not found, incomplete strategy% (23104)------------------------------
% 1.83/0.62  % (23104)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.83/0.62  % (23104)Termination reason: Refutation not found, incomplete strategy
% 1.83/0.62  
% 1.83/0.62  % (23104)Memory used [KB]: 10746
% 1.83/0.62  % (23104)Time elapsed: 0.190 s
% 1.83/0.62  % (23104)------------------------------
% 1.83/0.62  % (23104)------------------------------
% 1.83/0.62  % (23088)Refutation not found, incomplete strategy% (23088)------------------------------
% 1.83/0.62  % (23088)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.83/0.62  % (23088)Termination reason: Refutation not found, incomplete strategy
% 1.83/0.62  
% 1.83/0.62  % (23088)Memory used [KB]: 10746
% 1.83/0.62  % (23088)Time elapsed: 0.192 s
% 1.83/0.62  % (23088)------------------------------
% 1.83/0.62  % (23088)------------------------------
% 1.83/0.63  % (23092)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.83/0.63  fof(f79,plain,(
% 1.83/0.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.83/0.63    inference(definition_unfolding,[],[f52,f65])).
% 1.83/0.63  % (23102)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.83/0.63  fof(f65,plain,(
% 1.83/0.63    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.83/0.63    inference(cnf_transformation,[],[f5])).
% 1.83/0.63  fof(f5,axiom,(
% 1.83/0.63    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.83/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.83/0.63  fof(f52,plain,(
% 1.83/0.63    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.83/0.63    inference(cnf_transformation,[],[f4])).
% 1.83/0.63  % (23092)Refutation not found, incomplete strategy% (23092)------------------------------
% 1.83/0.63  % (23092)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.83/0.63  % (23092)Termination reason: Refutation not found, incomplete strategy
% 1.83/0.63  
% 1.83/0.63  % (23092)Memory used [KB]: 10618
% 1.83/0.63  % (23092)Time elapsed: 0.147 s
% 1.83/0.63  % (23092)------------------------------
% 1.83/0.63  % (23092)------------------------------
% 1.83/0.63  fof(f4,axiom,(
% 1.83/0.63    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.83/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.83/0.63  fof(f48,plain,(
% 1.83/0.63    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.83/0.63    inference(cnf_transformation,[],[f3])).
% 1.83/0.63  fof(f3,axiom,(
% 1.83/0.63    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.83/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.83/0.63  fof(f43,plain,(
% 1.83/0.63    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.83/0.63    inference(cnf_transformation,[],[f32])).
% 1.83/0.63  fof(f32,plain,(
% 1.83/0.63    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK3,k1_tarski(sK0),sK1) & v1_funct_1(sK3)),
% 1.83/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f31])).
% 1.83/0.63  fof(f31,plain,(
% 1.83/0.63    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK3,k1_tarski(sK0),sK1) & v1_funct_1(sK3))),
% 1.83/0.63    introduced(choice_axiom,[])).
% 1.83/0.63  fof(f20,plain,(
% 1.83/0.63    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3))),
% 1.83/0.63    inference(flattening,[],[f19])).
% 1.83/0.63  fof(f19,plain,(
% 1.83/0.63    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)))),
% 1.83/0.63    inference(ennf_transformation,[],[f18])).
% 1.83/0.63  fof(f18,negated_conjecture,(
% 1.83/0.63    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.83/0.63    inference(negated_conjecture,[],[f17])).
% 1.83/0.63  fof(f17,conjecture,(
% 1.83/0.63    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.83/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).
% 1.83/0.63  fof(f66,plain,(
% 1.83/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.83/0.63    inference(cnf_transformation,[],[f27])).
% 1.83/0.63  fof(f27,plain,(
% 1.83/0.63    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.83/0.63    inference(ennf_transformation,[],[f13])).
% 1.83/0.63  fof(f13,axiom,(
% 1.83/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.83/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.83/0.63  fof(f1429,plain,(
% 1.83/0.63    ~v1_relat_1(sK3) | ~spl4_6),
% 1.83/0.63    inference(resolution,[],[f1398,f53])).
% 1.83/0.63  fof(f53,plain,(
% 1.83/0.63    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.83/0.63    inference(cnf_transformation,[],[f23])).
% 1.83/0.63  fof(f23,plain,(
% 1.83/0.63    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.83/0.63    inference(ennf_transformation,[],[f10])).
% 1.83/0.63  fof(f10,axiom,(
% 1.83/0.63    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 1.83/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).
% 1.83/0.63  fof(f1398,plain,(
% 1.83/0.63    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | ~spl4_6),
% 1.83/0.63    inference(backward_demodulation,[],[f267,f1203])).
% 1.83/0.63  fof(f1203,plain,(
% 1.83/0.63    k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | ~spl4_6),
% 1.83/0.63    inference(subsumption_resolution,[],[f1202,f94])).
% 1.83/0.63  fof(f94,plain,(
% 1.83/0.63    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.83/0.63    inference(equality_resolution,[],[f58])).
% 1.83/0.63  fof(f58,plain,(
% 1.83/0.63    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.83/0.63    inference(cnf_transformation,[],[f35])).
% 1.83/0.63  fof(f35,plain,(
% 1.83/0.63    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.83/0.63    inference(flattening,[],[f34])).
% 1.83/0.63  fof(f34,plain,(
% 1.83/0.63    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.83/0.63    inference(nnf_transformation,[],[f1])).
% 1.83/0.63  fof(f1,axiom,(
% 1.83/0.63    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.83/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.83/0.63  fof(f1202,plain,(
% 1.83/0.63    ~r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | ~spl4_6),
% 1.83/0.63    inference(forward_demodulation,[],[f1201,f944])).
% 1.83/0.63  fof(f944,plain,(
% 1.83/0.63    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | ~spl4_6),
% 1.83/0.63    inference(avatar_component_clause,[],[f942])).
% 1.83/0.63  fof(f942,plain,(
% 1.83/0.63    spl4_6 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)),
% 1.83/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.83/0.63  fof(f1201,plain,(
% 1.83/0.63    ~r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k1_relat_1(sK3)) | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | ~spl4_6),
% 1.83/0.63    inference(subsumption_resolution,[],[f1200,f110])).
% 1.83/0.63  fof(f1200,plain,(
% 1.83/0.63    ~r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k1_relat_1(sK3)) | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | ~v1_relat_1(sK3) | ~spl4_6),
% 1.83/0.63    inference(subsumption_resolution,[],[f1194,f41])).
% 1.83/0.63  fof(f41,plain,(
% 1.83/0.63    v1_funct_1(sK3)),
% 1.83/0.63    inference(cnf_transformation,[],[f32])).
% 1.83/0.63  fof(f1194,plain,(
% 1.83/0.63    ~r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k1_relat_1(sK3)) | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_6),
% 1.83/0.63    inference(resolution,[],[f1147,f340])).
% 1.83/0.63  fof(f340,plain,(
% 1.83/0.63    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),k2_enumset1(X0,X0,X0,X0)) | ~r1_tarski(k2_enumset1(X0,X0,X0,X0),k1_relat_1(X1)) | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.83/0.63    inference(extensionality_resolution,[],[f59,f84])).
% 1.83/0.63  fof(f84,plain,(
% 1.83/0.63    ( ! [X0,X1] : (k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0) | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.83/0.63    inference(definition_unfolding,[],[f56,f80,f80])).
% 1.83/0.63  fof(f56,plain,(
% 1.83/0.63    ( ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.83/0.63    inference(cnf_transformation,[],[f26])).
% 1.83/0.63  fof(f26,plain,(
% 1.83/0.63    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.83/0.63    inference(flattening,[],[f25])).
% 1.83/0.63  fof(f25,plain,(
% 1.83/0.63    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.83/0.63    inference(ennf_transformation,[],[f12])).
% 1.83/0.63  fof(f12,axiom,(
% 1.83/0.63    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.83/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 1.83/0.63  % (23102)Refutation not found, incomplete strategy% (23102)------------------------------
% 1.83/0.63  % (23102)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.83/0.63  % (23102)Termination reason: Refutation not found, incomplete strategy
% 1.83/0.63  
% 1.83/0.63  % (23102)Memory used [KB]: 6396
% 1.83/0.63  % (23102)Time elapsed: 0.193 s
% 1.83/0.63  % (23102)------------------------------
% 1.83/0.63  % (23102)------------------------------
% 1.83/0.63  fof(f59,plain,(
% 1.83/0.63    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.83/0.63    inference(cnf_transformation,[],[f35])).
% 1.83/0.63  fof(f1147,plain,(
% 1.83/0.63    ( ! [X3] : (r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,X3))) ) | ~spl4_6),
% 1.83/0.63    inference(superposition,[],[f101,f944])).
% 1.83/0.63  fof(f101,plain,(
% 1.83/0.63    ( ! [X2,X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X1,X2))) )),
% 1.83/0.63    inference(equality_resolution,[],[f88])).
% 1.83/0.63  fof(f88,plain,(
% 1.83/0.63    ( ! [X2,X0,X3,X1] : (r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) | k2_enumset1(X0,X0,X0,X1) != X3) )),
% 1.83/0.63    inference(definition_unfolding,[],[f75,f65,f79])).
% 1.83/0.63  fof(f75,plain,(
% 1.83/0.63    ( ! [X2,X0,X3,X1] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) | k2_tarski(X0,X1) != X3) )),
% 1.83/0.63    inference(cnf_transformation,[],[f40])).
% 1.83/0.63  fof(f40,plain,(
% 1.83/0.63    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 1.83/0.63    inference(flattening,[],[f39])).
% 1.83/0.63  fof(f39,plain,(
% 1.83/0.63    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & ((k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3) | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 1.83/0.63    inference(nnf_transformation,[],[f30])).
% 1.83/0.63  fof(f30,plain,(
% 1.83/0.63    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3))),
% 1.83/0.63    inference(ennf_transformation,[],[f7])).
% 1.83/0.63  fof(f7,axiom,(
% 1.83/0.63    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> ~(k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3))),
% 1.83/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_zfmisc_1)).
% 1.83/0.63  fof(f267,plain,(
% 1.83/0.63    ~r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 1.83/0.63    inference(forward_demodulation,[],[f81,f253])).
% 1.83/0.63  fof(f253,plain,(
% 1.83/0.63    ( ! [X6] : (k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X6) = k9_relat_1(sK3,X6)) )),
% 1.83/0.63    inference(resolution,[],[f69,f82])).
% 1.83/0.63  fof(f69,plain,(
% 1.83/0.63    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.83/0.63    inference(cnf_transformation,[],[f29])).
% 1.83/0.63  fof(f29,plain,(
% 1.83/0.63    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.83/0.63    inference(ennf_transformation,[],[f15])).
% 1.83/0.63  fof(f15,axiom,(
% 1.83/0.63    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.83/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.83/0.63  fof(f81,plain,(
% 1.83/0.63    ~r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 1.83/0.63    inference(definition_unfolding,[],[f45,f80,f80])).
% 1.83/0.63  fof(f45,plain,(
% 1.83/0.63    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.83/0.63    inference(cnf_transformation,[],[f32])).
% 1.83/0.63  fof(f1122,plain,(
% 1.83/0.63    ~spl4_5),
% 1.83/0.63    inference(avatar_contradiction_clause,[],[f1121])).
% 1.83/0.63  fof(f1121,plain,(
% 1.83/0.63    $false | ~spl4_5),
% 1.83/0.63    inference(subsumption_resolution,[],[f1120,f46])).
% 1.83/0.63  fof(f46,plain,(
% 1.83/0.63    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.83/0.63    inference(cnf_transformation,[],[f2])).
% 1.83/0.63  fof(f2,axiom,(
% 1.83/0.63    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.83/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.83/0.63  fof(f1120,plain,(
% 1.83/0.63    ~r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) | ~spl4_5),
% 1.83/0.63    inference(forward_demodulation,[],[f1112,f47])).
% 1.83/0.63  fof(f47,plain,(
% 1.83/0.63    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 1.83/0.63    inference(cnf_transformation,[],[f11])).
% 1.83/0.63  fof(f11,axiom,(
% 1.83/0.63    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 1.83/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
% 1.83/0.63  fof(f1112,plain,(
% 1.83/0.63    ~r1_tarski(k9_relat_1(k1_xboole_0,sK2),k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) | ~spl4_5),
% 1.83/0.63    inference(backward_demodulation,[],[f267,f1095])).
% 1.83/0.63  fof(f1095,plain,(
% 1.83/0.63    k1_xboole_0 = sK3 | ~spl4_5),
% 1.83/0.63    inference(resolution,[],[f986,f122])).
% 1.83/0.63  fof(f122,plain,(
% 1.83/0.63    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.83/0.63    inference(resolution,[],[f59,f46])).
% 1.83/0.63  fof(f986,plain,(
% 1.83/0.63    r1_tarski(sK3,k1_xboole_0) | ~spl4_5),
% 1.83/0.63    inference(forward_demodulation,[],[f985,f97])).
% 1.83/0.63  fof(f97,plain,(
% 1.83/0.63    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.83/0.63    inference(equality_resolution,[],[f63])).
% 1.83/0.63  fof(f63,plain,(
% 1.83/0.63    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.83/0.63    inference(cnf_transformation,[],[f38])).
% 1.83/0.63  fof(f38,plain,(
% 1.83/0.63    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.83/0.63    inference(flattening,[],[f37])).
% 1.83/0.63  fof(f37,plain,(
% 1.83/0.63    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.83/0.63    inference(nnf_transformation,[],[f6])).
% 1.83/0.63  fof(f6,axiom,(
% 1.83/0.63    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.83/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.83/0.63  fof(f985,plain,(
% 1.83/0.63    r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3))) | ~spl4_5),
% 1.83/0.63    inference(subsumption_resolution,[],[f984,f41])).
% 1.83/0.63  fof(f984,plain,(
% 1.83/0.63    r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3))) | ~v1_funct_1(sK3) | ~spl4_5),
% 1.83/0.63    inference(subsumption_resolution,[],[f957,f110])).
% 1.83/0.63  fof(f957,plain,(
% 1.83/0.63    r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3))) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~spl4_5),
% 1.83/0.63    inference(superposition,[],[f233,f940])).
% 1.83/0.63  fof(f940,plain,(
% 1.83/0.63    k1_xboole_0 = k1_relat_1(sK3) | ~spl4_5),
% 1.83/0.63    inference(avatar_component_clause,[],[f938])).
% 1.83/0.63  fof(f938,plain,(
% 1.83/0.63    spl4_5 <=> k1_xboole_0 = k1_relat_1(sK3)),
% 1.83/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.83/0.63  fof(f233,plain,(
% 1.83/0.63    ( ! [X3] : (r1_tarski(X3,k2_zfmisc_1(k1_relat_1(X3),k2_relat_1(X3))) | ~v1_relat_1(X3) | ~v1_funct_1(X3)) )),
% 1.83/0.63    inference(resolution,[],[f51,f60])).
% 1.83/0.63  fof(f60,plain,(
% 1.83/0.63    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.83/0.63    inference(cnf_transformation,[],[f36])).
% 1.83/0.63  fof(f36,plain,(
% 1.83/0.63    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.83/0.63    inference(nnf_transformation,[],[f8])).
% 1.83/0.63  fof(f8,axiom,(
% 1.83/0.63    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.83/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.83/0.63  fof(f51,plain,(
% 1.83/0.63    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.83/0.63    inference(cnf_transformation,[],[f22])).
% 1.83/0.63  fof(f22,plain,(
% 1.83/0.63    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.83/0.63    inference(flattening,[],[f21])).
% 1.83/0.63  fof(f21,plain,(
% 1.83/0.63    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.83/0.63    inference(ennf_transformation,[],[f16])).
% 1.83/0.63  fof(f16,axiom,(
% 1.83/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.83/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 1.83/0.63  fof(f945,plain,(
% 1.83/0.63    spl4_5 | spl4_6),
% 1.83/0.63    inference(avatar_split_clause,[],[f936,f942,f938])).
% 1.83/0.63  fof(f936,plain,(
% 1.83/0.63    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | k1_xboole_0 = k1_relat_1(sK3)),
% 1.83/0.63    inference(subsumption_resolution,[],[f929,f110])).
% 1.83/0.63  fof(f929,plain,(
% 1.83/0.63    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | k1_xboole_0 = k1_relat_1(sK3) | ~v1_relat_1(sK3)),
% 1.83/0.63    inference(duplicate_literal_removal,[],[f928])).
% 1.83/0.63  fof(f928,plain,(
% 1.83/0.63    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | k1_xboole_0 = k1_relat_1(sK3) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | ~v1_relat_1(sK3)),
% 1.83/0.63    inference(resolution,[],[f364,f142])).
% 1.83/0.63  fof(f142,plain,(
% 1.83/0.63    v4_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.83/0.63    inference(resolution,[],[f67,f82])).
% 1.83/0.63  fof(f67,plain,(
% 1.83/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.83/0.63    inference(cnf_transformation,[],[f28])).
% 1.83/0.63  fof(f28,plain,(
% 1.83/0.63    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.83/0.63    inference(ennf_transformation,[],[f14])).
% 1.83/0.63  fof(f14,axiom,(
% 1.83/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.83/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.83/0.63  fof(f364,plain,(
% 1.83/0.63    ( ! [X26,X24,X27,X25] : (~v4_relat_1(X26,k2_enumset1(X24,X24,X27,X25)) | k1_relat_1(X26) = k2_enumset1(X27,X27,X27,X25) | k1_relat_1(X26) = k2_enumset1(X24,X24,X24,X27) | k1_relat_1(X26) = k2_enumset1(X25,X25,X25,X25) | k1_relat_1(X26) = k2_enumset1(X27,X27,X27,X27) | k1_relat_1(X26) = k2_enumset1(X24,X24,X24,X24) | k1_xboole_0 = k1_relat_1(X26) | k1_relat_1(X26) = k2_enumset1(X24,X24,X27,X25) | k2_enumset1(X24,X24,X24,X25) = k1_relat_1(X26) | ~v1_relat_1(X26)) )),
% 1.83/0.63    inference(resolution,[],[f93,f54])).
% 1.83/0.63  fof(f54,plain,(
% 1.83/0.63    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.83/0.63    inference(cnf_transformation,[],[f33])).
% 1.83/0.63  fof(f33,plain,(
% 1.83/0.63    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.83/0.63    inference(nnf_transformation,[],[f24])).
% 1.83/0.63  fof(f24,plain,(
% 1.83/0.63    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.83/0.63    inference(ennf_transformation,[],[f9])).
% 1.83/0.63  fof(f9,axiom,(
% 1.83/0.63    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.83/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 1.83/0.63  fof(f93,plain,(
% 1.83/0.63    ( ! [X2,X0,X3,X1] : (~r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) | k2_enumset1(X0,X0,X0,X2) = X3 | k2_enumset1(X1,X1,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X1) = X3 | k2_enumset1(X2,X2,X2,X2) = X3 | k2_enumset1(X1,X1,X1,X1) = X3 | k2_enumset1(X0,X0,X0,X0) = X3 | k1_xboole_0 = X3 | k2_enumset1(X0,X0,X1,X2) = X3) )),
% 1.83/0.63    inference(definition_unfolding,[],[f70,f65,f79,f79,f79,f80,f80,f80,f65])).
% 1.83/0.63  fof(f70,plain,(
% 1.83/0.63    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))) )),
% 1.83/0.63    inference(cnf_transformation,[],[f40])).
% 1.83/0.63  % SZS output end Proof for theBenchmark
% 1.83/0.63  % (23082)------------------------------
% 1.83/0.63  % (23082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.83/0.63  % (23082)Termination reason: Refutation
% 1.83/0.63  
% 1.83/0.63  % (23082)Memory used [KB]: 11257
% 1.83/0.63  % (23082)Time elapsed: 0.180 s
% 1.83/0.63  % (23082)------------------------------
% 1.83/0.63  % (23082)------------------------------
% 1.83/0.63  % (23075)Success in time 0.264 s
%------------------------------------------------------------------------------
