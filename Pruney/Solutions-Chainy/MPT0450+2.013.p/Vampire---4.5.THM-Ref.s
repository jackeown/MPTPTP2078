%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 137 expanded)
%              Number of leaves         :   16 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :  147 ( 298 expanded)
%              Number of equality atoms :   21 (  71 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f135,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f86,f109,f119,f126,f134])).

fof(f134,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f127])).

fof(f127,plain,
    ( $false
    | spl3_5 ),
    inference(unit_resulting_resolution,[],[f22,f108])).

fof(f108,plain,
    ( ~ v1_relat_1(sK1)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl3_5
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f22,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relat_1)).

fof(f126,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f123])).

fof(f123,plain,
    ( $false
    | spl3_4 ),
    inference(unit_resulting_resolution,[],[f51,f104,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f104,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl3_4
  <=> r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f51,plain,(
    ! [X2,X0,X5,X1] : r2_hidden(X5,k2_enumset1(X0,X1,X2,X5)) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( r2_hidden(X5,X4)
      | k2_enumset1(X0,X1,X2,X5) != X4 ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X3 != X5
      | r2_hidden(X5,X4)
      | k2_enumset1(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5 ) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X3 != X5
              & X2 != X5
              & X1 != X5
              & X0 != X5 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_enumset1)).

fof(f119,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | spl3_3 ),
    inference(unit_resulting_resolution,[],[f51,f113,f30])).

fof(f113,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1)
    | spl3_3 ),
    inference(unit_resulting_resolution,[],[f110,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f110,plain,
    ( ~ m1_subset_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),k1_zfmisc_1(sK1))
    | spl3_3 ),
    inference(unit_resulting_resolution,[],[f22,f100,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f100,plain,
    ( ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl3_3
  <=> v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f109,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | spl3_2 ),
    inference(avatar_split_clause,[],[f92,f68,f106,f102,f98])).

fof(f68,plain,
    ( spl3_2
  <=> r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f92,plain,
    ( ~ v1_relat_1(sK1)
    | ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1)
    | ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))
    | spl3_2 ),
    inference(resolution,[],[f70,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

fof(f70,plain,
    ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK1))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f86,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f83])).

fof(f83,plain,
    ( $false
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f51,f80,f30])).

fof(f80,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1)
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f75,f32])).

fof(f75,plain,
    ( ~ m1_subset_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),k1_zfmisc_1(sK1))
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f22,f72,f29])).

fof(f72,plain,
    ( ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f24,f49,f66,f27])).

fof(f66,plain,
    ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl3_1
  <=> r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f26,f46])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f28,f45])).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f31,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f24,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f71,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f60,f68,f64])).

fof(f60,plain,
    ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK1))
    | ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK0)) ),
    inference(resolution,[],[f47,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f25,f46])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

% (19120)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% (19134)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% (19134)Refutation not found, incomplete strategy% (19134)------------------------------
% (19134)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (19124)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f47,plain,(
    ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK1)))) ),
    inference(definition_unfolding,[],[f23,f46,f46])).

fof(f23,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:14:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.54  % (19112)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (19122)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  % (19116)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.57  % (19116)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f135,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(avatar_sat_refutation,[],[f71,f86,f109,f119,f126,f134])).
% 0.21/0.57  fof(f134,plain,(
% 0.21/0.57    spl3_5),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f127])).
% 0.21/0.57  fof(f127,plain,(
% 0.21/0.57    $false | spl3_5),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f22,f108])).
% 0.21/0.57  fof(f108,plain,(
% 0.21/0.57    ~v1_relat_1(sK1) | spl3_5),
% 0.21/0.57    inference(avatar_component_clause,[],[f106])).
% 0.21/0.57  fof(f106,plain,(
% 0.21/0.57    spl3_5 <=> v1_relat_1(sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.57  fof(f22,plain,(
% 0.21/0.57    v1_relat_1(sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f14])).
% 0.21/0.57  fof(f14,plain,(
% 0.21/0.57    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f13])).
% 0.21/0.57  fof(f13,negated_conjecture,(
% 0.21/0.57    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.21/0.57    inference(negated_conjecture,[],[f12])).
% 0.21/0.57  fof(f12,conjecture,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relat_1)).
% 0.21/0.57  fof(f126,plain,(
% 0.21/0.57    spl3_4),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f123])).
% 0.21/0.57  fof(f123,plain,(
% 0.21/0.57    $false | spl3_4),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f51,f104,f30])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f20])).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f9])).
% 0.21/0.57  fof(f9,axiom,(
% 0.21/0.57    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).
% 0.21/0.57  fof(f104,plain,(
% 0.21/0.57    ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1) | spl3_4),
% 0.21/0.57    inference(avatar_component_clause,[],[f102])).
% 0.21/0.57  fof(f102,plain,(
% 0.21/0.57    spl3_4 <=> r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.57  fof(f51,plain,(
% 0.21/0.57    ( ! [X2,X0,X5,X1] : (r2_hidden(X5,k2_enumset1(X0,X1,X2,X5))) )),
% 0.21/0.57    inference(equality_resolution,[],[f50])).
% 0.21/0.57  fof(f50,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X5,X1] : (r2_hidden(X5,X4) | k2_enumset1(X0,X1,X2,X5) != X4) )),
% 0.21/0.57    inference(equality_resolution,[],[f43])).
% 0.21/0.57  fof(f43,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (X3 != X5 | r2_hidden(X5,X4) | k2_enumset1(X0,X1,X2,X3) != X4) )),
% 0.21/0.57    inference(cnf_transformation,[],[f21])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5)))),
% 0.21/0.57    inference(ennf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> ~(X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_enumset1)).
% 0.21/0.57  fof(f119,plain,(
% 0.21/0.57    spl3_3),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f116])).
% 0.21/0.57  fof(f116,plain,(
% 0.21/0.57    $false | spl3_3),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f51,f113,f30])).
% 0.21/0.57  fof(f113,plain,(
% 0.21/0.57    ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1) | spl3_3),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f110,f32])).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,axiom,(
% 0.21/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.57  fof(f110,plain,(
% 0.21/0.57    ~m1_subset_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),k1_zfmisc_1(sK1)) | spl3_3),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f22,f100,f29])).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f19])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f10])).
% 0.21/0.57  fof(f10,axiom,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.57  fof(f100,plain,(
% 0.21/0.57    ~v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) | spl3_3),
% 0.21/0.57    inference(avatar_component_clause,[],[f98])).
% 0.21/0.57  fof(f98,plain,(
% 0.21/0.57    spl3_3 <=> v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.57  fof(f109,plain,(
% 0.21/0.57    ~spl3_3 | ~spl3_4 | ~spl3_5 | spl3_2),
% 0.21/0.57    inference(avatar_split_clause,[],[f92,f68,f106,f102,f98])).
% 0.21/0.57  fof(f68,plain,(
% 0.21/0.57    spl3_2 <=> r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK1))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.57  fof(f92,plain,(
% 0.21/0.57    ~v1_relat_1(sK1) | ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1) | ~v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) | spl3_2),
% 0.21/0.57    inference(resolution,[],[f70,f27])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f18])).
% 0.21/0.57  fof(f18,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(flattening,[],[f17])).
% 0.21/0.57  fof(f17,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : ((r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f11])).
% 0.21/0.57  fof(f11,axiom,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).
% 0.21/0.57  fof(f70,plain,(
% 0.21/0.57    ~r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK1)) | spl3_2),
% 0.21/0.57    inference(avatar_component_clause,[],[f68])).
% 0.21/0.57  fof(f86,plain,(
% 0.21/0.57    spl3_1),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f83])).
% 0.21/0.57  fof(f83,plain,(
% 0.21/0.57    $false | spl3_1),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f51,f80,f30])).
% 0.21/0.57  fof(f80,plain,(
% 0.21/0.57    ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1) | spl3_1),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f75,f32])).
% 0.21/0.57  fof(f75,plain,(
% 0.21/0.57    ~m1_subset_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),k1_zfmisc_1(sK1)) | spl3_1),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f22,f72,f29])).
% 0.21/0.57  fof(f72,plain,(
% 0.21/0.57    ~v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) | spl3_1),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f24,f49,f66,f27])).
% 0.21/0.57  fof(f66,plain,(
% 0.21/0.57    ~r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK0)) | spl3_1),
% 0.21/0.57    inference(avatar_component_clause,[],[f64])).
% 0.21/0.57  fof(f64,plain,(
% 0.21/0.57    spl3_1 <=> r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.57  fof(f49,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f26,f46])).
% 0.21/0.57  fof(f46,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.57    inference(definition_unfolding,[],[f28,f45])).
% 0.21/0.57  fof(f45,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f31,f44])).
% 0.21/0.57  fof(f44,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,axiom,(
% 0.21/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    v1_relat_1(sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f14])).
% 0.21/0.57  fof(f71,plain,(
% 0.21/0.57    ~spl3_1 | ~spl3_2),
% 0.21/0.57    inference(avatar_split_clause,[],[f60,f68,f64])).
% 0.21/0.57  fof(f60,plain,(
% 0.21/0.57    ~r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK1)) | ~r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK0))),
% 0.21/0.57    inference(resolution,[],[f47,f48])).
% 0.21/0.57  fof(f48,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f25,f46])).
% 0.21/0.57  fof(f25,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X0,X2) | r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f16])).
% 0.21/0.57  fof(f16,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.57    inference(flattening,[],[f15])).
% 0.21/0.57  fof(f15,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.57    inference(ennf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.21/0.57  % (19120)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.57  % (19134)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.57  % (19134)Refutation not found, incomplete strategy% (19134)------------------------------
% 0.21/0.57  % (19134)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (19124)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.57  fof(f47,plain,(
% 0.21/0.57    ~r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK1))))),
% 0.21/0.57    inference(definition_unfolding,[],[f23,f46,f46])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))),
% 0.21/0.57    inference(cnf_transformation,[],[f14])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (19116)------------------------------
% 0.21/0.57  % (19116)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (19116)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (19116)Memory used [KB]: 6268
% 0.21/0.57  % (19116)Time elapsed: 0.137 s
% 0.21/0.57  % (19116)------------------------------
% 0.21/0.57  % (19116)------------------------------
% 0.21/0.58  % (19111)Success in time 0.213 s
%------------------------------------------------------------------------------
