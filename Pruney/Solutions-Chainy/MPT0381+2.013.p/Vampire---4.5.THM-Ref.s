%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.14s
% Verified   : 
% Statistics : Number of formulae       :   46 (  92 expanded)
%              Number of leaves         :   11 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :   88 ( 147 expanded)
%              Number of equality atoms :    8 (  39 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f217,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f191,f216])).

fof(f216,plain,(
    ~ spl4_1 ),
    inference(avatar_contradiction_clause,[],[f207])).

fof(f207,plain,
    ( $false
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f38,f193,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f26,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f33,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f193,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_zfmisc_1(sK1))
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f74,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f74,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK1))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl4_1
  <=> v1_xboole_0(k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f38,plain,(
    ! [X0] : r1_tarski(k2_enumset1(X0,X0,X0,X0),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f23,f36])).

fof(f36,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f24,f35])).

fof(f24,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f23,plain,(
    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_zfmisc_1)).

fof(f191,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f186])).

fof(f186,plain,
    ( $false
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f38,f109,f40])).

fof(f109,plain,
    ( ~ r2_hidden(k2_enumset1(sK0,sK0,sK0,sK0),k1_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0)))
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f82,f63,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f63,plain,(
    r1_tarski(k1_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0)),k1_zfmisc_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f44,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(f44,plain,(
    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f16,f16,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f27,f35])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X2)
      | r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f16,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(f82,plain,
    ( ~ r2_hidden(k2_enumset1(sK0,sK0,sK0,sK0),k1_zfmisc_1(sK1))
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f37,f75,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f75,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK1))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f37,plain,(
    ~ m1_subset_1(k2_enumset1(sK0,sK0,sK0,sK0),k1_zfmisc_1(sK1)) ),
    inference(definition_unfolding,[],[f17,f36])).

fof(f17,plain,(
    ~ m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n005.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:55:17 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.54  % (1498)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (1498)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f217,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f191,f216])).
% 0.21/0.55  fof(f216,plain,(
% 0.21/0.55    ~spl4_1),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f207])).
% 0.21/0.55  fof(f207,plain,(
% 0.21/0.55    $false | ~spl4_1),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f38,f193,f40])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f26,f35])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f33,f34])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.21/0.55  fof(f193,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(X0,k1_zfmisc_1(sK1))) ) | ~spl4_1),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f74,f32])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.55  fof(f74,plain,(
% 0.21/0.55    v1_xboole_0(k1_zfmisc_1(sK1)) | ~spl4_1),
% 0.21/0.55    inference(avatar_component_clause,[],[f73])).
% 0.21/0.55  fof(f73,plain,(
% 0.21/0.55    spl4_1 <=> v1_xboole_0(k1_zfmisc_1(sK1))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    ( ! [X0] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(definition_unfolding,[],[f23,f36])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f24,f35])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ( ! [X0] : (r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f8])).
% 1.14/0.55  fof(f8,axiom,(
% 1.14/0.55    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))),
% 1.14/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_zfmisc_1)).
% 1.14/0.55  fof(f191,plain,(
% 1.14/0.55    spl4_1),
% 1.14/0.55    inference(avatar_contradiction_clause,[],[f186])).
% 1.14/0.55  fof(f186,plain,(
% 1.14/0.55    $false | spl4_1),
% 1.14/0.55    inference(unit_resulting_resolution,[],[f38,f109,f40])).
% 1.14/0.55  fof(f109,plain,(
% 1.14/0.55    ~r2_hidden(k2_enumset1(sK0,sK0,sK0,sK0),k1_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0))) | spl4_1),
% 1.14/0.55    inference(unit_resulting_resolution,[],[f82,f63,f28])).
% 1.14/0.55  fof(f28,plain,(
% 1.14/0.55    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 1.14/0.55    inference(cnf_transformation,[],[f15])).
% 1.14/0.55  fof(f15,plain,(
% 1.14/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.14/0.55    inference(ennf_transformation,[],[f2])).
% 1.14/0.55  fof(f2,axiom,(
% 1.14/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.14/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.14/0.55  fof(f63,plain,(
% 1.14/0.55    r1_tarski(k1_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0)),k1_zfmisc_1(sK1))),
% 1.14/0.55    inference(unit_resulting_resolution,[],[f44,f22])).
% 1.14/0.55  fof(f22,plain,(
% 1.14/0.55    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.14/0.55    inference(cnf_transformation,[],[f14])).
% 1.14/0.55  fof(f14,plain,(
% 1.14/0.55    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 1.14/0.55    inference(ennf_transformation,[],[f7])).
% 1.14/0.55  fof(f7,axiom,(
% 1.14/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 1.14/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).
% 1.14/0.55  fof(f44,plain,(
% 1.14/0.55    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 1.14/0.55    inference(unit_resulting_resolution,[],[f16,f16,f39])).
% 1.14/0.55  fof(f39,plain,(
% 1.14/0.55    ( ! [X2,X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.14/0.55    inference(definition_unfolding,[],[f27,f35])).
% 1.14/0.55  fof(f27,plain,(
% 1.14/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.14/0.55    inference(cnf_transformation,[],[f6])).
% 1.14/0.55  fof(f16,plain,(
% 1.14/0.55    r2_hidden(sK0,sK1)),
% 1.14/0.55    inference(cnf_transformation,[],[f12])).
% 1.14/0.55  fof(f12,plain,(
% 1.14/0.55    ? [X0,X1] : (~m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) & r2_hidden(X0,X1))),
% 1.14/0.55    inference(ennf_transformation,[],[f11])).
% 1.14/0.55  fof(f11,negated_conjecture,(
% 1.14/0.55    ~! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 1.14/0.55    inference(negated_conjecture,[],[f10])).
% 1.14/0.55  fof(f10,conjecture,(
% 1.14/0.55    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 1.14/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).
% 1.14/0.55  fof(f82,plain,(
% 1.14/0.55    ~r2_hidden(k2_enumset1(sK0,sK0,sK0,sK0),k1_zfmisc_1(sK1)) | spl4_1),
% 1.14/0.55    inference(unit_resulting_resolution,[],[f37,f75,f20])).
% 1.14/0.55  fof(f20,plain,(
% 1.14/0.55    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 1.14/0.55    inference(cnf_transformation,[],[f13])).
% 1.14/0.55  fof(f13,plain,(
% 1.14/0.55    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.14/0.55    inference(ennf_transformation,[],[f9])).
% 1.14/0.55  fof(f9,axiom,(
% 1.14/0.55    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.14/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.14/0.55  fof(f75,plain,(
% 1.14/0.55    ~v1_xboole_0(k1_zfmisc_1(sK1)) | spl4_1),
% 1.14/0.55    inference(avatar_component_clause,[],[f73])).
% 1.14/0.55  fof(f37,plain,(
% 1.14/0.55    ~m1_subset_1(k2_enumset1(sK0,sK0,sK0,sK0),k1_zfmisc_1(sK1))),
% 1.14/0.55    inference(definition_unfolding,[],[f17,f36])).
% 1.14/0.55  fof(f17,plain,(
% 1.14/0.55    ~m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1))),
% 1.14/0.55    inference(cnf_transformation,[],[f12])).
% 1.14/0.55  % SZS output end Proof for theBenchmark
% 1.14/0.55  % (1498)------------------------------
% 1.14/0.55  % (1498)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.14/0.55  % (1498)Termination reason: Refutation
% 1.14/0.55  
% 1.14/0.55  % (1498)Memory used [KB]: 6268
% 1.14/0.55  % (1498)Time elapsed: 0.118 s
% 1.14/0.55  % (1498)------------------------------
% 1.14/0.55  % (1498)------------------------------
% 1.14/0.55  % (1493)Success in time 0.187 s
%------------------------------------------------------------------------------
