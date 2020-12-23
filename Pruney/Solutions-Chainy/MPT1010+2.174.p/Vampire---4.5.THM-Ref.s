%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:15 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   48 (  78 expanded)
%              Number of leaves         :   10 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :  114 ( 213 expanded)
%              Number of equality atoms :   29 (  56 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f88,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f65,f67,f74,f87])).

fof(f87,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f75])).

fof(f75,plain,
    ( $false
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f39,f51])).

fof(f51,plain,
    ( k1_xboole_0 = k2_tarski(sK1,sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl5_1
  <=> k1_xboole_0 = k2_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) != k1_xboole_0 ),
    inference(superposition,[],[f30,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)) ),
    inference(definition_unfolding,[],[f20,f18,f18])).

fof(f18,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f20,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X0),X1) ),
    inference(definition_unfolding,[],[f19,f18])).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f74,plain,(
    ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f69])).

fof(f69,plain,
    ( $false
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f16,f17,f68])).

fof(f68,plain,
    ( ! [X0] :
        ( sK1 = k1_funct_1(sK3,X0)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f54,f35])).

fof(f35,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_tarski(X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f23,f18])).

fof(f23,plain,(
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

fof(f54,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK3,X0),k2_tarski(sK1,sK1))
        | ~ r2_hidden(X0,sK0) )
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl5_2
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k1_funct_1(sK3,X0),k2_tarski(sK1,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f17,plain,(
    sK1 != k1_funct_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

fof(f16,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f67,plain,(
    spl5_4 ),
    inference(avatar_contradiction_clause,[],[f66])).

fof(f66,plain,
    ( $false
    | spl5_4 ),
    inference(subsumption_resolution,[],[f29,f62])).

fof(f62,plain,
    ( ~ v1_funct_2(sK3,sK0,k2_tarski(sK1,sK1))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl5_4
  <=> v1_funct_2(sK3,sK0,k2_tarski(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f29,plain,(
    v1_funct_2(sK3,sK0,k2_tarski(sK1,sK1)) ),
    inference(definition_unfolding,[],[f14,f18])).

fof(f14,plain,(
    v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f65,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f64])).

fof(f64,plain,
    ( $false
    | spl5_3 ),
    inference(subsumption_resolution,[],[f13,f58])).

fof(f58,plain,
    ( ~ v1_funct_1(sK3)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl5_3
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f13,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f63,plain,
    ( spl5_1
    | spl5_2
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f47,f60,f56,f53,f49])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK3,sK0,k2_tarski(sK1,sK1))
      | ~ v1_funct_1(sK3)
      | ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = k2_tarski(sK1,sK1)
      | r2_hidden(k1_funct_1(sK3,X0),k2_tarski(sK1,sK1)) ) ),
    inference(resolution,[],[f26,f28])).

fof(f28,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_tarski(sK1,sK1)))) ),
    inference(definition_unfolding,[],[f15,f18])).

fof(f15,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | r2_hidden(k1_funct_1(X3,X2),X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:08:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.55  % (21387)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (21379)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (21371)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.56  % (21371)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f88,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(avatar_sat_refutation,[],[f63,f65,f67,f74,f87])).
% 0.22/0.56  fof(f87,plain,(
% 0.22/0.56    ~spl5_1),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f75])).
% 0.22/0.56  fof(f75,plain,(
% 0.22/0.56    $false | ~spl5_1),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f39,f51])).
% 0.22/0.56  fof(f51,plain,(
% 0.22/0.56    k1_xboole_0 = k2_tarski(sK1,sK1) | ~spl5_1),
% 0.22/0.56    inference(avatar_component_clause,[],[f49])).
% 0.22/0.56  fof(f49,plain,(
% 0.22/0.56    spl5_1 <=> k1_xboole_0 = k2_tarski(sK1,sK1)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.56  fof(f39,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) != k1_xboole_0) )),
% 0.22/0.56    inference(superposition,[],[f30,f27])).
% 0.22/0.56  fof(f27,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1))) )),
% 0.22/0.56    inference(definition_unfolding,[],[f20,f18,f18])).
% 0.22/0.56  fof(f18,plain,(
% 0.22/0.56    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.56  fof(f20,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X0),X1)) )),
% 0.22/0.56    inference(definition_unfolding,[],[f19,f18])).
% 0.22/0.56  fof(f19,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) )),
% 0.22/0.56    inference(cnf_transformation,[],[f5])).
% 0.22/0.56  fof(f5,axiom,(
% 0.22/0.56    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.22/0.56  fof(f74,plain,(
% 0.22/0.56    ~spl5_2),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f69])).
% 0.22/0.56  fof(f69,plain,(
% 0.22/0.56    $false | ~spl5_2),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f16,f17,f68])).
% 0.22/0.56  fof(f68,plain,(
% 0.22/0.56    ( ! [X0] : (sK1 = k1_funct_1(sK3,X0) | ~r2_hidden(X0,sK0)) ) | ~spl5_2),
% 0.22/0.56    inference(resolution,[],[f54,f35])).
% 0.22/0.56  fof(f35,plain,(
% 0.22/0.56    ( ! [X2,X0] : (~r2_hidden(X2,k2_tarski(X0,X0)) | X0 = X2) )),
% 0.22/0.56    inference(equality_resolution,[],[f33])).
% 0.22/0.56  fof(f33,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k2_tarski(X0,X0) != X1) )),
% 0.22/0.56    inference(definition_unfolding,[],[f23,f18])).
% 0.22/0.56  fof(f23,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f1])).
% 0.22/0.56  fof(f1,axiom,(
% 0.22/0.56    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.22/0.56  fof(f54,plain,(
% 0.22/0.56    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),k2_tarski(sK1,sK1)) | ~r2_hidden(X0,sK0)) ) | ~spl5_2),
% 0.22/0.56    inference(avatar_component_clause,[],[f53])).
% 0.22/0.56  fof(f53,plain,(
% 0.22/0.56    spl5_2 <=> ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK3,X0),k2_tarski(sK1,sK1)))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.56  fof(f17,plain,(
% 0.22/0.56    sK1 != k1_funct_1(sK3,sK2)),
% 0.22/0.56    inference(cnf_transformation,[],[f10])).
% 0.22/0.56  fof(f10,plain,(
% 0.22/0.56    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 0.22/0.56    inference(flattening,[],[f9])).
% 0.22/0.56  fof(f9,plain,(
% 0.22/0.56    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 0.22/0.56    inference(ennf_transformation,[],[f8])).
% 0.22/0.56  fof(f8,negated_conjecture,(
% 0.22/0.56    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 0.22/0.56    inference(negated_conjecture,[],[f7])).
% 0.22/0.56  fof(f7,conjecture,(
% 0.22/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).
% 0.22/0.56  fof(f16,plain,(
% 0.22/0.56    r2_hidden(sK2,sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f10])).
% 0.22/0.56  fof(f67,plain,(
% 0.22/0.56    spl5_4),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f66])).
% 0.22/0.56  fof(f66,plain,(
% 0.22/0.56    $false | spl5_4),
% 0.22/0.56    inference(subsumption_resolution,[],[f29,f62])).
% 0.22/0.56  fof(f62,plain,(
% 0.22/0.56    ~v1_funct_2(sK3,sK0,k2_tarski(sK1,sK1)) | spl5_4),
% 0.22/0.56    inference(avatar_component_clause,[],[f60])).
% 0.22/0.56  fof(f60,plain,(
% 0.22/0.56    spl5_4 <=> v1_funct_2(sK3,sK0,k2_tarski(sK1,sK1))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    v1_funct_2(sK3,sK0,k2_tarski(sK1,sK1))),
% 0.22/0.56    inference(definition_unfolding,[],[f14,f18])).
% 0.22/0.56  fof(f14,plain,(
% 0.22/0.56    v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 0.22/0.56    inference(cnf_transformation,[],[f10])).
% 0.22/0.56  fof(f65,plain,(
% 0.22/0.56    spl5_3),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f64])).
% 0.22/0.56  fof(f64,plain,(
% 0.22/0.56    $false | spl5_3),
% 0.22/0.56    inference(subsumption_resolution,[],[f13,f58])).
% 0.22/0.56  fof(f58,plain,(
% 0.22/0.56    ~v1_funct_1(sK3) | spl5_3),
% 0.22/0.56    inference(avatar_component_clause,[],[f56])).
% 0.22/0.56  fof(f56,plain,(
% 0.22/0.56    spl5_3 <=> v1_funct_1(sK3)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.56  fof(f13,plain,(
% 0.22/0.56    v1_funct_1(sK3)),
% 0.22/0.56    inference(cnf_transformation,[],[f10])).
% 0.22/0.56  fof(f63,plain,(
% 0.22/0.56    spl5_1 | spl5_2 | ~spl5_3 | ~spl5_4),
% 0.22/0.56    inference(avatar_split_clause,[],[f47,f60,f56,f53,f49])).
% 0.22/0.56  fof(f47,plain,(
% 0.22/0.56    ( ! [X0] : (~v1_funct_2(sK3,sK0,k2_tarski(sK1,sK1)) | ~v1_funct_1(sK3) | ~r2_hidden(X0,sK0) | k1_xboole_0 = k2_tarski(sK1,sK1) | r2_hidden(k1_funct_1(sK3,X0),k2_tarski(sK1,sK1))) )),
% 0.22/0.56    inference(resolution,[],[f26,f28])).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_tarski(sK1,sK1))))),
% 0.22/0.56    inference(definition_unfolding,[],[f15,f18])).
% 0.22/0.56  fof(f15,plain,(
% 0.22/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 0.22/0.56    inference(cnf_transformation,[],[f10])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | r2_hidden(k1_funct_1(X3,X2),X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f12])).
% 0.22/0.56  fof(f12,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.22/0.56    inference(flattening,[],[f11])).
% 0.22/0.56  fof(f11,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.22/0.56    inference(ennf_transformation,[],[f6])).
% 0.22/0.56  fof(f6,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (21371)------------------------------
% 0.22/0.56  % (21371)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (21371)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (21371)Memory used [KB]: 6268
% 0.22/0.56  % (21371)Time elapsed: 0.125 s
% 0.22/0.56  % (21371)------------------------------
% 0.22/0.56  % (21371)------------------------------
% 0.22/0.56  % (21357)Success in time 0.193 s
%------------------------------------------------------------------------------
