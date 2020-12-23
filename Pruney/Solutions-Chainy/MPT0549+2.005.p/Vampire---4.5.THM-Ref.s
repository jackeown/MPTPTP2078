%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:36 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 177 expanded)
%              Number of leaves         :   16 (  48 expanded)
%              Depth                    :   12
%              Number of atoms          :  204 ( 576 expanded)
%              Number of equality atoms :   53 ( 191 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f281,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f87,f169,f263,f266,f279])).

fof(f279,plain,
    ( spl3_2
    | ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f278])).

fof(f278,plain,
    ( $false
    | spl3_2
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f277,f41])).

fof(f41,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 != k9_relat_1(sK1,sK0) )
    & ( r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 = k9_relat_1(sK1,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f33,f34])).

fof(f34,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 = k9_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 != k9_relat_1(sK1,sK0) )
      & ( r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 = k9_relat_1(sK1,sK0) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k9_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k9_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k9_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k9_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k9_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

fof(f277,plain,
    ( ~ v1_relat_1(sK1)
    | spl3_2
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f274,f85])).

fof(f85,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl3_2
  <=> r1_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f274,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl3_4 ),
    inference(resolution,[],[f262,f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k7_relat_1(X0,X1),k1_xboole_0)
      | r1_xboole_0(k1_relat_1(X0),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f122,f45])).

fof(f45,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k7_relat_1(X0,X1),k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k7_relat_1(X0,X1))
      | r1_xboole_0(k1_relat_1(X0),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(extensionality_resolution,[],[f60,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k7_relat_1(X1,X0)
      | r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
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

fof(f262,plain,
    ( r1_tarski(k7_relat_1(sK1,sK0),k1_xboole_0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f260])).

fof(f260,plain,
    ( spl3_4
  <=> r1_tarski(k7_relat_1(sK1,sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f266,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f265])).

fof(f265,plain,
    ( $false
    | spl3_3 ),
    inference(subsumption_resolution,[],[f264,f41])).

fof(f264,plain,
    ( ~ v1_relat_1(sK1)
    | spl3_3 ),
    inference(resolution,[],[f258,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f258,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f256])).

fof(f256,plain,
    ( spl3_3
  <=> v1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f263,plain,
    ( ~ spl3_3
    | spl3_4
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f254,f79,f260,f256])).

fof(f79,plain,
    ( spl3_1
  <=> k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f254,plain,
    ( r1_tarski(k7_relat_1(sK1,sK0),k1_xboole_0)
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f251,f113])).

fof(f113,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(resolution,[],[f110,f46])).

fof(f46,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f110,plain,(
    ! [X4,X3] :
      ( ~ r1_xboole_0(X3,X3)
      | k1_xboole_0 = k2_zfmisc_1(X4,X3) ) ),
    inference(resolution,[],[f65,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ( ~ r1_xboole_0(X2,X3)
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(f251,plain,
    ( r1_tarski(k7_relat_1(sK1,sK0),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK1,sK0)),k1_xboole_0))
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl3_1 ),
    inference(superposition,[],[f104,f80])).

fof(f80,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f104,plain,(
    ! [X0] :
      ( r1_tarski(k7_relat_1(sK1,X0),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK1,X0)),k9_relat_1(sK1,X0)))
      | ~ v1_relat_1(k7_relat_1(sK1,X0)) ) ),
    inference(superposition,[],[f50,f99])).

fof(f99,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    inference(resolution,[],[f53,f41])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f50,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(f169,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f168])).

fof(f168,plain,
    ( $false
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f167,f156])).

fof(f156,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | spl3_1
    | ~ spl3_2 ),
    inference(superposition,[],[f81,f141])).

fof(f141,plain,
    ( k9_relat_1(sK1,sK0) = k2_relat_1(k1_xboole_0)
    | ~ spl3_2 ),
    inference(superposition,[],[f99,f140])).

fof(f140,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f138,f41])).

fof(f138,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f55,f84])).

fof(f84,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f81,plain,
    ( k1_xboole_0 != k9_relat_1(sK1,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f167,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f163,f89])).

fof(f89,plain,(
    k1_xboole_0 = k9_relat_1(sK1,k1_xboole_0) ),
    inference(resolution,[],[f49,f41])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_relat_1)).

fof(f163,plain,(
    k9_relat_1(sK1,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f99,f160])).

% (7912)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
fof(f160,plain,(
    k1_xboole_0 = k7_relat_1(sK1,k1_xboole_0) ),
    inference(resolution,[],[f139,f41])).

fof(f139,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f55,f46])).

fof(f87,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f42,f83,f79])).

fof(f42,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f86,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f43,f83,f79])).

fof(f43,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 != k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:04:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (7892)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (7908)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.51  % (7892)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % (7899)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.52  % (7904)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.52  % (7888)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.52  % (7900)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.52  % (7903)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.52  % (7900)Refutation not found, incomplete strategy% (7900)------------------------------
% 0.20/0.52  % (7900)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (7900)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (7900)Memory used [KB]: 1663
% 0.20/0.52  % (7900)Time elapsed: 0.121 s
% 0.20/0.52  % (7900)------------------------------
% 0.20/0.52  % (7900)------------------------------
% 1.27/0.52  % SZS output start Proof for theBenchmark
% 1.27/0.52  fof(f281,plain,(
% 1.27/0.52    $false),
% 1.27/0.52    inference(avatar_sat_refutation,[],[f86,f87,f169,f263,f266,f279])).
% 1.27/0.52  fof(f279,plain,(
% 1.27/0.52    spl3_2 | ~spl3_4),
% 1.27/0.52    inference(avatar_contradiction_clause,[],[f278])).
% 1.27/0.52  fof(f278,plain,(
% 1.27/0.52    $false | (spl3_2 | ~spl3_4)),
% 1.27/0.52    inference(subsumption_resolution,[],[f277,f41])).
% 1.27/0.52  fof(f41,plain,(
% 1.27/0.52    v1_relat_1(sK1)),
% 1.27/0.52    inference(cnf_transformation,[],[f35])).
% 1.27/0.52  fof(f35,plain,(
% 1.27/0.52    (~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k9_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k9_relat_1(sK1,sK0)) & v1_relat_1(sK1)),
% 1.27/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f33,f34])).
% 1.27/0.52  fof(f34,plain,(
% 1.27/0.52    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k9_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k9_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k9_relat_1(sK1,sK0)) & v1_relat_1(sK1))),
% 1.27/0.52    introduced(choice_axiom,[])).
% 1.27/0.52  fof(f33,plain,(
% 1.27/0.52    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k9_relat_1(X1,X0)) & v1_relat_1(X1))),
% 1.27/0.52    inference(flattening,[],[f32])).
% 1.27/0.52  fof(f32,plain,(
% 1.27/0.52    ? [X0,X1] : (((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k9_relat_1(X1,X0))) & v1_relat_1(X1))),
% 1.27/0.52    inference(nnf_transformation,[],[f22])).
% 1.27/0.52  fof(f22,plain,(
% 1.27/0.52    ? [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 1.27/0.52    inference(ennf_transformation,[],[f21])).
% 1.27/0.52  fof(f21,negated_conjecture,(
% 1.27/0.52    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 1.27/0.52    inference(negated_conjecture,[],[f20])).
% 1.27/0.52  fof(f20,conjecture,(
% 1.27/0.52    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 1.27/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).
% 1.27/0.52  fof(f277,plain,(
% 1.27/0.52    ~v1_relat_1(sK1) | (spl3_2 | ~spl3_4)),
% 1.27/0.52    inference(subsumption_resolution,[],[f274,f85])).
% 1.27/0.52  fof(f85,plain,(
% 1.27/0.52    ~r1_xboole_0(k1_relat_1(sK1),sK0) | spl3_2),
% 1.27/0.52    inference(avatar_component_clause,[],[f83])).
% 1.27/0.52  fof(f83,plain,(
% 1.27/0.52    spl3_2 <=> r1_xboole_0(k1_relat_1(sK1),sK0)),
% 1.27/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.27/0.52  fof(f274,plain,(
% 1.27/0.52    r1_xboole_0(k1_relat_1(sK1),sK0) | ~v1_relat_1(sK1) | ~spl3_4),
% 1.27/0.52    inference(resolution,[],[f262,f124])).
% 1.27/0.52  fof(f124,plain,(
% 1.27/0.52    ( ! [X0,X1] : (~r1_tarski(k7_relat_1(X0,X1),k1_xboole_0) | r1_xboole_0(k1_relat_1(X0),X1) | ~v1_relat_1(X0)) )),
% 1.27/0.52    inference(subsumption_resolution,[],[f122,f45])).
% 1.27/0.52  fof(f45,plain,(
% 1.27/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f2])).
% 1.27/0.52  fof(f2,axiom,(
% 1.27/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.27/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.27/0.52  fof(f122,plain,(
% 1.27/0.52    ( ! [X0,X1] : (~r1_tarski(k7_relat_1(X0,X1),k1_xboole_0) | ~r1_tarski(k1_xboole_0,k7_relat_1(X0,X1)) | r1_xboole_0(k1_relat_1(X0),X1) | ~v1_relat_1(X0)) )),
% 1.27/0.52    inference(extensionality_resolution,[],[f60,f54])).
% 1.27/0.52  fof(f54,plain,(
% 1.27/0.52    ( ! [X0,X1] : (k1_xboole_0 != k7_relat_1(X1,X0) | r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f36])).
% 1.27/0.52  fof(f36,plain,(
% 1.27/0.52    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.27/0.52    inference(nnf_transformation,[],[f28])).
% 1.27/0.52  fof(f28,plain,(
% 1.27/0.52    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.27/0.52    inference(ennf_transformation,[],[f19])).
% 1.27/0.52  fof(f19,axiom,(
% 1.27/0.52    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 1.27/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).
% 1.27/0.52  fof(f60,plain,(
% 1.27/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f40])).
% 1.27/0.52  fof(f40,plain,(
% 1.27/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.27/0.52    inference(flattening,[],[f39])).
% 1.27/0.52  fof(f39,plain,(
% 1.27/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.27/0.52    inference(nnf_transformation,[],[f1])).
% 1.27/0.52  fof(f1,axiom,(
% 1.27/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.27/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.27/0.52  fof(f262,plain,(
% 1.27/0.52    r1_tarski(k7_relat_1(sK1,sK0),k1_xboole_0) | ~spl3_4),
% 1.27/0.52    inference(avatar_component_clause,[],[f260])).
% 1.27/0.52  fof(f260,plain,(
% 1.27/0.52    spl3_4 <=> r1_tarski(k7_relat_1(sK1,sK0),k1_xboole_0)),
% 1.27/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.27/0.52  fof(f266,plain,(
% 1.27/0.52    spl3_3),
% 1.27/0.52    inference(avatar_contradiction_clause,[],[f265])).
% 1.27/0.52  fof(f265,plain,(
% 1.27/0.52    $false | spl3_3),
% 1.27/0.52    inference(subsumption_resolution,[],[f264,f41])).
% 1.27/0.52  fof(f264,plain,(
% 1.27/0.52    ~v1_relat_1(sK1) | spl3_3),
% 1.27/0.52    inference(resolution,[],[f258,f52])).
% 1.27/0.52  fof(f52,plain,(
% 1.27/0.52    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f26])).
% 1.27/0.52  fof(f26,plain,(
% 1.27/0.52    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.27/0.52    inference(ennf_transformation,[],[f15])).
% 1.27/0.52  fof(f15,axiom,(
% 1.27/0.52    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.27/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.27/0.52  fof(f258,plain,(
% 1.27/0.52    ~v1_relat_1(k7_relat_1(sK1,sK0)) | spl3_3),
% 1.27/0.52    inference(avatar_component_clause,[],[f256])).
% 1.27/0.52  fof(f256,plain,(
% 1.27/0.52    spl3_3 <=> v1_relat_1(k7_relat_1(sK1,sK0))),
% 1.27/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.27/0.52  fof(f263,plain,(
% 1.27/0.52    ~spl3_3 | spl3_4 | ~spl3_1),
% 1.27/0.52    inference(avatar_split_clause,[],[f254,f79,f260,f256])).
% 1.27/0.52  fof(f79,plain,(
% 1.27/0.52    spl3_1 <=> k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 1.27/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.27/0.52  fof(f254,plain,(
% 1.27/0.52    r1_tarski(k7_relat_1(sK1,sK0),k1_xboole_0) | ~v1_relat_1(k7_relat_1(sK1,sK0)) | ~spl3_1),
% 1.27/0.52    inference(forward_demodulation,[],[f251,f113])).
% 1.27/0.52  fof(f113,plain,(
% 1.27/0.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.27/0.52    inference(resolution,[],[f110,f46])).
% 1.27/0.52  fof(f46,plain,(
% 1.27/0.52    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f3])).
% 1.27/0.52  fof(f3,axiom,(
% 1.27/0.52    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.27/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.27/0.52  fof(f110,plain,(
% 1.27/0.52    ( ! [X4,X3] : (~r1_xboole_0(X3,X3) | k1_xboole_0 = k2_zfmisc_1(X4,X3)) )),
% 1.27/0.52    inference(resolution,[],[f65,f48])).
% 1.27/0.52  fof(f48,plain,(
% 1.27/0.52    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 1.27/0.52    inference(cnf_transformation,[],[f23])).
% 1.27/0.52  fof(f23,plain,(
% 1.27/0.52    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 1.27/0.52    inference(ennf_transformation,[],[f4])).
% 1.27/0.52  fof(f4,axiom,(
% 1.27/0.52    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 1.27/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 1.27/0.52  fof(f65,plain,(
% 1.27/0.52    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X2,X3)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f31])).
% 1.27/0.52  fof(f31,plain,(
% 1.27/0.52    ! [X0,X1,X2,X3] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | (~r1_xboole_0(X2,X3) & ~r1_xboole_0(X0,X1)))),
% 1.27/0.52    inference(ennf_transformation,[],[f11])).
% 1.27/0.52  fof(f11,axiom,(
% 1.27/0.52    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 1.27/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).
% 1.27/0.52  fof(f251,plain,(
% 1.27/0.52    r1_tarski(k7_relat_1(sK1,sK0),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK1,sK0)),k1_xboole_0)) | ~v1_relat_1(k7_relat_1(sK1,sK0)) | ~spl3_1),
% 1.27/0.52    inference(superposition,[],[f104,f80])).
% 1.27/0.52  fof(f80,plain,(
% 1.27/0.52    k1_xboole_0 = k9_relat_1(sK1,sK0) | ~spl3_1),
% 1.27/0.52    inference(avatar_component_clause,[],[f79])).
% 1.27/0.52  fof(f104,plain,(
% 1.27/0.52    ( ! [X0] : (r1_tarski(k7_relat_1(sK1,X0),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK1,X0)),k9_relat_1(sK1,X0))) | ~v1_relat_1(k7_relat_1(sK1,X0))) )),
% 1.27/0.52    inference(superposition,[],[f50,f99])).
% 1.27/0.52  fof(f99,plain,(
% 1.27/0.52    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)) )),
% 1.27/0.52    inference(resolution,[],[f53,f41])).
% 1.27/0.52  fof(f53,plain,(
% 1.27/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f27])).
% 1.27/0.52  fof(f27,plain,(
% 1.27/0.52    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.27/0.52    inference(ennf_transformation,[],[f16])).
% 1.27/0.52  fof(f16,axiom,(
% 1.27/0.52    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.27/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 1.27/0.52  fof(f50,plain,(
% 1.27/0.52    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f25])).
% 1.27/0.52  fof(f25,plain,(
% 1.27/0.52    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.27/0.52    inference(ennf_transformation,[],[f18])).
% 1.27/0.52  fof(f18,axiom,(
% 1.27/0.52    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 1.27/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).
% 1.27/0.52  fof(f169,plain,(
% 1.27/0.52    spl3_1 | ~spl3_2),
% 1.27/0.52    inference(avatar_contradiction_clause,[],[f168])).
% 1.27/0.52  fof(f168,plain,(
% 1.27/0.52    $false | (spl3_1 | ~spl3_2)),
% 1.27/0.52    inference(subsumption_resolution,[],[f167,f156])).
% 1.27/0.52  fof(f156,plain,(
% 1.27/0.52    k1_xboole_0 != k2_relat_1(k1_xboole_0) | (spl3_1 | ~spl3_2)),
% 1.27/0.52    inference(superposition,[],[f81,f141])).
% 1.27/0.52  fof(f141,plain,(
% 1.27/0.52    k9_relat_1(sK1,sK0) = k2_relat_1(k1_xboole_0) | ~spl3_2),
% 1.27/0.52    inference(superposition,[],[f99,f140])).
% 1.27/0.52  fof(f140,plain,(
% 1.27/0.52    k1_xboole_0 = k7_relat_1(sK1,sK0) | ~spl3_2),
% 1.27/0.52    inference(subsumption_resolution,[],[f138,f41])).
% 1.27/0.52  fof(f138,plain,(
% 1.27/0.52    k1_xboole_0 = k7_relat_1(sK1,sK0) | ~v1_relat_1(sK1) | ~spl3_2),
% 1.27/0.52    inference(resolution,[],[f55,f84])).
% 1.27/0.52  fof(f84,plain,(
% 1.27/0.52    r1_xboole_0(k1_relat_1(sK1),sK0) | ~spl3_2),
% 1.27/0.52    inference(avatar_component_clause,[],[f83])).
% 1.27/0.52  fof(f55,plain,(
% 1.27/0.52    ( ! [X0,X1] : (~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f36])).
% 1.27/0.52  fof(f81,plain,(
% 1.27/0.52    k1_xboole_0 != k9_relat_1(sK1,sK0) | spl3_1),
% 1.27/0.52    inference(avatar_component_clause,[],[f79])).
% 1.27/0.52  fof(f167,plain,(
% 1.27/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.27/0.52    inference(forward_demodulation,[],[f163,f89])).
% 1.27/0.52  fof(f89,plain,(
% 1.27/0.52    k1_xboole_0 = k9_relat_1(sK1,k1_xboole_0)),
% 1.27/0.52    inference(resolution,[],[f49,f41])).
% 1.27/0.52  fof(f49,plain,(
% 1.27/0.52    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f24])).
% 1.27/0.53  fof(f24,plain,(
% 1.27/0.53    ! [X0] : (k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 1.27/0.53    inference(ennf_transformation,[],[f17])).
% 1.27/0.53  fof(f17,axiom,(
% 1.27/0.53    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0))),
% 1.27/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_relat_1)).
% 1.27/0.53  fof(f163,plain,(
% 1.27/0.53    k9_relat_1(sK1,k1_xboole_0) = k2_relat_1(k1_xboole_0)),
% 1.27/0.53    inference(superposition,[],[f99,f160])).
% 1.27/0.53  % (7912)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.27/0.53  fof(f160,plain,(
% 1.27/0.53    k1_xboole_0 = k7_relat_1(sK1,k1_xboole_0)),
% 1.27/0.53    inference(resolution,[],[f139,f41])).
% 1.27/0.53  fof(f139,plain,(
% 1.27/0.53    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)) )),
% 1.27/0.53    inference(resolution,[],[f55,f46])).
% 1.27/0.53  fof(f87,plain,(
% 1.27/0.53    spl3_1 | spl3_2),
% 1.27/0.53    inference(avatar_split_clause,[],[f42,f83,f79])).
% 1.27/0.53  fof(f42,plain,(
% 1.27/0.53    r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 1.27/0.53    inference(cnf_transformation,[],[f35])).
% 1.27/0.53  fof(f86,plain,(
% 1.27/0.53    ~spl3_1 | ~spl3_2),
% 1.27/0.53    inference(avatar_split_clause,[],[f43,f83,f79])).
% 1.27/0.53  fof(f43,plain,(
% 1.27/0.53    ~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k9_relat_1(sK1,sK0)),
% 1.27/0.53    inference(cnf_transformation,[],[f35])).
% 1.27/0.53  % SZS output end Proof for theBenchmark
% 1.27/0.53  % (7892)------------------------------
% 1.27/0.53  % (7892)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.53  % (7892)Termination reason: Refutation
% 1.27/0.53  
% 1.27/0.53  % (7892)Memory used [KB]: 10874
% 1.27/0.53  % (7892)Time elapsed: 0.112 s
% 1.27/0.53  % (7892)------------------------------
% 1.27/0.53  % (7892)------------------------------
% 1.27/0.53  % (7893)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.27/0.53  % (7885)Success in time 0.168 s
%------------------------------------------------------------------------------
