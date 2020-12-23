%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 208 expanded)
%              Number of leaves         :   16 (  58 expanded)
%              Depth                    :   14
%              Number of atoms          :  154 ( 390 expanded)
%              Number of equality atoms :   47 ( 129 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f97,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f68,f84,f88,f96])).

fof(f96,plain,(
    ~ spl2_3 ),
    inference(avatar_contradiction_clause,[],[f90])).

fof(f90,plain,
    ( $false
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f46,f89])).

fof(f89,plain,
    ( ~ r1_tarski(k11_relat_1(sK1,sK0),k11_relat_1(sK1,sK0))
    | ~ spl2_3 ),
    inference(backward_demodulation,[],[f53,f79])).

fof(f79,plain,
    ( k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) = k11_relat_1(sK1,sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl2_3
  <=> k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) = k11_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f53,plain,(
    ~ r1_tarski(k11_relat_1(sK1,sK0),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
    inference(backward_demodulation,[],[f52,f47])).

fof(f47,plain,(
    ! [X0] : k11_relat_1(sK1,X0) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)) ),
    inference(unit_resulting_resolution,[],[f22,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f34,f40])).

fof(f40,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f35,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f35,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(f22,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_funct_1)).

fof(f52,plain,(
    ~ r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
    inference(backward_demodulation,[],[f41,f48])).

fof(f48,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    inference(unit_resulting_resolution,[],[f22,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f41,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
    inference(definition_unfolding,[],[f24,f40,f40])).

fof(f24,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f46,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f88,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f85])).

fof(f85,plain,
    ( $false
    | spl2_4 ),
    inference(unit_resulting_resolution,[],[f28,f83])).

fof(f83,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl2_4
  <=> r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f28,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f84,plain,
    ( spl2_3
    | ~ spl2_4
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f74,f58,f81,f77])).

fof(f58,plain,
    ( spl2_1
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | k11_relat_1(sK1,X0) = k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f74,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
    | k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) = k11_relat_1(sK1,sK0)
    | ~ spl2_1 ),
    inference(superposition,[],[f53,f73])).

fof(f73,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k11_relat_1(sK1,X0)
        | k11_relat_1(sK1,X0) = k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0)) )
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f72,f32])).

fof(f32,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f72,plain,
    ( ! [X0] :
        ( k2_relat_1(k1_xboole_0) = k11_relat_1(sK1,X0)
        | k11_relat_1(sK1,X0) = k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0)) )
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f71,f47])).

fof(f71,plain,
    ( ! [X0] :
        ( k2_relat_1(k1_xboole_0) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X0))
        | k11_relat_1(sK1,X0) = k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0)) )
    | ~ spl2_1 ),
    inference(superposition,[],[f48,f69])).

fof(f69,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0))
        | k11_relat_1(sK1,X0) = k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0)) )
    | ~ spl2_1 ),
    inference(resolution,[],[f59,f56])).

fof(f56,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_relat_1(sK1))
      | k1_xboole_0 = k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(factoring,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_relat_1(sK1))
      | k1_xboole_0 = k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X1))
      | r2_hidden(X0,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f50,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f39])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | r2_hidden(X2,X1)
      | r1_xboole_0(k2_tarski(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

fof(f50,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(X1,k1_relat_1(sK1))
      | k1_xboole_0 = k7_relat_1(sK1,X1) ) ),
    inference(resolution,[],[f22,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | k1_xboole_0 = k7_relat_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

fof(f59,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | k11_relat_1(sK1,X0) = k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0)) )
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f68,plain,(
    spl2_2 ),
    inference(avatar_contradiction_clause,[],[f65])).

fof(f65,plain,
    ( $false
    | spl2_2 ),
    inference(unit_resulting_resolution,[],[f22,f63])).

fof(f63,plain,
    ( ~ v1_relat_1(sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl2_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f64,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f54,f61,f58])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK1)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | k11_relat_1(sK1,X0) = k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0)) ) ),
    inference(resolution,[],[f23,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k11_relat_1(X1,X0) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) ) ),
    inference(definition_unfolding,[],[f29,f40])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

fof(f23,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:23:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.45  % (14591)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.50  % (14598)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.50  % (14614)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.50  % (14614)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f97,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f64,f68,f84,f88,f96])).
% 0.20/0.50  fof(f96,plain,(
% 0.20/0.50    ~spl2_3),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f90])).
% 0.20/0.50  fof(f90,plain,(
% 0.20/0.50    $false | ~spl2_3),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f46,f89])).
% 0.20/0.50  fof(f89,plain,(
% 0.20/0.50    ~r1_tarski(k11_relat_1(sK1,sK0),k11_relat_1(sK1,sK0)) | ~spl2_3),
% 0.20/0.50    inference(backward_demodulation,[],[f53,f79])).
% 0.20/0.50  fof(f79,plain,(
% 0.20/0.50    k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) = k11_relat_1(sK1,sK0) | ~spl2_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f77])).
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    spl2_3 <=> k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) = k11_relat_1(sK1,sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    ~r1_tarski(k11_relat_1(sK1,sK0),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))),
% 0.20/0.50    inference(backward_demodulation,[],[f52,f47])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ( ! [X0] : (k11_relat_1(sK1,X0) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X0))) )),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f22,f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 0.20/0.50    inference(definition_unfolding,[],[f34,f40])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f35,f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f37,f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    v1_relat_1(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.50    inference(flattening,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))))),
% 0.20/0.50    inference(negated_conjecture,[],[f12])).
% 0.20/0.50  fof(f12,conjecture,(
% 0.20/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_funct_1)).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ~r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))),
% 0.20/0.50    inference(backward_demodulation,[],[f41,f48])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)) )),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f22,f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))),
% 0.20/0.50    inference(definition_unfolding,[],[f24,f40,f40])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.50    inference(equality_resolution,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.50  fof(f88,plain,(
% 0.20/0.50    spl2_4),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f85])).
% 0.20/0.50  fof(f85,plain,(
% 0.20/0.50    $false | spl2_4),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f28,f83])).
% 0.20/0.50  fof(f83,plain,(
% 0.20/0.50    ~r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) | spl2_4),
% 0.20/0.50    inference(avatar_component_clause,[],[f81])).
% 0.20/0.50  fof(f81,plain,(
% 0.20/0.50    spl2_4 <=> r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.50  fof(f84,plain,(
% 0.20/0.50    spl2_3 | ~spl2_4 | ~spl2_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f74,f58,f81,f77])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    spl2_1 <=> ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k11_relat_1(sK1,X0) = k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.50  fof(f74,plain,(
% 0.20/0.50    ~r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) | k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) = k11_relat_1(sK1,sK0) | ~spl2_1),
% 0.20/0.50    inference(superposition,[],[f53,f73])).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    ( ! [X0] : (k1_xboole_0 = k11_relat_1(sK1,X0) | k11_relat_1(sK1,X0) = k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0))) ) | ~spl2_1),
% 0.20/0.50    inference(forward_demodulation,[],[f72,f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.50    inference(cnf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,axiom,(
% 0.20/0.50    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    ( ! [X0] : (k2_relat_1(k1_xboole_0) = k11_relat_1(sK1,X0) | k11_relat_1(sK1,X0) = k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0))) ) | ~spl2_1),
% 0.20/0.50    inference(forward_demodulation,[],[f71,f47])).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    ( ! [X0] : (k2_relat_1(k1_xboole_0) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)) | k11_relat_1(sK1,X0) = k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0))) ) | ~spl2_1),
% 0.20/0.50    inference(superposition,[],[f48,f69])).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    ( ! [X0] : (k1_xboole_0 = k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)) | k11_relat_1(sK1,X0) = k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0))) ) | ~spl2_1),
% 0.20/0.50    inference(resolution,[],[f59,f56])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    ( ! [X0] : (r2_hidden(X0,k1_relat_1(sK1)) | k1_xboole_0 = k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0))) )),
% 0.20/0.50    inference(factoring,[],[f55])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r2_hidden(X1,k1_relat_1(sK1)) | k1_xboole_0 = k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X1)) | r2_hidden(X0,k1_relat_1(sK1))) )),
% 0.20/0.50    inference(resolution,[],[f50,f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f36,f39])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | r2_hidden(X2,X1) | r1_xboole_0(k2_tarski(X0,X2),X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ~(~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    ( ! [X1] : (~r1_xboole_0(X1,k1_relat_1(sK1)) | k1_xboole_0 = k7_relat_1(sK1,X1)) )),
% 0.20/0.50    inference(resolution,[],[f22,f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r1_xboole_0(X1,k1_relat_1(X0)) | k1_xboole_0 = k7_relat_1(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).
% 0.20/0.50  fof(f59,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k11_relat_1(sK1,X0) = k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0))) ) | ~spl2_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f58])).
% 0.20/0.50  fof(f68,plain,(
% 0.20/0.50    spl2_2),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f65])).
% 0.20/0.50  fof(f65,plain,(
% 0.20/0.50    $false | spl2_2),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f22,f63])).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    ~v1_relat_1(sK1) | spl2_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f61])).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    spl2_2 <=> v1_relat_1(sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.50  fof(f64,plain,(
% 0.20/0.50    spl2_1 | ~spl2_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f54,f61,f58])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_relat_1(sK1) | ~r2_hidden(X0,k1_relat_1(sK1)) | k11_relat_1(sK1,X0) = k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0))) )),
% 0.20/0.50    inference(resolution,[],[f23,f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | k11_relat_1(X1,X0) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))) )),
% 0.20/0.50    inference(definition_unfolding,[],[f29,f40])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0,X1] : (k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(flattening,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0,X1] : ((k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,axiom,(
% 0.20/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    v1_funct_1(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (14614)------------------------------
% 0.20/0.50  % (14614)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (14614)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (14614)Memory used [KB]: 6268
% 0.20/0.50  % (14614)Time elapsed: 0.111 s
% 0.20/0.50  % (14614)------------------------------
% 0.20/0.50  % (14614)------------------------------
% 0.20/0.50  % (14583)Success in time 0.148 s
%------------------------------------------------------------------------------
