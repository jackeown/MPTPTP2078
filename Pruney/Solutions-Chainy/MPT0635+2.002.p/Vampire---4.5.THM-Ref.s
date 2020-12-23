%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 116 expanded)
%              Number of leaves         :   19 (  43 expanded)
%              Depth                    :    8
%              Number of atoms          :  181 ( 275 expanded)
%              Number of equality atoms :   42 (  76 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f104,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f60,f65,f70,f89,f93,f97,f100,f103])).

fof(f103,plain,
    ( ~ spl5_3
    | spl5_8 ),
    inference(avatar_contradiction_clause,[],[f101])).

fof(f101,plain,
    ( $false
    | ~ spl5_3
    | spl5_8 ),
    inference(unit_resulting_resolution,[],[f44,f64,f88,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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

fof(f88,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl5_8
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f64,plain,
    ( r2_hidden(sK0,k1_setfam_1(k2_enumset1(sK1,sK1,sK1,k1_relat_1(sK2))))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl5_3
  <=> r2_hidden(sK0,k1_setfam_1(k2_enumset1(sK1,sK1,sK1,k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f28,f42])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f30,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f31,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f100,plain,
    ( ~ spl5_5
    | ~ spl5_8
    | ~ spl5_6
    | spl5_7 ),
    inference(avatar_split_clause,[],[f99,f82,f78,f86,f74])).

fof(f74,plain,
    ( spl5_5
  <=> v1_relat_1(k6_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f78,plain,
    ( spl5_6
  <=> v1_funct_1(k6_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f82,plain,
    ( spl5_7
  <=> k1_funct_1(sK2,sK0) = k1_funct_1(sK2,k1_funct_1(k6_relat_1(sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f99,plain,
    ( ~ v1_funct_1(k6_relat_1(sK1))
    | ~ r2_hidden(sK0,sK1)
    | ~ v1_relat_1(k6_relat_1(sK1))
    | spl5_7 ),
    inference(trivial_inequality_removal,[],[f98])).

fof(f98,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(sK2,sK0)
    | ~ v1_funct_1(k6_relat_1(sK1))
    | ~ r2_hidden(sK0,sK1)
    | ~ v1_relat_1(k6_relat_1(sK1))
    | spl5_7 ),
    inference(superposition,[],[f84,f47])).

fof(f47,plain,(
    ! [X2,X0] :
      ( k1_funct_1(k6_relat_1(X0),X2) = X2
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ r2_hidden(X2,X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X2,X0)
      | k1_funct_1(X1,X2) = X2
      | k6_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

fof(f84,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(sK2,k1_funct_1(k6_relat_1(sK1),sK0))
    | spl5_7 ),
    inference(avatar_component_clause,[],[f82])).

fof(f97,plain,(
    spl5_6 ),
    inference(avatar_contradiction_clause,[],[f94])).

fof(f94,plain,
    ( $false
    | spl5_6 ),
    inference(unit_resulting_resolution,[],[f25,f80])).

fof(f80,plain,
    ( ~ v1_funct_1(k6_relat_1(sK1))
    | spl5_6 ),
    inference(avatar_component_clause,[],[f78])).

fof(f25,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f93,plain,(
    spl5_5 ),
    inference(avatar_contradiction_clause,[],[f90])).

fof(f90,plain,
    ( $false
    | spl5_5 ),
    inference(unit_resulting_resolution,[],[f24,f76])).

fof(f76,plain,
    ( ~ v1_relat_1(k6_relat_1(sK1))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f74])).

fof(f24,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f89,plain,
    ( ~ spl5_5
    | ~ spl5_2
    | ~ spl5_1
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | spl5_4 ),
    inference(avatar_split_clause,[],[f72,f67,f86,f82,f78,f52,f57,f74])).

fof(f57,plain,
    ( spl5_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f52,plain,
    ( spl5_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f67,plain,
    ( spl5_4
  <=> k1_funct_1(sK2,sK0) = k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f72,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_funct_1(sK2,sK0) != k1_funct_1(sK2,k1_funct_1(k6_relat_1(sK1),sK0))
    | ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(k6_relat_1(sK1))
    | spl5_4 ),
    inference(forward_demodulation,[],[f71,f26])).

fof(f26,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f71,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(sK2,k1_funct_1(k6_relat_1(sK1),sK0))
    | ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ r2_hidden(sK0,k1_relat_1(k6_relat_1(sK1)))
    | ~ v1_relat_1(k6_relat_1(sK1))
    | spl5_4 ),
    inference(superposition,[],[f69,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

fof(f69,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f70,plain,(
    ~ spl5_4 ),
    inference(avatar_split_clause,[],[f23,f67])).

fof(f23,plain,(
    k1_funct_1(sK2,sK0) != k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
         => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
       => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_1)).

fof(f65,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f50,f62])).

fof(f50,plain,(
    r2_hidden(sK0,k1_setfam_1(k2_enumset1(sK1,sK1,sK1,k1_relat_1(sK2)))) ),
    inference(forward_demodulation,[],[f43,f45])).

fof(f45,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f29,f41,f41])).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f43,plain,(
    r2_hidden(sK0,k1_setfam_1(k2_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),sK1))) ),
    inference(definition_unfolding,[],[f22,f42])).

fof(f22,plain,(
    r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f60,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f21,f57])).

fof(f21,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f55,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f20,f52])).

fof(f20,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.21/0.35  % WCLimit    : 600
% 0.21/0.35  % DateTime   : Tue Dec  1 17:58:06 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.22/0.53  % (6302)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (6293)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (6283)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (6308)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (6292)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.54  % (6285)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (6302)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f104,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f55,f60,f65,f70,f89,f93,f97,f100,f103])).
% 0.22/0.54  fof(f103,plain,(
% 0.22/0.54    ~spl5_3 | spl5_8),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f101])).
% 0.22/0.54  fof(f101,plain,(
% 0.22/0.54    $false | (~spl5_3 | spl5_8)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f44,f64,f88,f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.54  fof(f88,plain,(
% 0.22/0.54    ~r2_hidden(sK0,sK1) | spl5_8),
% 0.22/0.54    inference(avatar_component_clause,[],[f86])).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    spl5_8 <=> r2_hidden(sK0,sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.22/0.54  fof(f64,plain,(
% 0.22/0.54    r2_hidden(sK0,k1_setfam_1(k2_enumset1(sK1,sK1,sK1,k1_relat_1(sK2)))) | ~spl5_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f62])).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    spl5_3 <=> r2_hidden(sK0,k1_setfam_1(k2_enumset1(sK1,sK1,sK1,k1_relat_1(sK2))))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f28,f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f30,f41])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f31,f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.22/0.54  fof(f100,plain,(
% 0.22/0.54    ~spl5_5 | ~spl5_8 | ~spl5_6 | spl5_7),
% 0.22/0.54    inference(avatar_split_clause,[],[f99,f82,f78,f86,f74])).
% 0.22/0.54  fof(f74,plain,(
% 0.22/0.54    spl5_5 <=> v1_relat_1(k6_relat_1(sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.54  fof(f78,plain,(
% 0.22/0.54    spl5_6 <=> v1_funct_1(k6_relat_1(sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.54  fof(f82,plain,(
% 0.22/0.54    spl5_7 <=> k1_funct_1(sK2,sK0) = k1_funct_1(sK2,k1_funct_1(k6_relat_1(sK1),sK0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.54  fof(f99,plain,(
% 0.22/0.54    ~v1_funct_1(k6_relat_1(sK1)) | ~r2_hidden(sK0,sK1) | ~v1_relat_1(k6_relat_1(sK1)) | spl5_7),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f98])).
% 0.22/0.54  fof(f98,plain,(
% 0.22/0.54    k1_funct_1(sK2,sK0) != k1_funct_1(sK2,sK0) | ~v1_funct_1(k6_relat_1(sK1)) | ~r2_hidden(sK0,sK1) | ~v1_relat_1(k6_relat_1(sK1)) | spl5_7),
% 0.22/0.54    inference(superposition,[],[f84,f47])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ( ! [X2,X0] : (k1_funct_1(k6_relat_1(X0),X2) = X2 | ~v1_funct_1(k6_relat_1(X0)) | ~r2_hidden(X2,X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.54    inference(equality_resolution,[],[f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r2_hidden(X2,X0) | k1_funct_1(X1,X2) = X2 | k6_relat_1(X0) != X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(flattening,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).
% 0.22/0.54  fof(f84,plain,(
% 0.22/0.54    k1_funct_1(sK2,sK0) != k1_funct_1(sK2,k1_funct_1(k6_relat_1(sK1),sK0)) | spl5_7),
% 0.22/0.54    inference(avatar_component_clause,[],[f82])).
% 0.22/0.54  fof(f97,plain,(
% 0.22/0.54    spl5_6),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f94])).
% 0.22/0.54  fof(f94,plain,(
% 0.22/0.54    $false | spl5_6),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f25,f80])).
% 0.22/0.54  fof(f80,plain,(
% 0.22/0.54    ~v1_funct_1(k6_relat_1(sK1)) | spl5_6),
% 0.22/0.54    inference(avatar_component_clause,[],[f78])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.22/0.54  fof(f93,plain,(
% 0.22/0.54    spl5_5),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f90])).
% 0.22/0.54  fof(f90,plain,(
% 0.22/0.54    $false | spl5_5),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f24,f76])).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    ~v1_relat_1(k6_relat_1(sK1)) | spl5_5),
% 0.22/0.54    inference(avatar_component_clause,[],[f74])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f8])).
% 0.22/0.54  fof(f89,plain,(
% 0.22/0.54    ~spl5_5 | ~spl5_2 | ~spl5_1 | ~spl5_6 | ~spl5_7 | ~spl5_8 | spl5_4),
% 0.22/0.54    inference(avatar_split_clause,[],[f72,f67,f86,f82,f78,f52,f57,f74])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    spl5_2 <=> v1_funct_1(sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    spl5_1 <=> v1_relat_1(sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.54  fof(f67,plain,(
% 0.22/0.54    spl5_4 <=> k1_funct_1(sK2,sK0) = k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    ~r2_hidden(sK0,sK1) | k1_funct_1(sK2,sK0) != k1_funct_1(sK2,k1_funct_1(k6_relat_1(sK1),sK0)) | ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(k6_relat_1(sK1)) | spl5_4),
% 0.22/0.54    inference(forward_demodulation,[],[f71,f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.54  fof(f71,plain,(
% 0.22/0.54    k1_funct_1(sK2,sK0) != k1_funct_1(sK2,k1_funct_1(k6_relat_1(sK1),sK0)) | ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~r2_hidden(sK0,k1_relat_1(k6_relat_1(sK1))) | ~v1_relat_1(k6_relat_1(sK1)) | spl5_4),
% 0.22/0.54    inference(superposition,[],[f69,f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(flattening,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    k1_funct_1(sK2,sK0) != k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0) | spl5_4),
% 0.22/0.54    inference(avatar_component_clause,[],[f67])).
% 0.22/0.54  fof(f70,plain,(
% 0.22/0.54    ~spl5_4),
% 0.22/0.54    inference(avatar_split_clause,[],[f23,f67])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    k1_funct_1(sK2,sK0) != k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.22/0.54    inference(flattening,[],[f13])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ? [X0,X1,X2] : ((k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.22/0.54    inference(ennf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)))),
% 0.22/0.54    inference(negated_conjecture,[],[f11])).
% 0.22/0.54  fof(f11,conjecture,(
% 0.22/0.54    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_1)).
% 0.22/0.54  fof(f65,plain,(
% 0.22/0.54    spl5_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f50,f62])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    r2_hidden(sK0,k1_setfam_1(k2_enumset1(sK1,sK1,sK1,k1_relat_1(sK2))))),
% 0.22/0.54    inference(forward_demodulation,[],[f43,f45])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f29,f41,f41])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    r2_hidden(sK0,k1_setfam_1(k2_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),sK1)))),
% 0.22/0.54    inference(definition_unfolding,[],[f22,f42])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))),
% 0.22/0.54    inference(cnf_transformation,[],[f14])).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    spl5_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f21,f57])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    v1_funct_1(sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f14])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    spl5_1),
% 0.22/0.54    inference(avatar_split_clause,[],[f20,f52])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    v1_relat_1(sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f14])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (6302)------------------------------
% 0.22/0.54  % (6302)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (6302)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (6302)Memory used [KB]: 10746
% 0.22/0.54  % (6302)Time elapsed: 0.079 s
% 0.22/0.54  % (6302)------------------------------
% 0.22/0.54  % (6302)------------------------------
% 0.22/0.54  % (6284)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (6310)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (6280)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (6286)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (6281)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (6298)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.54  % (6280)Refutation not found, incomplete strategy% (6280)------------------------------
% 0.22/0.54  % (6280)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (6280)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (6280)Memory used [KB]: 10618
% 0.22/0.54  % (6280)Time elapsed: 0.124 s
% 0.22/0.54  % (6280)------------------------------
% 0.22/0.54  % (6280)------------------------------
% 0.22/0.55  % (6276)Success in time 0.179 s
%------------------------------------------------------------------------------
