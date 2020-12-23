%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 608 expanded)
%              Number of leaves         :    8 ( 154 expanded)
%              Depth                    :   16
%              Number of atoms          :  144 (2211 expanded)
%              Number of equality atoms :   44 ( 791 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f225,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f132,f224])).

fof(f224,plain,(
    ~ spl8_1 ),
    inference(avatar_contradiction_clause,[],[f218])).

fof(f218,plain,
    ( $false
    | ~ spl8_1 ),
    inference(unit_resulting_resolution,[],[f158,f146,f167,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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

fof(f167,plain,
    ( ! [X0] : r2_hidden(sK4(sK6(k1_xboole_0,X0),X0),k1_xboole_0)
    | ~ spl8_1 ),
    inference(backward_demodulation,[],[f98,f44])).

fof(f44,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl8_1
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f98,plain,(
    ! [X0] : r2_hidden(sK4(sK6(sK1,X0),X0),sK1) ),
    inference(backward_demodulation,[],[f89,f95])).

fof(f95,plain,(
    ! [X0] : sK2(k2_relat_1(sK6(sK1,X0)),sK0) = X0 ),
    inference(backward_demodulation,[],[f82,f90])).

fof(f90,plain,(
    ! [X0,X1] : k1_funct_1(sK6(sK1,X0),sK4(sK6(sK1,X1),sK2(k2_relat_1(sK6(sK1,X1)),sK0))) = X0 ),
    inference(unit_resulting_resolution,[],[f89,f30])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | k1_funct_1(sK6(X0,X1),X3) = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f82,plain,(
    ! [X0] : sK2(k2_relat_1(sK6(sK1,X0)),sK0) = k1_funct_1(sK6(sK1,X0),sK4(sK6(sK1,X0),sK2(k2_relat_1(sK6(sK1,X0)),sK0))) ),
    inference(unit_resulting_resolution,[],[f32,f31,f76,f39])).

fof(f39,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_funct_1(X0,sK4(X0,X2)) = X2
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK4(X0,X2)) = X2
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(f76,plain,(
    ! [X0] : r2_hidden(sK2(k2_relat_1(sK6(sK1,X0)),sK0),k2_relat_1(sK6(sK1,X0))) ),
    inference(unit_resulting_resolution,[],[f74,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f74,plain,(
    ! [X0] : ~ r1_tarski(k2_relat_1(sK6(sK1,X0)),sK0) ),
    inference(unit_resulting_resolution,[],[f31,f32,f33,f16])).

fof(f16,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_relat_1(X2),sK0)
      | ~ v1_funct_1(X2)
      | k1_relat_1(X2) != sK1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

fof(f33,plain,(
    ! [X0,X1] : k1_relat_1(sK6(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0,X1] : v1_relat_1(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0,X1] : v1_funct_1(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f89,plain,(
    ! [X0] : r2_hidden(sK4(sK6(sK1,X0),sK2(k2_relat_1(sK6(sK1,X0)),sK0)),sK1) ),
    inference(forward_demodulation,[],[f81,f33])).

fof(f81,plain,(
    ! [X0] : r2_hidden(sK4(sK6(sK1,X0),sK2(k2_relat_1(sK6(sK1,X0)),sK0)),k1_relat_1(sK6(sK1,X0))) ),
    inference(unit_resulting_resolution,[],[f32,f31,f76,f40])).

fof(f40,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK4(X0,X2),k1_relat_1(X0))
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK4(X0,X2),k1_relat_1(X0))
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f146,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f101,f111])).

fof(f111,plain,(
    k1_xboole_0 = sK0 ),
    inference(unit_resulting_resolution,[],[f101,f34])).

fof(f34,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f101,plain,(
    ! [X0] : ~ r2_hidden(X0,sK0) ),
    inference(backward_demodulation,[],[f77,f95])).

fof(f77,plain,(
    ! [X0] : ~ r2_hidden(sK2(k2_relat_1(sK6(sK1,X0)),sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f74,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f158,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f110,f111])).

fof(f110,plain,(
    ! [X0] : r1_tarski(sK0,X0) ),
    inference(unit_resulting_resolution,[],[f101,f19])).

fof(f132,plain,(
    spl8_2 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f36,f101,f55])).

fof(f55,plain,
    ( ! [X1] :
        ( r2_hidden(sK7(sK0),X1)
        | ~ r1_tarski(sK0,X1) )
    | spl8_2 ),
    inference(resolution,[],[f50,f18])).

fof(f50,plain,
    ( r2_hidden(sK7(sK0),sK0)
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f48,f34])).

fof(f48,plain,
    ( k1_xboole_0 != sK0
    | spl8_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl8_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f36,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f49,plain,
    ( spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f17,f46,f42])).

fof(f17,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:59:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (4687)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (4711)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.48  % (4687)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (4682)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.50  % (4691)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.50  % (4695)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (4682)Refutation not found, incomplete strategy% (4682)------------------------------
% 0.21/0.50  % (4682)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (4682)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (4682)Memory used [KB]: 1663
% 0.21/0.50  % (4682)Time elapsed: 0.098 s
% 0.21/0.50  % (4682)------------------------------
% 0.21/0.50  % (4682)------------------------------
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f225,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f49,f132,f224])).
% 0.21/0.50  fof(f224,plain,(
% 0.21/0.50    ~spl8_1),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f218])).
% 0.21/0.50  fof(f218,plain,(
% 0.21/0.50    $false | ~spl8_1),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f158,f146,f167,f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.50  fof(f167,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(sK4(sK6(k1_xboole_0,X0),X0),k1_xboole_0)) ) | ~spl8_1),
% 0.21/0.50    inference(backward_demodulation,[],[f98,f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    k1_xboole_0 = sK1 | ~spl8_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    spl8_1 <=> k1_xboole_0 = sK1),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(sK4(sK6(sK1,X0),X0),sK1)) )),
% 0.21/0.50    inference(backward_demodulation,[],[f89,f95])).
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    ( ! [X0] : (sK2(k2_relat_1(sK6(sK1,X0)),sK0) = X0) )),
% 0.21/0.50    inference(backward_demodulation,[],[f82,f90])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_funct_1(sK6(sK1,X0),sK4(sK6(sK1,X1),sK2(k2_relat_1(sK6(sK1,X1)),sK0))) = X0) )),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f89,f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | k1_funct_1(sK6(X0,X1),X3) = X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    ( ! [X0] : (sK2(k2_relat_1(sK6(sK1,X0)),sK0) = k1_funct_1(sK6(sK1,X0),sK4(sK6(sK1,X0),sK2(k2_relat_1(sK6(sK1,X0)),sK0)))) )),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f32,f31,f76,f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X2,X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_funct_1(X0,sK4(X0,X2)) = X2 | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 0.21/0.50    inference(equality_resolution,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK4(X0,X2)) = X2 | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(sK2(k2_relat_1(sK6(sK1,X0)),sK0),k2_relat_1(sK6(sK1,X0)))) )),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f74,f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(k2_relat_1(sK6(sK1,X0)),sK0)) )),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f31,f32,f33,f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ( ! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | ~v1_funct_1(X2) | k1_relat_1(X2) != sK1 | ~v1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 0.21/0.50    inference(flattening,[],[f9])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.21/0.50    inference(negated_conjecture,[],[f7])).
% 0.21/0.50  fof(f7,conjecture,(
% 0.21/0.50    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_relat_1(sK6(X0,X1)) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_relat_1(sK6(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_funct_1(sK6(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(sK4(sK6(sK1,X0),sK2(k2_relat_1(sK6(sK1,X0)),sK0)),sK1)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f81,f33])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(sK4(sK6(sK1,X0),sK2(k2_relat_1(sK6(sK1,X0)),sK0)),k1_relat_1(sK6(sK1,X0)))) )),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f32,f31,f76,f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X2,X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(sK4(X0,X2),k1_relat_1(X0)) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 0.21/0.50    inference(equality_resolution,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK4(X0,X2),k1_relat_1(X0)) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f146,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.50    inference(backward_demodulation,[],[f101,f111])).
% 0.21/0.50  fof(f111,plain,(
% 0.21/0.50    k1_xboole_0 = sK0),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f101,f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(sK7(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,sK0)) )),
% 0.21/0.50    inference(backward_demodulation,[],[f77,f95])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(sK2(k2_relat_1(sK6(sK1,X0)),sK0),sK0)) )),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f74,f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f158,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f110,f111])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(sK0,X0)) )),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f101,f19])).
% 0.21/0.50  fof(f132,plain,(
% 0.21/0.50    spl8_2),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f120])).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    $false | spl8_2),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f36,f101,f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X1] : (r2_hidden(sK7(sK0),X1) | ~r1_tarski(sK0,X1)) ) | spl8_2),
% 0.21/0.50    inference(resolution,[],[f50,f18])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    r2_hidden(sK7(sK0),sK0) | spl8_2),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f48,f34])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    k1_xboole_0 != sK0 | spl8_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    spl8_2 <=> k1_xboole_0 = sK0),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.50    inference(equality_resolution,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    spl8_1 | ~spl8_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f17,f46,f42])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    k1_xboole_0 != sK0 | k1_xboole_0 = sK1),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (4687)------------------------------
% 0.21/0.50  % (4687)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (4687)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (4687)Memory used [KB]: 6268
% 0.21/0.50  % (4687)Time elapsed: 0.095 s
% 0.21/0.50  % (4687)------------------------------
% 0.21/0.50  % (4687)------------------------------
% 0.21/0.50  % (4681)Success in time 0.14 s
%------------------------------------------------------------------------------
