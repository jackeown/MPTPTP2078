%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:11 EST 2020

% Result     : Theorem 1.47s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 322 expanded)
%              Number of leaves         :    7 (  80 expanded)
%              Depth                    :   19
%              Number of atoms          :  153 (1158 expanded)
%              Number of equality atoms :   48 ( 405 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f296,plain,(
    $false ),
    inference(global_subsumption,[],[f192,f295])).

fof(f295,plain,(
    ! [X0] : r2_hidden(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f294,f92])).

fof(f92,plain,(
    ! [X0] : k1_xboole_0 = k2_relat_1(sK7(k1_xboole_0,X0)) ),
    inference(unit_resulting_resolution,[],[f34,f36,f21])).

% (1961)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f36,plain,(
    ! [X0,X1] : k1_relat_1(sK7(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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

fof(f34,plain,(
    ! [X0,X1] : v1_relat_1(sK7(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f294,plain,(
    ! [X0] : r2_hidden(X0,k2_relat_1(sK7(k1_xboole_0,X0))) ),
    inference(forward_demodulation,[],[f246,f92])).

fof(f246,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_relat_1(sK7(k2_relat_1(sK7(k1_xboole_0,X1)),X0))) ),
    inference(backward_demodulation,[],[f164,f229])).

fof(f229,plain,(
    k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f220])).

fof(f220,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(backward_demodulation,[],[f18,f205])).

fof(f205,plain,(
    k1_xboole_0 = sK0 ),
    inference(unit_resulting_resolution,[],[f191,f29])).

fof(f29,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f191,plain,(
    ! [X0] : ~ r2_hidden(X0,sK0) ),
    inference(backward_demodulation,[],[f47,f189])).

fof(f189,plain,(
    ! [X0] : sK6(k2_relat_1(sK7(sK1,X0)),sK0) = X0 ),
    inference(backward_demodulation,[],[f158,f186])).

fof(f186,plain,(
    ! [X0,X1] : k1_funct_1(sK7(sK1,X0),sK4(sK7(sK1,X1),sK6(k2_relat_1(sK7(sK1,X1)),sK0))) = X0 ),
    inference(unit_resulting_resolution,[],[f160,f33])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK7(X0,X1),X3) = X1
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f160,plain,(
    ! [X0] : r2_hidden(sK4(sK7(sK1,X0),sK6(k2_relat_1(sK7(sK1,X0)),sK0)),sK1) ),
    inference(forward_demodulation,[],[f159,f36])).

fof(f159,plain,(
    ! [X0] : r2_hidden(sK4(sK7(sK1,X0),sK6(k2_relat_1(sK7(sK1,X0)),sK0)),k1_relat_1(sK7(sK1,X0))) ),
    inference(unit_resulting_resolution,[],[f144,f23])).

fof(f23,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK4(X0,X2),k1_relat_1(X0))
      | ~ sP3(X2,X0) ) ),
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

fof(f144,plain,(
    ! [X0] : sP3(sK6(k2_relat_1(sK7(sK1,X0)),sK0),sK7(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f34,f35,f46,f37])).

fof(f37,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | sP3(X2,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | sP3(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f46,plain,(
    ! [X0] : r2_hidden(sK6(k2_relat_1(sK7(sK1,X0)),sK0),k2_relat_1(sK7(sK1,X0))) ),
    inference(unit_resulting_resolution,[],[f40,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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

fof(f40,plain,(
    ! [X0] : ~ r1_tarski(k2_relat_1(sK7(sK1,X0)),sK0) ),
    inference(unit_resulting_resolution,[],[f35,f34,f36,f17])).

fof(f17,plain,(
    ! [X2] :
      ( k1_relat_1(X2) != sK1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),sK0) ) ),
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

fof(f35,plain,(
    ! [X0,X1] : v1_funct_1(sK7(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f158,plain,(
    ! [X0] : sK6(k2_relat_1(sK7(sK1,X0)),sK0) = k1_funct_1(sK7(sK1,X0),sK4(sK7(sK1,X0),sK6(k2_relat_1(sK7(sK1,X0)),sK0))) ),
    inference(unit_resulting_resolution,[],[f144,f24])).

fof(f24,plain,(
    ! [X2,X0] :
      ( k1_funct_1(X0,sK4(X0,X2)) = X2
      | ~ sP3(X2,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f47,plain,(
    ! [X0] : ~ r2_hidden(sK6(k2_relat_1(sK7(sK1,X0)),sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f40,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f18,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f10])).

fof(f164,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_relat_1(sK7(k2_relat_1(sK7(sK1,X1)),X0))) ),
    inference(unit_resulting_resolution,[],[f34,f143,f35,f38])).

fof(f38,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ sP3(X2,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ sP3(X2,X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f143,plain,(
    ! [X0,X1] : sP3(X0,sK7(k2_relat_1(sK7(sK1,X1)),X0)) ),
    inference(unit_resulting_resolution,[],[f63,f129])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( sP3(X1,sK7(X0,X1))
      | ~ r2_hidden(X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | sP3(X1,sK7(X0,X1))
      | ~ r2_hidden(X2,X0) ) ),
    inference(forward_demodulation,[],[f126,f36])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( sP3(X1,sK7(X0,X1))
      | ~ r2_hidden(X2,k1_relat_1(sK7(X0,X1)))
      | ~ r2_hidden(X2,X0) ) ),
    inference(superposition,[],[f39,f33])).

fof(f39,plain,(
    ! [X0,X3] :
      ( sP3(k1_funct_1(X0,X3),X0)
      | ~ r2_hidden(X3,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | sP3(X2,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f63,plain,(
    ! [X0] : r2_hidden(sK6(k2_relat_1(sK7(sK1,X0)),k1_xboole_0),k2_relat_1(sK7(sK1,X0))) ),
    inference(unit_resulting_resolution,[],[f61,f31])).

fof(f61,plain,(
    ! [X0] : ~ r1_tarski(k2_relat_1(sK7(sK1,X0)),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f46,f51,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f51,plain,(
    ! [X0] : ~ r2_hidden(sK6(k2_relat_1(sK7(sK1,X0)),sK0),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f19,f47,f30])).

fof(f19,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f192,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f51,f189])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:00:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 1.27/0.55  % (1957)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.47/0.56  % (1973)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.47/0.56  % (1957)Refutation not found, incomplete strategy% (1957)------------------------------
% 1.47/0.56  % (1957)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (1971)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.47/0.57  % (1965)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.47/0.57  % (1957)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.57  
% 1.47/0.57  % (1957)Memory used [KB]: 10618
% 1.47/0.57  % (1957)Time elapsed: 0.134 s
% 1.47/0.57  % (1957)------------------------------
% 1.47/0.57  % (1957)------------------------------
% 1.47/0.57  % (1963)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.47/0.57  % (1979)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.47/0.57  % (1963)Refutation not found, incomplete strategy% (1963)------------------------------
% 1.47/0.57  % (1963)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.57  % (1969)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.47/0.57  % (1965)Refutation not found, incomplete strategy% (1965)------------------------------
% 1.47/0.57  % (1965)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.58  % (1965)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.58  
% 1.47/0.58  % (1965)Memory used [KB]: 10618
% 1.47/0.58  % (1965)Time elapsed: 0.147 s
% 1.47/0.58  % (1965)------------------------------
% 1.47/0.58  % (1965)------------------------------
% 1.47/0.58  % (1955)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.47/0.58  % (1955)Refutation not found, incomplete strategy% (1955)------------------------------
% 1.47/0.58  % (1955)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.58  % (1955)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.58  
% 1.47/0.58  % (1955)Memory used [KB]: 1663
% 1.47/0.58  % (1955)Time elapsed: 0.151 s
% 1.47/0.58  % (1955)------------------------------
% 1.47/0.58  % (1955)------------------------------
% 1.47/0.58  % (1979)Refutation found. Thanks to Tanya!
% 1.47/0.58  % SZS status Theorem for theBenchmark
% 1.47/0.58  % (1963)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.59  
% 1.47/0.59  % (1963)Memory used [KB]: 10618
% 1.47/0.59  % (1963)Time elapsed: 0.151 s
% 1.47/0.59  % (1963)------------------------------
% 1.47/0.59  % (1963)------------------------------
% 1.47/0.59  % (1956)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.47/0.59  % SZS output start Proof for theBenchmark
% 1.47/0.59  fof(f296,plain,(
% 1.47/0.59    $false),
% 1.47/0.59    inference(global_subsumption,[],[f192,f295])).
% 1.47/0.59  fof(f295,plain,(
% 1.47/0.59    ( ! [X0] : (r2_hidden(X0,k1_xboole_0)) )),
% 1.47/0.59    inference(forward_demodulation,[],[f294,f92])).
% 1.47/0.59  fof(f92,plain,(
% 1.47/0.59    ( ! [X0] : (k1_xboole_0 = k2_relat_1(sK7(k1_xboole_0,X0))) )),
% 1.47/0.59    inference(unit_resulting_resolution,[],[f34,f36,f21])).
% 1.47/0.59  % (1961)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.47/0.59  fof(f21,plain,(
% 1.47/0.59    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.47/0.59    inference(cnf_transformation,[],[f11])).
% 1.47/0.59  fof(f11,plain,(
% 1.47/0.59    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.47/0.59    inference(ennf_transformation,[],[f4])).
% 1.47/0.59  fof(f4,axiom,(
% 1.47/0.59    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 1.47/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 1.47/0.59  fof(f36,plain,(
% 1.47/0.59    ( ! [X0,X1] : (k1_relat_1(sK7(X0,X1)) = X0) )),
% 1.47/0.59    inference(cnf_transformation,[],[f16])).
% 1.47/0.59  fof(f16,plain,(
% 1.47/0.59    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.47/0.59    inference(ennf_transformation,[],[f6])).
% 1.47/0.59  fof(f6,axiom,(
% 1.47/0.59    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.47/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 1.47/0.59  fof(f34,plain,(
% 1.47/0.59    ( ! [X0,X1] : (v1_relat_1(sK7(X0,X1))) )),
% 1.47/0.59    inference(cnf_transformation,[],[f16])).
% 1.47/0.59  fof(f294,plain,(
% 1.47/0.59    ( ! [X0] : (r2_hidden(X0,k2_relat_1(sK7(k1_xboole_0,X0)))) )),
% 1.47/0.59    inference(forward_demodulation,[],[f246,f92])).
% 1.47/0.59  fof(f246,plain,(
% 1.47/0.59    ( ! [X0,X1] : (r2_hidden(X0,k2_relat_1(sK7(k2_relat_1(sK7(k1_xboole_0,X1)),X0)))) )),
% 1.47/0.59    inference(backward_demodulation,[],[f164,f229])).
% 1.47/0.59  fof(f229,plain,(
% 1.47/0.59    k1_xboole_0 = sK1),
% 1.47/0.59    inference(trivial_inequality_removal,[],[f220])).
% 1.47/0.59  fof(f220,plain,(
% 1.47/0.59    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1),
% 1.47/0.59    inference(backward_demodulation,[],[f18,f205])).
% 1.47/0.59  fof(f205,plain,(
% 1.47/0.59    k1_xboole_0 = sK0),
% 1.47/0.59    inference(unit_resulting_resolution,[],[f191,f29])).
% 1.47/0.59  fof(f29,plain,(
% 1.47/0.59    ( ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0) )),
% 1.47/0.59    inference(cnf_transformation,[],[f14])).
% 1.47/0.59  fof(f14,plain,(
% 1.47/0.59    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.47/0.59    inference(ennf_transformation,[],[f2])).
% 1.47/0.59  fof(f2,axiom,(
% 1.47/0.59    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.47/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.47/0.59  fof(f191,plain,(
% 1.47/0.59    ( ! [X0] : (~r2_hidden(X0,sK0)) )),
% 1.47/0.59    inference(backward_demodulation,[],[f47,f189])).
% 1.47/0.59  fof(f189,plain,(
% 1.47/0.59    ( ! [X0] : (sK6(k2_relat_1(sK7(sK1,X0)),sK0) = X0) )),
% 1.47/0.59    inference(backward_demodulation,[],[f158,f186])).
% 1.47/0.59  fof(f186,plain,(
% 1.47/0.59    ( ! [X0,X1] : (k1_funct_1(sK7(sK1,X0),sK4(sK7(sK1,X1),sK6(k2_relat_1(sK7(sK1,X1)),sK0))) = X0) )),
% 1.47/0.59    inference(unit_resulting_resolution,[],[f160,f33])).
% 1.47/0.59  fof(f33,plain,(
% 1.47/0.59    ( ! [X0,X3,X1] : (k1_funct_1(sK7(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) )),
% 1.47/0.59    inference(cnf_transformation,[],[f16])).
% 1.47/0.59  fof(f160,plain,(
% 1.47/0.59    ( ! [X0] : (r2_hidden(sK4(sK7(sK1,X0),sK6(k2_relat_1(sK7(sK1,X0)),sK0)),sK1)) )),
% 1.47/0.59    inference(forward_demodulation,[],[f159,f36])).
% 1.47/0.59  fof(f159,plain,(
% 1.47/0.59    ( ! [X0] : (r2_hidden(sK4(sK7(sK1,X0),sK6(k2_relat_1(sK7(sK1,X0)),sK0)),k1_relat_1(sK7(sK1,X0)))) )),
% 1.47/0.59    inference(unit_resulting_resolution,[],[f144,f23])).
% 1.47/0.59  fof(f23,plain,(
% 1.47/0.59    ( ! [X2,X0] : (r2_hidden(sK4(X0,X2),k1_relat_1(X0)) | ~sP3(X2,X0)) )),
% 1.47/0.59    inference(cnf_transformation,[],[f13])).
% 1.47/0.59  fof(f13,plain,(
% 1.47/0.59    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.47/0.59    inference(flattening,[],[f12])).
% 1.47/0.59  fof(f12,plain,(
% 1.47/0.59    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.47/0.59    inference(ennf_transformation,[],[f5])).
% 1.47/0.59  fof(f5,axiom,(
% 1.47/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.47/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 1.47/0.59  fof(f144,plain,(
% 1.47/0.59    ( ! [X0] : (sP3(sK6(k2_relat_1(sK7(sK1,X0)),sK0),sK7(sK1,X0))) )),
% 1.47/0.59    inference(unit_resulting_resolution,[],[f34,f35,f46,f37])).
% 1.47/0.59  fof(f37,plain,(
% 1.47/0.59    ( ! [X2,X0] : (~r2_hidden(X2,k2_relat_1(X0)) | ~v1_funct_1(X0) | sP3(X2,X0) | ~v1_relat_1(X0)) )),
% 1.47/0.59    inference(equality_resolution,[],[f26])).
% 1.47/0.59  fof(f26,plain,(
% 1.47/0.59    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | sP3(X2,X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.47/0.59    inference(cnf_transformation,[],[f13])).
% 1.47/0.59  fof(f46,plain,(
% 1.47/0.59    ( ! [X0] : (r2_hidden(sK6(k2_relat_1(sK7(sK1,X0)),sK0),k2_relat_1(sK7(sK1,X0)))) )),
% 1.47/0.59    inference(unit_resulting_resolution,[],[f40,f31])).
% 1.47/0.59  fof(f31,plain,(
% 1.47/0.59    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.47/0.59    inference(cnf_transformation,[],[f15])).
% 1.47/0.59  fof(f15,plain,(
% 1.47/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.47/0.59    inference(ennf_transformation,[],[f1])).
% 1.47/0.59  fof(f1,axiom,(
% 1.47/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.47/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.47/0.59  fof(f40,plain,(
% 1.47/0.59    ( ! [X0] : (~r1_tarski(k2_relat_1(sK7(sK1,X0)),sK0)) )),
% 1.47/0.59    inference(unit_resulting_resolution,[],[f35,f34,f36,f17])).
% 1.47/0.59  fof(f17,plain,(
% 1.47/0.59    ( ! [X2] : (k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),sK0)) )),
% 1.47/0.59    inference(cnf_transformation,[],[f10])).
% 1.47/0.59  fof(f10,plain,(
% 1.47/0.59    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.47/0.59    inference(flattening,[],[f9])).
% 1.47/0.59  fof(f9,plain,(
% 1.47/0.59    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.47/0.59    inference(ennf_transformation,[],[f8])).
% 1.47/0.59  fof(f8,negated_conjecture,(
% 1.47/0.59    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.47/0.59    inference(negated_conjecture,[],[f7])).
% 1.47/0.59  fof(f7,conjecture,(
% 1.47/0.59    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.47/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).
% 1.47/0.59  fof(f35,plain,(
% 1.47/0.59    ( ! [X0,X1] : (v1_funct_1(sK7(X0,X1))) )),
% 1.47/0.59    inference(cnf_transformation,[],[f16])).
% 1.47/0.59  fof(f158,plain,(
% 1.47/0.59    ( ! [X0] : (sK6(k2_relat_1(sK7(sK1,X0)),sK0) = k1_funct_1(sK7(sK1,X0),sK4(sK7(sK1,X0),sK6(k2_relat_1(sK7(sK1,X0)),sK0)))) )),
% 1.47/0.59    inference(unit_resulting_resolution,[],[f144,f24])).
% 1.47/0.59  fof(f24,plain,(
% 1.47/0.59    ( ! [X2,X0] : (k1_funct_1(X0,sK4(X0,X2)) = X2 | ~sP3(X2,X0)) )),
% 1.47/0.59    inference(cnf_transformation,[],[f13])).
% 1.47/0.59  fof(f47,plain,(
% 1.47/0.59    ( ! [X0] : (~r2_hidden(sK6(k2_relat_1(sK7(sK1,X0)),sK0),sK0)) )),
% 1.47/0.59    inference(unit_resulting_resolution,[],[f40,f32])).
% 1.47/0.59  fof(f32,plain,(
% 1.47/0.59    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.47/0.59    inference(cnf_transformation,[],[f15])).
% 1.47/0.59  fof(f18,plain,(
% 1.47/0.59    k1_xboole_0 != sK0 | k1_xboole_0 = sK1),
% 1.47/0.59    inference(cnf_transformation,[],[f10])).
% 1.47/0.59  fof(f164,plain,(
% 1.47/0.59    ( ! [X0,X1] : (r2_hidden(X0,k2_relat_1(sK7(k2_relat_1(sK7(sK1,X1)),X0)))) )),
% 1.47/0.59    inference(unit_resulting_resolution,[],[f34,f143,f35,f38])).
% 1.47/0.59  fof(f38,plain,(
% 1.47/0.59    ( ! [X2,X0] : (r2_hidden(X2,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~sP3(X2,X0) | ~v1_relat_1(X0)) )),
% 1.47/0.59    inference(equality_resolution,[],[f25])).
% 1.47/0.59  fof(f25,plain,(
% 1.47/0.59    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~sP3(X2,X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.47/0.59    inference(cnf_transformation,[],[f13])).
% 1.47/0.59  fof(f143,plain,(
% 1.47/0.59    ( ! [X0,X1] : (sP3(X0,sK7(k2_relat_1(sK7(sK1,X1)),X0))) )),
% 1.47/0.59    inference(unit_resulting_resolution,[],[f63,f129])).
% 1.47/0.59  fof(f129,plain,(
% 1.47/0.59    ( ! [X2,X0,X1] : (sP3(X1,sK7(X0,X1)) | ~r2_hidden(X2,X0)) )),
% 1.47/0.59    inference(duplicate_literal_removal,[],[f128])).
% 1.47/0.59  fof(f128,plain,(
% 1.47/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | sP3(X1,sK7(X0,X1)) | ~r2_hidden(X2,X0)) )),
% 1.47/0.59    inference(forward_demodulation,[],[f126,f36])).
% 1.47/0.59  fof(f126,plain,(
% 1.47/0.59    ( ! [X2,X0,X1] : (sP3(X1,sK7(X0,X1)) | ~r2_hidden(X2,k1_relat_1(sK7(X0,X1))) | ~r2_hidden(X2,X0)) )),
% 1.47/0.59    inference(superposition,[],[f39,f33])).
% 1.47/0.59  fof(f39,plain,(
% 1.47/0.59    ( ! [X0,X3] : (sP3(k1_funct_1(X0,X3),X0) | ~r2_hidden(X3,k1_relat_1(X0))) )),
% 1.47/0.59    inference(equality_resolution,[],[f22])).
% 1.47/0.59  fof(f22,plain,(
% 1.47/0.59    ( ! [X2,X0,X3] : (~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X0,X3) != X2 | sP3(X2,X0)) )),
% 1.47/0.59    inference(cnf_transformation,[],[f13])).
% 1.47/0.59  fof(f63,plain,(
% 1.47/0.59    ( ! [X0] : (r2_hidden(sK6(k2_relat_1(sK7(sK1,X0)),k1_xboole_0),k2_relat_1(sK7(sK1,X0)))) )),
% 1.47/0.59    inference(unit_resulting_resolution,[],[f61,f31])).
% 1.47/0.59  fof(f61,plain,(
% 1.47/0.59    ( ! [X0] : (~r1_tarski(k2_relat_1(sK7(sK1,X0)),k1_xboole_0)) )),
% 1.47/0.59    inference(unit_resulting_resolution,[],[f46,f51,f30])).
% 1.47/0.59  fof(f30,plain,(
% 1.47/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.47/0.59    inference(cnf_transformation,[],[f15])).
% 1.47/0.59  fof(f51,plain,(
% 1.47/0.59    ( ! [X0] : (~r2_hidden(sK6(k2_relat_1(sK7(sK1,X0)),sK0),k1_xboole_0)) )),
% 1.47/0.59    inference(unit_resulting_resolution,[],[f19,f47,f30])).
% 1.47/0.59  fof(f19,plain,(
% 1.47/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.47/0.59    inference(cnf_transformation,[],[f3])).
% 1.47/0.59  fof(f3,axiom,(
% 1.47/0.59    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.47/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.47/0.59  fof(f192,plain,(
% 1.47/0.59    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.47/0.59    inference(backward_demodulation,[],[f51,f189])).
% 1.47/0.59  % SZS output end Proof for theBenchmark
% 1.47/0.59  % (1979)------------------------------
% 1.47/0.59  % (1979)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.59  % (1979)Termination reason: Refutation
% 1.47/0.59  
% 1.47/0.59  % (1979)Memory used [KB]: 6396
% 1.47/0.59  % (1979)Time elapsed: 0.156 s
% 1.47/0.59  % (1979)------------------------------
% 1.47/0.59  % (1979)------------------------------
% 1.47/0.59  % (1958)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.47/0.59  % (1954)Success in time 0.232 s
%------------------------------------------------------------------------------
