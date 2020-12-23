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
% DateTime   : Thu Dec  3 12:52:05 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 853 expanded)
%              Number of leaves         :    5 ( 208 expanded)
%              Depth                    :   22
%              Number of atoms          :  153 (3184 expanded)
%              Number of equality atoms :   53 (1160 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f683,plain,(
    $false ),
    inference(global_subsumption,[],[f576,f682])).

% (2149)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
fof(f682,plain,(
    ! [X0] : sP3(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f651,f52])).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = sK6(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f34,f36,f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != k1_xboole_0
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_relat_1(X0) = k1_xboole_0 )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f36,plain,(
    ! [X0,X1] : k1_relat_1(sK6(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    ! [X0,X1] : v1_relat_1(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f651,plain,(
    ! [X0] : sP3(X0,sK6(k1_xboole_0,X0)) ),
    inference(backward_demodulation,[],[f156,f633])).

fof(f633,plain,(
    k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f579])).

fof(f579,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(backward_demodulation,[],[f17,f577])).

fof(f577,plain,(
    k1_xboole_0 = sK0 ),
    inference(backward_demodulation,[],[f233,f554])).

fof(f554,plain,(
    ! [X0] : k1_xboole_0 = k2_relat_1(sK6(sK0,X0)) ),
    inference(unit_resulting_resolution,[],[f34,f35,f218,f543,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( sP3(sK2(X0,X1),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK2(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f543,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(global_subsumption,[],[f524,f527])).

fof(f527,plain,(
    ! [X2,X1] :
      ( ~ sP3(X2,k1_funct_1(k1_xboole_0,X1))
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f218,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k1_xboole_0,X1) = X0
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f33,f52])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK6(X0,X1),X3) = X1
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f524,plain,(
    ! [X2,X1] :
      ( sP3(X1,k1_funct_1(k1_xboole_0,X2))
      | ~ r2_hidden(X2,k1_xboole_0) ) ),
    inference(superposition,[],[f111,f99])).

fof(f111,plain,(
    ! [X0,X1] : sP3(X0,sK6(k2_relat_1(sK6(sK1,X1)),X0)) ),
    inference(unit_resulting_resolution,[],[f48,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( sP3(X1,sK6(X0,X1))
      | ~ r2_hidden(X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | sP3(X1,sK6(X0,X1))
      | ~ r2_hidden(X2,X0) ) ),
    inference(forward_demodulation,[],[f101,f36])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( sP3(X1,sK6(X0,X1))
      | ~ r2_hidden(X2,k1_relat_1(sK6(X0,X1)))
      | ~ r2_hidden(X2,X0) ) ),
    inference(superposition,[],[f39,f33])).

fof(f39,plain,(
    ! [X0,X3] :
      ( sP3(k1_funct_1(X0,X3),X0)
      | ~ r2_hidden(X3,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | sP3(X2,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f48,plain,(
    ! [X0] : r2_hidden(sK5(k2_relat_1(sK6(sK1,X0)),sK0),k2_relat_1(sK6(sK1,X0))) ),
    inference(unit_resulting_resolution,[],[f42,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f42,plain,(
    ! [X0] : ~ r1_tarski(k2_relat_1(sK6(sK1,X0)),sK0) ),
    inference(unit_resulting_resolution,[],[f35,f34,f36,f16])).

fof(f16,plain,(
    ! [X2] :
      ( k1_relat_1(X2) != sK1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),sK0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

fof(f218,plain,(
    ! [X0,X1] : ~ sP3(X0,sK6(sK0,X1)) ),
    inference(unit_resulting_resolution,[],[f151,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(sK6(X0,X1),X2),X0)
      | ~ sP3(X2,sK6(X0,X1)) ) ),
    inference(superposition,[],[f21,f36])).

fof(f21,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK4(X0,X2),k1_relat_1(X0))
      | ~ sP3(X2,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f151,plain,(
    ! [X0] : ~ r2_hidden(X0,sK0) ),
    inference(backward_demodulation,[],[f49,f149])).

fof(f149,plain,(
    ! [X0] : sK5(k2_relat_1(sK6(sK1,X0)),sK0) = X0 ),
    inference(backward_demodulation,[],[f121,f146])).

fof(f146,plain,(
    ! [X0,X1] : k1_funct_1(sK6(sK1,X0),sK4(sK6(sK1,X1),sK5(k2_relat_1(sK6(sK1,X1)),sK0))) = X0 ),
    inference(unit_resulting_resolution,[],[f123,f33])).

fof(f123,plain,(
    ! [X0] : r2_hidden(sK4(sK6(sK1,X0),sK5(k2_relat_1(sK6(sK1,X0)),sK0)),sK1) ),
    inference(forward_demodulation,[],[f122,f36])).

fof(f122,plain,(
    ! [X0] : r2_hidden(sK4(sK6(sK1,X0),sK5(k2_relat_1(sK6(sK1,X0)),sK0)),k1_relat_1(sK6(sK1,X0))) ),
    inference(unit_resulting_resolution,[],[f113,f21])).

fof(f113,plain,(
    ! [X0] : sP3(sK5(k2_relat_1(sK6(sK1,X0)),sK0),sK6(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f34,f35,f48,f37])).

fof(f37,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | sP3(X2,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | sP3(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f121,plain,(
    ! [X0] : sK5(k2_relat_1(sK6(sK1,X0)),sK0) = k1_funct_1(sK6(sK1,X0),sK4(sK6(sK1,X0),sK5(k2_relat_1(sK6(sK1,X0)),sK0))) ),
    inference(unit_resulting_resolution,[],[f113,f22])).

fof(f22,plain,(
    ! [X2,X0] :
      ( k1_funct_1(X0,sK4(X0,X2)) = X2
      | ~ sP3(X2,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f49,plain,(
    ! [X0] : ~ r2_hidden(sK5(k2_relat_1(sK6(sK1,X0)),sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f42,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X0,X1] : v1_funct_1(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f233,plain,(
    ! [X0] : sK0 = k2_relat_1(sK6(sK0,X0)) ),
    inference(unit_resulting_resolution,[],[f34,f35,f151,f218,f25])).

fof(f17,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f9])).

fof(f156,plain,(
    ! [X0] : sP3(X0,sK6(sK1,X0)) ),
    inference(backward_demodulation,[],[f113,f149])).

fof(f576,plain,(
    ! [X0] : ~ sP3(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f556,f52])).

fof(f556,plain,(
    ! [X0,X1] : ~ sP3(X0,sK6(k1_xboole_0,X1)) ),
    inference(unit_resulting_resolution,[],[f543,f58])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:33:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.51  % (2129)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (2138)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (2129)Refutation not found, incomplete strategy% (2129)------------------------------
% 0.20/0.52  % (2129)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (2129)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (2129)Memory used [KB]: 1663
% 0.20/0.52  % (2129)Time elapsed: 0.102 s
% 0.20/0.52  % (2129)------------------------------
% 0.20/0.52  % (2129)------------------------------
% 0.20/0.52  % (2153)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (2136)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (2138)Refutation not found, incomplete strategy% (2138)------------------------------
% 0.20/0.53  % (2138)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (2138)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (2138)Memory used [KB]: 10618
% 0.20/0.53  % (2138)Time elapsed: 0.116 s
% 0.20/0.53  % (2138)------------------------------
% 0.20/0.53  % (2138)------------------------------
% 0.20/0.53  % (2145)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (2154)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (2132)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (2132)Refutation not found, incomplete strategy% (2132)------------------------------
% 0.20/0.53  % (2132)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (2132)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (2132)Memory used [KB]: 10618
% 0.20/0.53  % (2132)Time elapsed: 0.115 s
% 0.20/0.53  % (2132)------------------------------
% 0.20/0.53  % (2132)------------------------------
% 0.20/0.54  % (2159)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (2144)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.54  % (2137)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (2135)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.54  % (2158)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (2133)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (2134)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.54  % (2141)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (2146)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.55  % (2148)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.55  % (2152)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.55  % (2151)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.55  % (2151)Refutation not found, incomplete strategy% (2151)------------------------------
% 0.20/0.55  % (2151)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (2151)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (2151)Memory used [KB]: 1663
% 0.20/0.55  % (2151)Time elapsed: 0.140 s
% 0.20/0.55  % (2151)------------------------------
% 0.20/0.55  % (2151)------------------------------
% 0.20/0.55  % (2152)Refutation not found, incomplete strategy% (2152)------------------------------
% 0.20/0.55  % (2152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (2152)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (2152)Memory used [KB]: 10618
% 0.20/0.55  % (2152)Time elapsed: 0.137 s
% 0.20/0.55  % (2152)------------------------------
% 0.20/0.55  % (2152)------------------------------
% 0.20/0.55  % (2143)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  % (2150)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.55  % (2157)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.55  % (2150)Refutation not found, incomplete strategy% (2150)------------------------------
% 0.20/0.55  % (2150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (2150)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (2150)Memory used [KB]: 10746
% 0.20/0.55  % (2150)Time elapsed: 0.136 s
% 0.20/0.55  % (2150)------------------------------
% 0.20/0.55  % (2150)------------------------------
% 0.20/0.56  % (2154)Refutation found. Thanks to Tanya!
% 0.20/0.56  % SZS status Theorem for theBenchmark
% 0.20/0.56  % (2130)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.56  % (2156)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.56  % SZS output start Proof for theBenchmark
% 0.20/0.56  fof(f683,plain,(
% 0.20/0.56    $false),
% 0.20/0.56    inference(global_subsumption,[],[f576,f682])).
% 0.20/0.56  % (2149)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.56  fof(f682,plain,(
% 0.20/0.56    ( ! [X0] : (sP3(X0,k1_xboole_0)) )),
% 0.20/0.56    inference(forward_demodulation,[],[f651,f52])).
% 0.20/0.56  fof(f52,plain,(
% 0.20/0.56    ( ! [X0] : (k1_xboole_0 = sK6(k1_xboole_0,X0)) )),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f34,f36,f18])).
% 0.20/0.56  fof(f18,plain,(
% 0.20/0.56    ( ! [X0] : (k1_relat_1(X0) != k1_xboole_0 | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.20/0.56    inference(cnf_transformation,[],[f11])).
% 0.20/0.56  fof(f11,plain,(
% 0.20/0.56    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0) | ~v1_relat_1(X0))),
% 0.20/0.56    inference(flattening,[],[f10])).
% 0.20/0.56  fof(f10,plain,(
% 0.20/0.56    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 0.20/0.56    inference(ennf_transformation,[],[f3])).
% 0.20/0.56  fof(f3,axiom,(
% 0.20/0.56    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_relat_1(X0) = k1_xboole_0) => k1_xboole_0 = X0))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.20/0.56  fof(f36,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k1_relat_1(sK6(X0,X1)) = X0) )),
% 0.20/0.56    inference(cnf_transformation,[],[f15])).
% 0.20/0.56  fof(f15,plain,(
% 0.20/0.56    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.20/0.56    inference(ennf_transformation,[],[f5])).
% 0.20/0.56  fof(f5,axiom,(
% 0.20/0.56    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 0.20/0.56  fof(f34,plain,(
% 0.20/0.56    ( ! [X0,X1] : (v1_relat_1(sK6(X0,X1))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f15])).
% 0.20/0.56  fof(f651,plain,(
% 0.20/0.56    ( ! [X0] : (sP3(X0,sK6(k1_xboole_0,X0))) )),
% 0.20/0.56    inference(backward_demodulation,[],[f156,f633])).
% 0.20/0.56  fof(f633,plain,(
% 0.20/0.56    k1_xboole_0 = sK1),
% 0.20/0.56    inference(trivial_inequality_removal,[],[f579])).
% 0.20/0.56  fof(f579,plain,(
% 0.20/0.56    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1),
% 0.20/0.56    inference(backward_demodulation,[],[f17,f577])).
% 0.20/0.56  fof(f577,plain,(
% 0.20/0.56    k1_xboole_0 = sK0),
% 0.20/0.56    inference(backward_demodulation,[],[f233,f554])).
% 0.20/0.56  fof(f554,plain,(
% 0.20/0.56    ( ! [X0] : (k1_xboole_0 = k2_relat_1(sK6(sK0,X0))) )),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f34,f35,f218,f543,f25])).
% 0.20/0.56  fof(f25,plain,(
% 0.20/0.56    ( ! [X0,X1] : (sP3(sK2(X0,X1),X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(sK2(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 0.20/0.56    inference(cnf_transformation,[],[f13])).
% 0.20/0.56  fof(f13,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.56    inference(flattening,[],[f12])).
% 0.20/0.56  fof(f12,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f4])).
% 0.20/0.56  fof(f4,axiom,(
% 0.20/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 0.20/0.56  fof(f543,plain,(
% 0.20/0.56    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 0.20/0.56    inference(global_subsumption,[],[f524,f527])).
% 0.20/0.56  fof(f527,plain,(
% 0.20/0.56    ( ! [X2,X1] : (~sP3(X2,k1_funct_1(k1_xboole_0,X1)) | ~r2_hidden(X1,k1_xboole_0)) )),
% 0.20/0.56    inference(superposition,[],[f218,f99])).
% 0.20/0.56  fof(f99,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k1_funct_1(k1_xboole_0,X1) = X0 | ~r2_hidden(X1,k1_xboole_0)) )),
% 0.20/0.56    inference(superposition,[],[f33,f52])).
% 0.20/0.56  fof(f33,plain,(
% 0.20/0.56    ( ! [X0,X3,X1] : (k1_funct_1(sK6(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f15])).
% 0.20/0.56  fof(f524,plain,(
% 0.20/0.56    ( ! [X2,X1] : (sP3(X1,k1_funct_1(k1_xboole_0,X2)) | ~r2_hidden(X2,k1_xboole_0)) )),
% 0.20/0.56    inference(superposition,[],[f111,f99])).
% 0.20/0.56  fof(f111,plain,(
% 0.20/0.56    ( ! [X0,X1] : (sP3(X0,sK6(k2_relat_1(sK6(sK1,X1)),X0))) )),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f48,f104])).
% 0.20/0.56  fof(f104,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (sP3(X1,sK6(X0,X1)) | ~r2_hidden(X2,X0)) )),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f103])).
% 0.20/0.56  fof(f103,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | sP3(X1,sK6(X0,X1)) | ~r2_hidden(X2,X0)) )),
% 0.20/0.56    inference(forward_demodulation,[],[f101,f36])).
% 0.20/0.56  fof(f101,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (sP3(X1,sK6(X0,X1)) | ~r2_hidden(X2,k1_relat_1(sK6(X0,X1))) | ~r2_hidden(X2,X0)) )),
% 0.20/0.56    inference(superposition,[],[f39,f33])).
% 0.20/0.56  fof(f39,plain,(
% 0.20/0.56    ( ! [X0,X3] : (sP3(k1_funct_1(X0,X3),X0) | ~r2_hidden(X3,k1_relat_1(X0))) )),
% 0.20/0.56    inference(equality_resolution,[],[f20])).
% 0.20/0.56  fof(f20,plain,(
% 0.20/0.56    ( ! [X2,X0,X3] : (~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X0,X3) != X2 | sP3(X2,X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f13])).
% 0.20/0.56  fof(f48,plain,(
% 0.20/0.56    ( ! [X0] : (r2_hidden(sK5(k2_relat_1(sK6(sK1,X0)),sK0),k2_relat_1(sK6(sK1,X0)))) )),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f42,f31])).
% 0.20/0.56  fof(f31,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f14])).
% 0.20/0.56  fof(f14,plain,(
% 0.20/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f1])).
% 0.20/0.56  fof(f1,axiom,(
% 0.20/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.56  fof(f42,plain,(
% 0.20/0.56    ( ! [X0] : (~r1_tarski(k2_relat_1(sK6(sK1,X0)),sK0)) )),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f35,f34,f36,f16])).
% 0.20/0.56  fof(f16,plain,(
% 0.20/0.56    ( ! [X2] : (k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),sK0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f9])).
% 0.20/0.56  fof(f9,plain,(
% 0.20/0.56    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 0.20/0.56    inference(flattening,[],[f8])).
% 0.20/0.56  fof(f8,plain,(
% 0.20/0.56    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 0.20/0.56    inference(ennf_transformation,[],[f7])).
% 0.20/0.56  fof(f7,negated_conjecture,(
% 0.20/0.56    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.20/0.56    inference(negated_conjecture,[],[f6])).
% 0.20/0.56  fof(f6,conjecture,(
% 0.20/0.56    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).
% 0.20/0.56  fof(f218,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~sP3(X0,sK6(sK0,X1))) )),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f151,f58])).
% 0.20/0.56  fof(f58,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (r2_hidden(sK4(sK6(X0,X1),X2),X0) | ~sP3(X2,sK6(X0,X1))) )),
% 0.20/0.56    inference(superposition,[],[f21,f36])).
% 0.20/0.56  fof(f21,plain,(
% 0.20/0.56    ( ! [X2,X0] : (r2_hidden(sK4(X0,X2),k1_relat_1(X0)) | ~sP3(X2,X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f13])).
% 0.20/0.56  fof(f151,plain,(
% 0.20/0.56    ( ! [X0] : (~r2_hidden(X0,sK0)) )),
% 0.20/0.56    inference(backward_demodulation,[],[f49,f149])).
% 0.20/0.56  fof(f149,plain,(
% 0.20/0.56    ( ! [X0] : (sK5(k2_relat_1(sK6(sK1,X0)),sK0) = X0) )),
% 0.20/0.56    inference(backward_demodulation,[],[f121,f146])).
% 0.20/0.56  fof(f146,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k1_funct_1(sK6(sK1,X0),sK4(sK6(sK1,X1),sK5(k2_relat_1(sK6(sK1,X1)),sK0))) = X0) )),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f123,f33])).
% 0.20/0.56  fof(f123,plain,(
% 0.20/0.56    ( ! [X0] : (r2_hidden(sK4(sK6(sK1,X0),sK5(k2_relat_1(sK6(sK1,X0)),sK0)),sK1)) )),
% 0.20/0.56    inference(forward_demodulation,[],[f122,f36])).
% 0.20/0.56  fof(f122,plain,(
% 0.20/0.56    ( ! [X0] : (r2_hidden(sK4(sK6(sK1,X0),sK5(k2_relat_1(sK6(sK1,X0)),sK0)),k1_relat_1(sK6(sK1,X0)))) )),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f113,f21])).
% 0.20/0.56  fof(f113,plain,(
% 0.20/0.56    ( ! [X0] : (sP3(sK5(k2_relat_1(sK6(sK1,X0)),sK0),sK6(sK1,X0))) )),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f34,f35,f48,f37])).
% 0.20/0.56  fof(f37,plain,(
% 0.20/0.56    ( ! [X2,X0] : (~r2_hidden(X2,k2_relat_1(X0)) | ~v1_funct_1(X0) | sP3(X2,X0) | ~v1_relat_1(X0)) )),
% 0.20/0.56    inference(equality_resolution,[],[f24])).
% 0.20/0.56  fof(f24,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | sP3(X2,X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.20/0.56    inference(cnf_transformation,[],[f13])).
% 0.20/0.56  fof(f121,plain,(
% 0.20/0.56    ( ! [X0] : (sK5(k2_relat_1(sK6(sK1,X0)),sK0) = k1_funct_1(sK6(sK1,X0),sK4(sK6(sK1,X0),sK5(k2_relat_1(sK6(sK1,X0)),sK0)))) )),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f113,f22])).
% 0.20/0.56  fof(f22,plain,(
% 0.20/0.56    ( ! [X2,X0] : (k1_funct_1(X0,sK4(X0,X2)) = X2 | ~sP3(X2,X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f13])).
% 0.20/0.56  fof(f49,plain,(
% 0.20/0.56    ( ! [X0] : (~r2_hidden(sK5(k2_relat_1(sK6(sK1,X0)),sK0),sK0)) )),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f42,f32])).
% 0.20/0.56  fof(f32,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f14])).
% 0.20/0.56  fof(f35,plain,(
% 0.20/0.56    ( ! [X0,X1] : (v1_funct_1(sK6(X0,X1))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f15])).
% 0.20/0.56  fof(f233,plain,(
% 0.20/0.56    ( ! [X0] : (sK0 = k2_relat_1(sK6(sK0,X0))) )),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f34,f35,f151,f218,f25])).
% 0.20/0.56  fof(f17,plain,(
% 0.20/0.56    k1_xboole_0 != sK0 | k1_xboole_0 = sK1),
% 0.20/0.56    inference(cnf_transformation,[],[f9])).
% 0.20/0.56  fof(f156,plain,(
% 0.20/0.56    ( ! [X0] : (sP3(X0,sK6(sK1,X0))) )),
% 0.20/0.56    inference(backward_demodulation,[],[f113,f149])).
% 0.20/0.56  fof(f576,plain,(
% 0.20/0.56    ( ! [X0] : (~sP3(X0,k1_xboole_0)) )),
% 0.20/0.56    inference(forward_demodulation,[],[f556,f52])).
% 0.20/0.56  fof(f556,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~sP3(X0,sK6(k1_xboole_0,X1))) )),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f543,f58])).
% 0.20/0.56  % SZS output end Proof for theBenchmark
% 0.20/0.56  % (2154)------------------------------
% 0.20/0.56  % (2154)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (2154)Termination reason: Refutation
% 0.20/0.56  
% 0.20/0.56  % (2154)Memory used [KB]: 6652
% 0.20/0.56  % (2154)Time elapsed: 0.139 s
% 0.20/0.56  % (2154)------------------------------
% 0.20/0.56  % (2154)------------------------------
% 0.20/0.56  % (2128)Success in time 0.197 s
%------------------------------------------------------------------------------
