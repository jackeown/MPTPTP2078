%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   61 (1038 expanded)
%              Number of leaves         :    6 ( 258 expanded)
%              Depth                    :   21
%              Number of atoms          :  146 (3803 expanded)
%              Number of equality atoms :   52 (1384 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f307,plain,(
    $false ),
    inference(global_subsumption,[],[f172,f306])).

fof(f306,plain,(
    ! [X0] : r2_hidden(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f305,f214])).

% (18013)Termination reason: Refutation not found, incomplete strategy
fof(f214,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f53,f52,f172,f187,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( sP3(sK2(X0,X1),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK2(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f13])).

% (18013)Memory used [KB]: 10618
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

% (18013)Time elapsed: 0.134 s
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

% (18013)------------------------------
% (18013)------------------------------
fof(f187,plain,(
    ! [X0] : ~ sP3(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f171,f75])).

fof(f75,plain,(
    ! [X8,X9] :
      ( r2_hidden(sK4(k1_xboole_0,X8),X9)
      | ~ sP3(X8,k1_xboole_0) ) ),
    inference(global_subsumption,[],[f18,f74])).

fof(f74,plain,(
    ! [X8,X9] :
      ( r2_hidden(sK4(k1_xboole_0,X8),X9)
      | ~ r1_tarski(k1_xboole_0,X9)
      | ~ sP3(X8,k1_xboole_0) ) ),
    inference(resolution,[],[f28,f66])).

fof(f66,plain,(
    ! [X3] :
      ( r2_hidden(sK4(k1_xboole_0,X3),k1_xboole_0)
      | ~ sP3(X3,k1_xboole_0) ) ),
    inference(superposition,[],[f22,f51])).

fof(f51,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f34,f48])).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = sK6(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f32,f34,f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f32,plain,(
    ! [X0,X1] : v1_relat_1(sK6(X0,X1)) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f34,plain,(
    ! [X0,X1] : k1_relat_1(sK6(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f22,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK4(X0,X2),k1_relat_1(X0))
      | ~ sP3(X2,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f18,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f171,plain,(
    ! [X0] : ~ r2_hidden(X0,sK0) ),
    inference(backward_demodulation,[],[f45,f169])).

fof(f169,plain,(
    ! [X0] : sK5(k2_relat_1(sK6(sK1,X0)),sK0) = X0 ),
    inference(backward_demodulation,[],[f134,f166])).

fof(f166,plain,(
    ! [X0,X1] : k1_funct_1(sK6(sK1,X0),sK4(sK6(sK1,X1),sK5(k2_relat_1(sK6(sK1,X1)),sK0))) = X0 ),
    inference(unit_resulting_resolution,[],[f136,f31])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK6(X0,X1),X3) = X1
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f136,plain,(
    ! [X0] : r2_hidden(sK4(sK6(sK1,X0),sK5(k2_relat_1(sK6(sK1,X0)),sK0)),sK1) ),
    inference(forward_demodulation,[],[f135,f34])).

fof(f135,plain,(
    ! [X0] : r2_hidden(sK4(sK6(sK1,X0),sK5(k2_relat_1(sK6(sK1,X0)),sK0)),k1_relat_1(sK6(sK1,X0))) ),
    inference(unit_resulting_resolution,[],[f123,f22])).

fof(f123,plain,(
    ! [X0] : sP3(sK5(k2_relat_1(sK6(sK1,X0)),sK0),sK6(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f32,f33,f44,f35])).

fof(f35,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | sP3(X2,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | sP3(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f44,plain,(
    ! [X0] : r2_hidden(sK5(k2_relat_1(sK6(sK1,X0)),sK0),k2_relat_1(sK6(sK1,X0))) ),
    inference(unit_resulting_resolution,[],[f38,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X0] : ~ r1_tarski(k2_relat_1(sK6(sK1,X0)),sK0) ),
    inference(unit_resulting_resolution,[],[f33,f32,f34,f16])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

fof(f33,plain,(
    ! [X0,X1] : v1_funct_1(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f134,plain,(
    ! [X0] : sK5(k2_relat_1(sK6(sK1,X0)),sK0) = k1_funct_1(sK6(sK1,X0),sK4(sK6(sK1,X0),sK5(k2_relat_1(sK6(sK1,X0)),sK0))) ),
    inference(unit_resulting_resolution,[],[f123,f23])).

fof(f23,plain,(
    ! [X2,X0] :
      ( k1_funct_1(X0,sK4(X0,X2)) = X2
      | ~ sP3(X2,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f45,plain,(
    ! [X0] : ~ r2_hidden(sK5(k2_relat_1(sK6(sK1,X0)),sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f38,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f52,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f33,f48])).

fof(f53,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f32,f48])).

fof(f305,plain,(
    ! [X0] : r2_hidden(X0,k2_relat_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f250,f48])).

fof(f250,plain,(
    ! [X0] : r2_hidden(X0,k2_relat_1(sK6(k1_xboole_0,X0))) ),
    inference(backward_demodulation,[],[f170,f228])).

fof(f228,plain,(
    k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f220])).

fof(f220,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(backward_demodulation,[],[f17,f218])).

fof(f218,plain,(
    k1_xboole_0 = sK0 ),
    inference(forward_demodulation,[],[f213,f214])).

fof(f213,plain,(
    sK0 = k2_relat_1(k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f53,f52,f171,f187,f26])).

fof(f17,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f9])).

fof(f170,plain,(
    ! [X0] : r2_hidden(X0,k2_relat_1(sK6(sK1,X0))) ),
    inference(backward_demodulation,[],[f44,f169])).

fof(f172,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f67,f169])).

fof(f67,plain,(
    ! [X0] : ~ r2_hidden(sK5(k2_relat_1(sK6(sK1,X0)),sK0),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f18,f45,f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:58:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (18009)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.50  % (17994)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.50  % (18000)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.50  % (17996)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (17996)Refutation not found, incomplete strategy% (17996)------------------------------
% 0.21/0.51  % (17996)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (18015)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.51  % (17996)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (17996)Memory used [KB]: 10618
% 0.21/0.51  % (17996)Time elapsed: 0.098 s
% 0.21/0.51  % (17996)------------------------------
% 0.21/0.51  % (17996)------------------------------
% 0.21/0.51  % (18019)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (17997)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (18014)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.51  % (17998)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (17994)Refutation not found, incomplete strategy% (17994)------------------------------
% 0.21/0.51  % (17994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (17994)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (17994)Memory used [KB]: 1663
% 0.21/0.51  % (17994)Time elapsed: 0.099 s
% 0.21/0.51  % (17994)------------------------------
% 0.21/0.51  % (17994)------------------------------
% 0.21/0.51  % (18023)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.52  % (18005)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (18008)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (18020)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.52  % (18018)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (18005)Refutation not found, incomplete strategy% (18005)------------------------------
% 0.21/0.52  % (18005)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (18005)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  % (18002)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  
% 0.21/0.52  % (18005)Memory used [KB]: 10618
% 0.21/0.52  % (18005)Time elapsed: 0.110 s
% 0.21/0.52  % (18005)------------------------------
% 0.21/0.52  % (18005)------------------------------
% 0.21/0.52  % (18007)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (17999)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (18022)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.52  % (17995)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (18021)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.52  % (18012)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (18002)Refutation not found, incomplete strategy% (18002)------------------------------
% 0.21/0.53  % (18002)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (18024)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (18002)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (18002)Memory used [KB]: 10618
% 0.21/0.53  % (18002)Time elapsed: 0.122 s
% 0.21/0.53  % (18002)------------------------------
% 0.21/0.53  % (18002)------------------------------
% 0.21/0.53  % (18011)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (18025)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (18017)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (18017)Refutation not found, incomplete strategy% (18017)------------------------------
% 0.21/0.53  % (18017)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (18017)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (18017)Memory used [KB]: 1663
% 0.21/0.53  % (18017)Time elapsed: 0.122 s
% 0.21/0.53  % (18017)------------------------------
% 0.21/0.53  % (18017)------------------------------
% 0.21/0.53  % (18016)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (18010)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (18004)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (18004)Refutation not found, incomplete strategy% (18004)------------------------------
% 0.21/0.54  % (18004)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (18004)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (18004)Memory used [KB]: 10618
% 0.21/0.54  % (18004)Time elapsed: 0.132 s
% 0.21/0.54  % (18004)------------------------------
% 0.21/0.54  % (18004)------------------------------
% 0.21/0.54  % (18001)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (18018)Refutation not found, incomplete strategy% (18018)------------------------------
% 0.21/0.54  % (18018)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (18013)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (18013)Refutation not found, incomplete strategy% (18013)------------------------------
% 0.21/0.54  % (18013)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (18020)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f307,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(global_subsumption,[],[f172,f306])).
% 0.21/0.54  fof(f306,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f305,f214])).
% 0.21/0.54  % (18013)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  fof(f214,plain,(
% 0.21/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f53,f52,f172,f187,f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ( ! [X0,X1] : (sP3(sK2(X0,X1),X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(sK2(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  
% 0.21/0.54  % (18013)Memory used [KB]: 10618
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f12])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  % (18013)Time elapsed: 0.134 s
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 0.21/0.54  % (18013)------------------------------
% 0.21/0.54  % (18013)------------------------------
% 0.21/0.54  fof(f187,plain,(
% 0.21/0.54    ( ! [X0] : (~sP3(X0,k1_xboole_0)) )),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f171,f75])).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    ( ! [X8,X9] : (r2_hidden(sK4(k1_xboole_0,X8),X9) | ~sP3(X8,k1_xboole_0)) )),
% 0.21/0.54    inference(global_subsumption,[],[f18,f74])).
% 0.21/0.54  fof(f74,plain,(
% 0.21/0.54    ( ! [X8,X9] : (r2_hidden(sK4(k1_xboole_0,X8),X9) | ~r1_tarski(k1_xboole_0,X9) | ~sP3(X8,k1_xboole_0)) )),
% 0.21/0.54    inference(resolution,[],[f28,f66])).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    ( ! [X3] : (r2_hidden(sK4(k1_xboole_0,X3),k1_xboole_0) | ~sP3(X3,k1_xboole_0)) )),
% 0.21/0.54    inference(superposition,[],[f22,f51])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.54    inference(superposition,[],[f34,f48])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = sK6(k1_xboole_0,X0)) )),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f32,f34,f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,plain,(
% 0.21/0.54    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f10])).
% 0.21/0.54  fof(f10,plain,(
% 0.21/0.54    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_relat_1(sK6(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.54    inference(ennf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_relat_1(sK6(X0,X1)) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ( ! [X2,X0] : (r2_hidden(sK4(X0,X2),k1_relat_1(X0)) | ~sP3(X2,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.54  fof(f171,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,sK0)) )),
% 0.21/0.54    inference(backward_demodulation,[],[f45,f169])).
% 0.21/0.54  fof(f169,plain,(
% 0.21/0.54    ( ! [X0] : (sK5(k2_relat_1(sK6(sK1,X0)),sK0) = X0) )),
% 0.21/0.54    inference(backward_demodulation,[],[f134,f166])).
% 0.21/0.54  fof(f166,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_funct_1(sK6(sK1,X0),sK4(sK6(sK1,X1),sK5(k2_relat_1(sK6(sK1,X1)),sK0))) = X0) )),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f136,f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ( ! [X0,X3,X1] : (k1_funct_1(sK6(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f136,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(sK4(sK6(sK1,X0),sK5(k2_relat_1(sK6(sK1,X0)),sK0)),sK1)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f135,f34])).
% 0.21/0.54  fof(f135,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(sK4(sK6(sK1,X0),sK5(k2_relat_1(sK6(sK1,X0)),sK0)),k1_relat_1(sK6(sK1,X0)))) )),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f123,f22])).
% 0.21/0.54  fof(f123,plain,(
% 0.21/0.54    ( ! [X0] : (sP3(sK5(k2_relat_1(sK6(sK1,X0)),sK0),sK6(sK1,X0))) )),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f32,f33,f44,f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ( ! [X2,X0] : (~r2_hidden(X2,k2_relat_1(X0)) | ~v1_funct_1(X0) | sP3(X2,X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | sP3(X2,X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(sK5(k2_relat_1(sK6(sK1,X0)),sK0),k2_relat_1(sK6(sK1,X0)))) )),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f38,f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_tarski(k2_relat_1(sK6(sK1,X0)),sK0)) )),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f33,f32,f34,f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ( ! [X2] : (k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),sK0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,plain,(
% 0.21/0.54    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 0.21/0.54    inference(flattening,[],[f8])).
% 0.21/0.54  fof(f8,plain,(
% 0.21/0.54    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.21/0.54    inference(negated_conjecture,[],[f6])).
% 0.21/0.54  fof(f6,conjecture,(
% 0.21/0.54    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_funct_1(sK6(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f134,plain,(
% 0.21/0.54    ( ! [X0] : (sK5(k2_relat_1(sK6(sK1,X0)),sK0) = k1_funct_1(sK6(sK1,X0),sK4(sK6(sK1,X0),sK5(k2_relat_1(sK6(sK1,X0)),sK0)))) )),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f123,f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ( ! [X2,X0] : (k1_funct_1(X0,sK4(X0,X2)) = X2 | ~sP3(X2,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(sK5(k2_relat_1(sK6(sK1,X0)),sK0),sK0)) )),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f38,f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    v1_funct_1(k1_xboole_0)),
% 0.21/0.54    inference(superposition,[],[f33,f48])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    v1_relat_1(k1_xboole_0)),
% 0.21/0.54    inference(superposition,[],[f32,f48])).
% 0.21/0.54  fof(f305,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(X0,k2_relat_1(k1_xboole_0))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f250,f48])).
% 0.21/0.54  fof(f250,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(X0,k2_relat_1(sK6(k1_xboole_0,X0)))) )),
% 0.21/0.54    inference(backward_demodulation,[],[f170,f228])).
% 0.21/0.54  fof(f228,plain,(
% 0.21/0.54    k1_xboole_0 = sK1),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f220])).
% 0.21/0.54  fof(f220,plain,(
% 0.21/0.54    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1),
% 0.21/0.54    inference(backward_demodulation,[],[f17,f218])).
% 0.21/0.54  fof(f218,plain,(
% 0.21/0.54    k1_xboole_0 = sK0),
% 0.21/0.54    inference(forward_demodulation,[],[f213,f214])).
% 0.21/0.54  fof(f213,plain,(
% 0.21/0.54    sK0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f53,f52,f171,f187,f26])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    k1_xboole_0 != sK0 | k1_xboole_0 = sK1),
% 0.21/0.54    inference(cnf_transformation,[],[f9])).
% 0.21/0.54  fof(f170,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(X0,k2_relat_1(sK6(sK1,X0)))) )),
% 0.21/0.54    inference(backward_demodulation,[],[f44,f169])).
% 0.21/0.54  fof(f172,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.54    inference(backward_demodulation,[],[f67,f169])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(sK5(k2_relat_1(sK6(sK1,X0)),sK0),k1_xboole_0)) )),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f18,f45,f28])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (18020)------------------------------
% 0.21/0.54  % (18020)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (18020)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (18020)Memory used [KB]: 6396
% 0.21/0.54  % (18020)Time elapsed: 0.090 s
% 0.21/0.54  % (18020)------------------------------
% 0.21/0.54  % (18020)------------------------------
% 0.21/0.55  % (17991)Success in time 0.182 s
%------------------------------------------------------------------------------
