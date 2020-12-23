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
% DateTime   : Thu Dec  3 12:52:07 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.13s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 715 expanded)
%              Number of leaves         :   11 ( 169 expanded)
%              Depth                    :   24
%              Number of atoms          :  214 (2454 expanded)
%              Number of equality atoms :  100 (1269 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f349,plain,(
    $false ),
    inference(global_subsumption,[],[f23,f127,f348])).

fof(f348,plain,(
    k1_xboole_0 = sK0 ),
    inference(forward_demodulation,[],[f340,f328])).

fof(f328,plain,(
    ! [X11] : k1_xboole_0 = k3_xboole_0(sK0,X11) ),
    inference(resolution,[],[f293,f202])).

fof(f202,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f201,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f59,f27])).

fof(f27,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_xboole_0(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f201,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f195,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f195,plain,(
    ! [X2] : r1_xboole_0(X2,k1_xboole_0) ),
    inference(resolution,[],[f192,f76])).

fof(f76,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK4(X2,k1_xboole_0),X3)
      | r1_xboole_0(X2,k1_xboole_0) ) ),
    inference(resolution,[],[f74,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f192,plain,(
    ! [X0] : ~ r2_hidden(X0,sK0) ),
    inference(subsumption_resolution,[],[f191,f127])).

% (20078)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f191,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = sK1 ) ),
    inference(equality_resolution,[],[f180])).

fof(f180,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | ~ r2_hidden(X1,sK0)
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f179])).

fof(f179,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | ~ r2_hidden(X1,sK0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f172,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK2(X0,X1)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).

fof(f172,plain,(
    ! [X0,X1] :
      ( sK1 != k1_relat_1(sK2(X1,X0))
      | ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f170,f131])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X1),sK0)
      | sK1 != k1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f130,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f130,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X1),sK0)
      | sK1 != k1_relat_1(sK2(X0,X1))
      | ~ v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f128,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X1),sK0)
      | ~ v1_funct_1(sK2(X0,X1))
      | sK1 != k1_relat_1(sK2(X0,X1))
      | ~ v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f22,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f22,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_relat_1(X2),sK0)
      | ~ v1_funct_1(X2)
      | k1_relat_1(X2) != sK1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

fof(f170,plain,(
    ! [X0] :
      ( r1_tarski(k1_tarski(X0),sK0)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(superposition,[],[f43,f168])).

fof(f168,plain,(
    ! [X0] : sK5(k1_tarski(X0),sK0) = X0 ),
    inference(subsumption_resolution,[],[f167,f127])).

fof(f167,plain,(
    ! [X0] :
      ( sK5(k1_tarski(X0),sK0) = X0
      | k1_xboole_0 = sK1 ) ),
    inference(equality_resolution,[],[f166])).

fof(f166,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | sK5(k1_tarski(X1),sK0) = X1
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f165])).

fof(f165,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | sK5(k1_tarski(X1),sK0) = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f135,f32])).

fof(f135,plain,(
    ! [X0,X1] :
      ( sK1 != k1_relat_1(sK2(X1,X0))
      | sK5(k1_tarski(X0),sK0) = X0
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f64,f131])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | sK5(k1_tarski(X0),X1) = X0 ) ),
    inference(resolution,[],[f42,f54])).

fof(f54,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f293,plain,(
    ! [X50,X51] :
      ( r2_hidden(sK7(sK0,X50,X51),X51)
      | k3_xboole_0(sK0,X50) = X51 ) ),
    inference(resolution,[],[f49,f192])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),X0)
      | r2_hidden(sK7(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f340,plain,(
    ! [X38] : sK0 = k3_xboole_0(sK0,X38) ),
    inference(resolution,[],[f293,f192])).

fof(f127,plain,(
    k1_xboole_0 != sK1 ),
    inference(subsumption_resolution,[],[f126,f119])).

fof(f119,plain,(
    ! [X3] :
      ( v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != X3 ) ),
    inference(superposition,[],[f35,f115])).

fof(f115,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK3(X0)
      | k1_xboole_0 != X0 ) ),
    inference(superposition,[],[f86,f37])).

fof(f37,plain,(
    ! [X0] : k1_relat_1(sK3(X0)) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(f86,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(sK3(X0))
      | k1_xboole_0 = sK3(X0) ) ),
    inference(resolution,[],[f28,f35])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

% (20089)Termination reason: Refutation not found, incomplete strategy
fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

% (20089)Memory used [KB]: 10746
fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

% (20089)Time elapsed: 0.110 s
% (20089)------------------------------
% (20089)------------------------------
fof(f35,plain,(
    ! [X0] : v1_relat_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f126,plain,
    ( k1_xboole_0 != sK1
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f125,f118])).

fof(f118,plain,(
    ! [X2] :
      ( v1_funct_1(k1_xboole_0)
      | k1_xboole_0 != X2 ) ),
    inference(superposition,[],[f36,f115])).

fof(f36,plain,(
    ! [X0] : v1_funct_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f125,plain,
    ( k1_xboole_0 != sK1
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f124,f24])).

fof(f24,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f124,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | k1_relat_1(k1_xboole_0) != sK1
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f123,f26])).

fof(f26,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f123,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | ~ v1_funct_1(k1_xboole_0)
    | k1_relat_1(k1_xboole_0) != sK1
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f22,f25])).

fof(f25,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f23,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:07:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.49  % (20071)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.50  % (20090)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.50  % (20080)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.50  % (20081)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (20072)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.51  % (20071)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 1.13/0.51  % (20065)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.13/0.51  % (20070)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.13/0.51  % (20065)Refutation not found, incomplete strategy% (20065)------------------------------
% 1.13/0.51  % (20065)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.13/0.51  % (20065)Termination reason: Refutation not found, incomplete strategy
% 1.13/0.51  
% 1.13/0.51  % (20065)Memory used [KB]: 1663
% 1.13/0.51  % (20065)Time elapsed: 0.108 s
% 1.13/0.51  % (20065)------------------------------
% 1.13/0.51  % (20065)------------------------------
% 1.13/0.52  % (20069)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.13/0.52  % (20089)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.13/0.52  % (20089)Refutation not found, incomplete strategy% (20089)------------------------------
% 1.13/0.52  % (20089)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.13/0.52  % SZS output start Proof for theBenchmark
% 1.13/0.52  fof(f349,plain,(
% 1.13/0.52    $false),
% 1.13/0.52    inference(global_subsumption,[],[f23,f127,f348])).
% 1.13/0.52  fof(f348,plain,(
% 1.13/0.52    k1_xboole_0 = sK0),
% 1.13/0.52    inference(forward_demodulation,[],[f340,f328])).
% 1.13/0.52  fof(f328,plain,(
% 1.13/0.52    ( ! [X11] : (k1_xboole_0 = k3_xboole_0(sK0,X11)) )),
% 1.13/0.52    inference(resolution,[],[f293,f202])).
% 1.13/0.52  fof(f202,plain,(
% 1.13/0.52    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.13/0.52    inference(subsumption_resolution,[],[f201,f74])).
% 1.13/0.52  fof(f74,plain,(
% 1.13/0.52    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | r2_hidden(X1,X0)) )),
% 1.13/0.52    inference(superposition,[],[f59,f27])).
% 1.13/0.52  fof(f27,plain,(
% 1.13/0.52    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.13/0.52    inference(cnf_transformation,[],[f4])).
% 1.13/0.52  fof(f4,axiom,(
% 1.13/0.52    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.13/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.13/0.52  fof(f59,plain,(
% 1.13/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,k3_xboole_0(X0,X1)) | r2_hidden(X3,X0)) )),
% 1.13/0.52    inference(equality_resolution,[],[f51])).
% 1.13/0.52  fof(f51,plain,(
% 1.13/0.52    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.13/0.52    inference(cnf_transformation,[],[f2])).
% 1.13/0.52  fof(f2,axiom,(
% 1.13/0.52    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.13/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.13/0.52  fof(f201,plain,(
% 1.13/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,X1)) )),
% 1.13/0.52    inference(resolution,[],[f195,f38])).
% 1.13/0.52  fof(f38,plain,(
% 1.13/0.52    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.13/0.52    inference(cnf_transformation,[],[f20])).
% 1.13/0.52  fof(f20,plain,(
% 1.13/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.13/0.52    inference(ennf_transformation,[],[f13])).
% 1.13/0.52  fof(f13,plain,(
% 1.13/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.13/0.52    inference(rectify,[],[f3])).
% 1.13/0.52  fof(f3,axiom,(
% 1.13/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.13/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.13/0.52  fof(f195,plain,(
% 1.13/0.52    ( ! [X2] : (r1_xboole_0(X2,k1_xboole_0)) )),
% 1.13/0.52    inference(resolution,[],[f192,f76])).
% 1.13/0.52  fof(f76,plain,(
% 1.13/0.52    ( ! [X2,X3] : (r2_hidden(sK4(X2,k1_xboole_0),X3) | r1_xboole_0(X2,k1_xboole_0)) )),
% 1.13/0.52    inference(resolution,[],[f74,f40])).
% 1.13/0.52  fof(f40,plain,(
% 1.13/0.52    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.13/0.52    inference(cnf_transformation,[],[f20])).
% 1.13/0.52  fof(f192,plain,(
% 1.13/0.52    ( ! [X0] : (~r2_hidden(X0,sK0)) )),
% 1.13/0.52    inference(subsumption_resolution,[],[f191,f127])).
% 1.13/0.52  % (20078)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.13/0.52  fof(f191,plain,(
% 1.13/0.52    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_xboole_0 = sK1) )),
% 1.13/0.52    inference(equality_resolution,[],[f180])).
% 1.13/0.52  fof(f180,plain,(
% 1.13/0.52    ( ! [X0,X1] : (sK1 != X0 | ~r2_hidden(X1,sK0) | k1_xboole_0 = X0) )),
% 1.13/0.52    inference(duplicate_literal_removal,[],[f179])).
% 1.13/0.52  fof(f179,plain,(
% 1.13/0.52    ( ! [X0,X1] : (sK1 != X0 | ~r2_hidden(X1,sK0) | k1_xboole_0 = X0 | k1_xboole_0 = X0) )),
% 1.13/0.52    inference(superposition,[],[f172,f32])).
% 1.13/0.52  fof(f32,plain,(
% 1.13/0.52    ( ! [X0,X1] : (k1_relat_1(sK2(X0,X1)) = X0 | k1_xboole_0 = X0) )),
% 1.13/0.52    inference(cnf_transformation,[],[f18])).
% 1.13/0.52  fof(f18,plain,(
% 1.13/0.52    ! [X0] : (! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 1.13/0.52    inference(ennf_transformation,[],[f10])).
% 1.13/0.52  fof(f10,axiom,(
% 1.13/0.52    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.13/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).
% 1.13/0.52  fof(f172,plain,(
% 1.13/0.52    ( ! [X0,X1] : (sK1 != k1_relat_1(sK2(X1,X0)) | ~r2_hidden(X0,sK0) | k1_xboole_0 = X1) )),
% 1.13/0.52    inference(resolution,[],[f170,f131])).
% 1.13/0.52  fof(f131,plain,(
% 1.13/0.52    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X1),sK0) | sK1 != k1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.13/0.52    inference(subsumption_resolution,[],[f130,f30])).
% 1.13/0.52  fof(f30,plain,(
% 1.13/0.52    ( ! [X0,X1] : (v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.13/0.52    inference(cnf_transformation,[],[f18])).
% 1.13/0.52  fof(f130,plain,(
% 1.13/0.52    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X1),sK0) | sK1 != k1_relat_1(sK2(X0,X1)) | ~v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.13/0.52    inference(subsumption_resolution,[],[f128,f31])).
% 1.13/0.52  fof(f31,plain,(
% 1.13/0.52    ( ! [X0,X1] : (v1_funct_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.13/0.52    inference(cnf_transformation,[],[f18])).
% 1.13/0.52  fof(f128,plain,(
% 1.13/0.52    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X1),sK0) | ~v1_funct_1(sK2(X0,X1)) | sK1 != k1_relat_1(sK2(X0,X1)) | ~v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.13/0.52    inference(superposition,[],[f22,f33])).
% 1.13/0.52  fof(f33,plain,(
% 1.13/0.52    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.13/0.52    inference(cnf_transformation,[],[f18])).
% 1.13/0.52  fof(f22,plain,(
% 1.13/0.52    ( ! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | ~v1_funct_1(X2) | k1_relat_1(X2) != sK1 | ~v1_relat_1(X2)) )),
% 1.13/0.52    inference(cnf_transformation,[],[f15])).
% 1.13/0.52  fof(f15,plain,(
% 1.13/0.52    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.13/0.52    inference(flattening,[],[f14])).
% 1.13/0.52  fof(f14,plain,(
% 1.13/0.52    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.13/0.52    inference(ennf_transformation,[],[f12])).
% 1.13/0.52  fof(f12,negated_conjecture,(
% 1.13/0.52    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.13/0.52    inference(negated_conjecture,[],[f11])).
% 1.13/0.52  fof(f11,conjecture,(
% 1.13/0.52    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.13/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).
% 1.13/0.52  fof(f170,plain,(
% 1.13/0.52    ( ! [X0] : (r1_tarski(k1_tarski(X0),sK0) | ~r2_hidden(X0,sK0)) )),
% 1.13/0.52    inference(superposition,[],[f43,f168])).
% 1.13/0.52  fof(f168,plain,(
% 1.13/0.52    ( ! [X0] : (sK5(k1_tarski(X0),sK0) = X0) )),
% 1.13/0.52    inference(subsumption_resolution,[],[f167,f127])).
% 1.13/0.52  fof(f167,plain,(
% 1.13/0.52    ( ! [X0] : (sK5(k1_tarski(X0),sK0) = X0 | k1_xboole_0 = sK1) )),
% 1.13/0.52    inference(equality_resolution,[],[f166])).
% 1.13/0.52  fof(f166,plain,(
% 1.13/0.52    ( ! [X0,X1] : (sK1 != X0 | sK5(k1_tarski(X1),sK0) = X1 | k1_xboole_0 = X0) )),
% 1.13/0.52    inference(duplicate_literal_removal,[],[f165])).
% 1.13/0.52  fof(f165,plain,(
% 1.13/0.52    ( ! [X0,X1] : (sK1 != X0 | sK5(k1_tarski(X1),sK0) = X1 | k1_xboole_0 = X0 | k1_xboole_0 = X0) )),
% 1.13/0.52    inference(superposition,[],[f135,f32])).
% 1.13/0.52  fof(f135,plain,(
% 1.13/0.52    ( ! [X0,X1] : (sK1 != k1_relat_1(sK2(X1,X0)) | sK5(k1_tarski(X0),sK0) = X0 | k1_xboole_0 = X1) )),
% 1.13/0.52    inference(resolution,[],[f64,f131])).
% 1.13/0.52  fof(f64,plain,(
% 1.13/0.52    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | sK5(k1_tarski(X0),X1) = X0) )),
% 1.13/0.52    inference(resolution,[],[f42,f54])).
% 1.13/0.52  fof(f54,plain,(
% 1.13/0.52    ( ! [X2,X0] : (~r2_hidden(X2,k1_tarski(X0)) | X0 = X2) )),
% 1.13/0.52    inference(equality_resolution,[],[f45])).
% 1.13/0.52  fof(f45,plain,(
% 1.13/0.52    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.13/0.52    inference(cnf_transformation,[],[f6])).
% 1.13/0.52  fof(f6,axiom,(
% 1.13/0.52    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.13/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.13/0.52  fof(f42,plain,(
% 1.13/0.52    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.13/0.52    inference(cnf_transformation,[],[f21])).
% 1.13/0.52  fof(f21,plain,(
% 1.13/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.13/0.52    inference(ennf_transformation,[],[f1])).
% 1.13/0.52  fof(f1,axiom,(
% 1.13/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.13/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.13/0.52  fof(f43,plain,(
% 1.13/0.52    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.13/0.52    inference(cnf_transformation,[],[f21])).
% 1.13/0.52  fof(f293,plain,(
% 1.13/0.52    ( ! [X50,X51] : (r2_hidden(sK7(sK0,X50,X51),X51) | k3_xboole_0(sK0,X50) = X51) )),
% 1.13/0.52    inference(resolution,[],[f49,f192])).
% 1.13/0.52  fof(f49,plain,(
% 1.13/0.52    ( ! [X2,X0,X1] : (r2_hidden(sK7(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 1.13/0.52    inference(cnf_transformation,[],[f2])).
% 1.13/0.52  fof(f340,plain,(
% 1.13/0.52    ( ! [X38] : (sK0 = k3_xboole_0(sK0,X38)) )),
% 1.13/0.52    inference(resolution,[],[f293,f192])).
% 1.13/0.52  fof(f127,plain,(
% 1.13/0.52    k1_xboole_0 != sK1),
% 1.13/0.52    inference(subsumption_resolution,[],[f126,f119])).
% 1.13/0.52  fof(f119,plain,(
% 1.13/0.52    ( ! [X3] : (v1_relat_1(k1_xboole_0) | k1_xboole_0 != X3) )),
% 1.13/0.52    inference(superposition,[],[f35,f115])).
% 1.13/0.52  fof(f115,plain,(
% 1.13/0.52    ( ! [X0] : (k1_xboole_0 = sK3(X0) | k1_xboole_0 != X0) )),
% 1.13/0.52    inference(superposition,[],[f86,f37])).
% 1.13/0.52  fof(f37,plain,(
% 1.13/0.52    ( ! [X0] : (k1_relat_1(sK3(X0)) = X0) )),
% 1.13/0.52    inference(cnf_transformation,[],[f19])).
% 1.13/0.52  fof(f19,plain,(
% 1.13/0.52    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.13/0.52    inference(ennf_transformation,[],[f9])).
% 1.13/0.52  fof(f9,axiom,(
% 1.13/0.52    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.13/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).
% 1.13/0.52  fof(f86,plain,(
% 1.13/0.52    ( ! [X0] : (k1_xboole_0 != k1_relat_1(sK3(X0)) | k1_xboole_0 = sK3(X0)) )),
% 1.13/0.52    inference(resolution,[],[f28,f35])).
% 1.13/0.52  fof(f28,plain,(
% 1.13/0.52    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0) )),
% 1.13/0.52    inference(cnf_transformation,[],[f17])).
% 1.13/0.52  fof(f17,plain,(
% 1.13/0.52    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.13/0.52    inference(flattening,[],[f16])).
% 1.13/0.52  % (20089)Termination reason: Refutation not found, incomplete strategy
% 1.13/0.52  fof(f16,plain,(
% 1.13/0.52    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.13/0.52    inference(ennf_transformation,[],[f8])).
% 1.13/0.52  
% 1.13/0.52  % (20089)Memory used [KB]: 10746
% 1.13/0.52  fof(f8,axiom,(
% 1.13/0.52    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.13/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 1.13/0.52  % (20089)Time elapsed: 0.110 s
% 1.13/0.52  % (20089)------------------------------
% 1.13/0.52  % (20089)------------------------------
% 1.13/0.52  fof(f35,plain,(
% 1.13/0.52    ( ! [X0] : (v1_relat_1(sK3(X0))) )),
% 1.13/0.52    inference(cnf_transformation,[],[f19])).
% 1.13/0.52  fof(f126,plain,(
% 1.13/0.52    k1_xboole_0 != sK1 | ~v1_relat_1(k1_xboole_0)),
% 1.13/0.52    inference(subsumption_resolution,[],[f125,f118])).
% 1.13/0.52  fof(f118,plain,(
% 1.13/0.52    ( ! [X2] : (v1_funct_1(k1_xboole_0) | k1_xboole_0 != X2) )),
% 1.13/0.52    inference(superposition,[],[f36,f115])).
% 1.13/0.52  fof(f36,plain,(
% 1.13/0.52    ( ! [X0] : (v1_funct_1(sK3(X0))) )),
% 1.13/0.52    inference(cnf_transformation,[],[f19])).
% 1.13/0.52  fof(f125,plain,(
% 1.13/0.52    k1_xboole_0 != sK1 | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 1.13/0.52    inference(forward_demodulation,[],[f124,f24])).
% 1.13/0.52  fof(f24,plain,(
% 1.13/0.52    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.13/0.52    inference(cnf_transformation,[],[f7])).
% 1.13/0.52  fof(f7,axiom,(
% 1.13/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.13/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.13/0.52  fof(f124,plain,(
% 1.13/0.52    ~v1_funct_1(k1_xboole_0) | k1_relat_1(k1_xboole_0) != sK1 | ~v1_relat_1(k1_xboole_0)),
% 1.13/0.52    inference(subsumption_resolution,[],[f123,f26])).
% 1.13/0.52  fof(f26,plain,(
% 1.13/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.13/0.52    inference(cnf_transformation,[],[f5])).
% 1.13/0.52  fof(f5,axiom,(
% 1.13/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.13/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.13/0.52  fof(f123,plain,(
% 1.13/0.52    ~r1_tarski(k1_xboole_0,sK0) | ~v1_funct_1(k1_xboole_0) | k1_relat_1(k1_xboole_0) != sK1 | ~v1_relat_1(k1_xboole_0)),
% 1.13/0.52    inference(superposition,[],[f22,f25])).
% 1.13/0.52  fof(f25,plain,(
% 1.13/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.13/0.52    inference(cnf_transformation,[],[f7])).
% 1.13/0.52  fof(f23,plain,(
% 1.13/0.52    k1_xboole_0 != sK0 | k1_xboole_0 = sK1),
% 1.13/0.52    inference(cnf_transformation,[],[f15])).
% 1.13/0.52  % SZS output end Proof for theBenchmark
% 1.13/0.52  % (20071)------------------------------
% 1.13/0.52  % (20071)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.13/0.52  % (20071)Termination reason: Refutation
% 1.13/0.52  
% 1.13/0.52  % (20071)Memory used [KB]: 6524
% 1.13/0.52  % (20071)Time elapsed: 0.104 s
% 1.13/0.52  % (20071)------------------------------
% 1.13/0.52  % (20071)------------------------------
% 1.13/0.52  % (20061)Success in time 0.157 s
%------------------------------------------------------------------------------
