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
% DateTime   : Thu Dec  3 12:47:51 EST 2020

% Result     : Theorem 0.81s
% Output     : Refutation 1.14s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 135 expanded)
%              Number of leaves         :   14 (  35 expanded)
%              Depth                    :   17
%              Number of atoms          :  170 ( 301 expanded)
%              Number of equality atoms :   32 (  67 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f181,plain,(
    $false ),
    inference(subsumption_resolution,[],[f179,f119])).

fof(f119,plain,(
    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(trivial_inequality_removal,[],[f115])).

fof(f115,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(superposition,[],[f29,f107])).

fof(f107,plain,(
    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    inference(resolution,[],[f104,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f104,plain,(
    v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f103,f30])).

fof(f30,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(f103,plain,
    ( v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f102,f50])).

fof(f50,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f34,f31])).

fof(f31,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f102,plain,
    ( v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f95,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f95,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f94,f31])).

fof(f94,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(superposition,[],[f39,f88])).

fof(f88,plain,(
    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(resolution,[],[f87,f30])).

fof(f87,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f86,f59])).

fof(f59,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(resolution,[],[f57,f31])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(resolution,[],[f47,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(resolution,[],[f44,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
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

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f86,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k4_xboole_0(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) ) ),
    inference(resolution,[],[f85,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f85,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f84,f50])).

fof(f84,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f36,f33])).

fof(f33,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

fof(f29,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f179,plain,(
    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    inference(resolution,[],[f176,f35])).

fof(f176,plain,(
    v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(subsumption_resolution,[],[f175,f50])).

fof(f175,plain,
    ( v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f174,f30])).

fof(f174,plain,
    ( v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f173,f45])).

fof(f173,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(subsumption_resolution,[],[f172,f31])).

fof(f172,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(superposition,[],[f38,f165])).

fof(f165,plain,(
    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(resolution,[],[f162,f30])).

fof(f162,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) ) ),
    inference(forward_demodulation,[],[f160,f59])).

fof(f160,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k4_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) ) ),
    inference(resolution,[],[f159,f48])).

fof(f159,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f152,f50])).

fof(f152,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f37,f32])).

fof(f32,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:16:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.37  ipcrm: permission denied for id (819134465)
% 0.13/0.37  ipcrm: permission denied for id (819167234)
% 0.13/0.37  ipcrm: permission denied for id (819200005)
% 0.13/0.37  ipcrm: permission denied for id (819232774)
% 0.13/0.39  ipcrm: permission denied for id (819331091)
% 0.13/0.39  ipcrm: permission denied for id (819363861)
% 0.13/0.39  ipcrm: permission denied for id (819396630)
% 0.13/0.39  ipcrm: permission denied for id (819429399)
% 0.13/0.40  ipcrm: permission denied for id (819462172)
% 0.13/0.41  ipcrm: permission denied for id (819593251)
% 0.13/0.41  ipcrm: permission denied for id (819658791)
% 0.21/0.43  ipcrm: permission denied for id (819789877)
% 0.21/0.44  ipcrm: permission denied for id (819855419)
% 0.21/0.44  ipcrm: permission denied for id (819888189)
% 0.21/0.44  ipcrm: permission denied for id (819953726)
% 0.21/0.44  ipcrm: permission denied for id (819986495)
% 0.21/0.45  ipcrm: permission denied for id (820117575)
% 0.21/0.45  ipcrm: permission denied for id (820150346)
% 0.21/0.46  ipcrm: permission denied for id (820183118)
% 0.21/0.46  ipcrm: permission denied for id (820248657)
% 0.21/0.47  ipcrm: permission denied for id (820281432)
% 0.21/0.47  ipcrm: permission denied for id (820346970)
% 0.21/0.49  ipcrm: permission denied for id (820379749)
% 0.21/0.50  ipcrm: permission denied for id (820412527)
% 0.21/0.50  ipcrm: permission denied for id (820445296)
% 0.21/0.51  ipcrm: permission denied for id (820543605)
% 0.21/0.51  ipcrm: permission denied for id (820576375)
% 0.21/0.51  ipcrm: permission denied for id (820609145)
% 0.81/0.61  % (10306)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.81/0.62  % (10313)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.81/0.63  % (10317)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.81/0.63  % (10317)Refutation found. Thanks to Tanya!
% 0.81/0.63  % SZS status Theorem for theBenchmark
% 0.81/0.64  % (10309)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 1.14/0.64  % (10324)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 1.14/0.64  % SZS output start Proof for theBenchmark
% 1.14/0.64  fof(f181,plain,(
% 1.14/0.64    $false),
% 1.14/0.64    inference(subsumption_resolution,[],[f179,f119])).
% 1.14/0.64  fof(f119,plain,(
% 1.14/0.64    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 1.14/0.64    inference(trivial_inequality_removal,[],[f115])).
% 1.14/0.64  fof(f115,plain,(
% 1.14/0.64    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 1.14/0.64    inference(superposition,[],[f29,f107])).
% 1.14/0.64  fof(f107,plain,(
% 1.14/0.64    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 1.14/0.64    inference(resolution,[],[f104,f35])).
% 1.14/0.64  fof(f35,plain,(
% 1.14/0.64    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.14/0.64    inference(cnf_transformation,[],[f19])).
% 1.14/0.64  fof(f19,plain,(
% 1.14/0.64    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.14/0.64    inference(ennf_transformation,[],[f3])).
% 1.14/0.64  fof(f3,axiom,(
% 1.14/0.64    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.14/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.14/0.64  fof(f104,plain,(
% 1.14/0.64    v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))),
% 1.14/0.64    inference(subsumption_resolution,[],[f103,f30])).
% 1.14/0.64  fof(f30,plain,(
% 1.14/0.64    v1_relat_1(sK0)),
% 1.14/0.64    inference(cnf_transformation,[],[f17])).
% 1.14/0.64  fof(f17,plain,(
% 1.14/0.64    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 1.14/0.64    inference(ennf_transformation,[],[f15])).
% 1.14/0.64  fof(f15,negated_conjecture,(
% 1.14/0.64    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.14/0.64    inference(negated_conjecture,[],[f14])).
% 1.14/0.64  fof(f14,conjecture,(
% 1.14/0.64    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.14/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).
% 1.14/0.64  fof(f103,plain,(
% 1.14/0.64    v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) | ~v1_relat_1(sK0)),
% 1.14/0.64    inference(subsumption_resolution,[],[f102,f50])).
% 1.14/0.64  fof(f50,plain,(
% 1.14/0.64    v1_relat_1(k1_xboole_0)),
% 1.14/0.64    inference(resolution,[],[f34,f31])).
% 1.14/0.64  fof(f31,plain,(
% 1.14/0.64    v1_xboole_0(k1_xboole_0)),
% 1.14/0.64    inference(cnf_transformation,[],[f2])).
% 1.14/0.64  fof(f2,axiom,(
% 1.14/0.64    v1_xboole_0(k1_xboole_0)),
% 1.14/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.14/0.64  fof(f34,plain,(
% 1.14/0.64    ( ! [X0] : (~v1_xboole_0(X0) | v1_relat_1(X0)) )),
% 1.14/0.64    inference(cnf_transformation,[],[f18])).
% 1.14/0.64  fof(f18,plain,(
% 1.14/0.64    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 1.14/0.64    inference(ennf_transformation,[],[f7])).
% 1.14/0.64  fof(f7,axiom,(
% 1.14/0.64    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 1.14/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 1.14/0.64  fof(f102,plain,(
% 1.14/0.64    v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK0)),
% 1.14/0.64    inference(resolution,[],[f95,f45])).
% 1.14/0.64  fof(f45,plain,(
% 1.14/0.64    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.14/0.64    inference(cnf_transformation,[],[f28])).
% 1.14/0.64  fof(f28,plain,(
% 1.14/0.64    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.14/0.64    inference(flattening,[],[f27])).
% 1.14/0.64  fof(f27,plain,(
% 1.14/0.64    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.14/0.64    inference(ennf_transformation,[],[f8])).
% 1.14/0.64  fof(f8,axiom,(
% 1.14/0.64    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.14/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.14/0.64  fof(f95,plain,(
% 1.14/0.64    ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))),
% 1.14/0.64    inference(subsumption_resolution,[],[f94,f31])).
% 1.14/0.64  fof(f94,plain,(
% 1.14/0.64    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))),
% 1.14/0.64    inference(superposition,[],[f39,f88])).
% 1.14/0.64  fof(f88,plain,(
% 1.14/0.64    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 1.14/0.64    inference(resolution,[],[f87,f30])).
% 1.14/0.64  fof(f87,plain,(
% 1.14/0.64    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0))) )),
% 1.14/0.64    inference(forward_demodulation,[],[f86,f59])).
% 1.14/0.64  fof(f59,plain,(
% 1.14/0.64    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.14/0.64    inference(resolution,[],[f57,f31])).
% 1.14/0.64  fof(f57,plain,(
% 1.14/0.64    ( ! [X0,X1] : (~v1_xboole_0(X1) | k4_xboole_0(X0,X1) = X0) )),
% 1.14/0.64    inference(resolution,[],[f47,f56])).
% 1.14/0.64  fof(f56,plain,(
% 1.14/0.64    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~v1_xboole_0(X1)) )),
% 1.14/0.64    inference(resolution,[],[f44,f41])).
% 1.14/0.64  fof(f41,plain,(
% 1.14/0.64    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.14/0.64    inference(cnf_transformation,[],[f1])).
% 1.14/0.64  fof(f1,axiom,(
% 1.14/0.64    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.14/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.14/0.64  fof(f44,plain,(
% 1.14/0.64    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.14/0.64    inference(cnf_transformation,[],[f26])).
% 1.14/0.64  fof(f26,plain,(
% 1.14/0.64    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.14/0.64    inference(ennf_transformation,[],[f16])).
% 1.14/0.64  fof(f16,plain,(
% 1.14/0.64    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.14/0.64    inference(rectify,[],[f4])).
% 1.14/0.64  fof(f4,axiom,(
% 1.14/0.64    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.14/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.14/0.64  fof(f47,plain,(
% 1.14/0.64    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 1.14/0.64    inference(cnf_transformation,[],[f6])).
% 1.14/0.64  fof(f6,axiom,(
% 1.14/0.64    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.14/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.14/0.64  fof(f86,plain,(
% 1.14/0.64    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k4_xboole_0(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)) )),
% 1.14/0.64    inference(resolution,[],[f85,f48])).
% 1.14/0.64  fof(f48,plain,(
% 1.14/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 1.14/0.64    inference(cnf_transformation,[],[f5])).
% 1.14/0.64  fof(f5,axiom,(
% 1.14/0.64    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 1.14/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.14/0.64  fof(f85,plain,(
% 1.14/0.64    ( ! [X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(X0)) )),
% 1.14/0.64    inference(subsumption_resolution,[],[f84,f50])).
% 1.14/0.64  fof(f84,plain,(
% 1.14/0.64    ( ! [X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0)) )),
% 1.14/0.64    inference(superposition,[],[f36,f33])).
% 1.14/0.64  fof(f33,plain,(
% 1.14/0.64    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.14/0.64    inference(cnf_transformation,[],[f13])).
% 1.14/0.64  fof(f13,axiom,(
% 1.14/0.64    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.14/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.14/0.64  fof(f36,plain,(
% 1.14/0.64    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.14/0.64    inference(cnf_transformation,[],[f20])).
% 1.14/0.64  fof(f20,plain,(
% 1.14/0.64    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.14/0.64    inference(ennf_transformation,[],[f12])).
% 1.14/0.64  fof(f12,axiom,(
% 1.14/0.64    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 1.14/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).
% 1.14/0.64  fof(f39,plain,(
% 1.14/0.64    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 1.14/0.64    inference(cnf_transformation,[],[f25])).
% 1.14/0.64  fof(f25,plain,(
% 1.14/0.64    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 1.14/0.64    inference(flattening,[],[f24])).
% 1.14/0.64  fof(f24,plain,(
% 1.14/0.64    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 1.14/0.64    inference(ennf_transformation,[],[f10])).
% 1.14/0.64  fof(f10,axiom,(
% 1.14/0.64    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 1.14/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).
% 1.14/0.64  fof(f29,plain,(
% 1.14/0.64    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 1.14/0.64    inference(cnf_transformation,[],[f17])).
% 1.14/0.64  fof(f179,plain,(
% 1.14/0.64    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 1.14/0.64    inference(resolution,[],[f176,f35])).
% 1.14/0.64  fof(f176,plain,(
% 1.14/0.64    v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))),
% 1.14/0.64    inference(subsumption_resolution,[],[f175,f50])).
% 1.14/0.64  fof(f175,plain,(
% 1.14/0.64    v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) | ~v1_relat_1(k1_xboole_0)),
% 1.14/0.64    inference(subsumption_resolution,[],[f174,f30])).
% 1.14/0.64  fof(f174,plain,(
% 1.14/0.64    v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(k1_xboole_0)),
% 1.14/0.64    inference(resolution,[],[f173,f45])).
% 1.14/0.64  fof(f173,plain,(
% 1.14/0.64    ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))),
% 1.14/0.64    inference(subsumption_resolution,[],[f172,f31])).
% 1.14/0.64  fof(f172,plain,(
% 1.14/0.64    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))),
% 1.14/0.64    inference(superposition,[],[f38,f165])).
% 1.14/0.64  fof(f165,plain,(
% 1.14/0.64    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 1.14/0.64    inference(resolution,[],[f162,f30])).
% 1.14/0.64  fof(f162,plain,(
% 1.14/0.64    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0))) )),
% 1.14/0.64    inference(forward_demodulation,[],[f160,f59])).
% 1.14/0.64  fof(f160,plain,(
% 1.14/0.64    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k4_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0)) )),
% 1.14/0.64    inference(resolution,[],[f159,f48])).
% 1.14/0.64  fof(f159,plain,(
% 1.14/0.64    ( ! [X0] : (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) | ~v1_relat_1(X0)) )),
% 1.14/0.64    inference(subsumption_resolution,[],[f152,f50])).
% 1.14/0.64  fof(f152,plain,(
% 1.14/0.64    ( ! [X0] : (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.14/0.64    inference(superposition,[],[f37,f32])).
% 1.14/0.64  fof(f32,plain,(
% 1.14/0.64    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.14/0.64    inference(cnf_transformation,[],[f13])).
% 1.14/0.64  fof(f37,plain,(
% 1.14/0.64    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.14/0.64    inference(cnf_transformation,[],[f21])).
% 1.14/0.64  fof(f21,plain,(
% 1.14/0.64    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.14/0.64    inference(ennf_transformation,[],[f11])).
% 1.14/0.64  fof(f11,axiom,(
% 1.14/0.64    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 1.14/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).
% 1.14/0.64  fof(f38,plain,(
% 1.14/0.64    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 1.14/0.64    inference(cnf_transformation,[],[f23])).
% 1.14/0.64  fof(f23,plain,(
% 1.14/0.64    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 1.14/0.64    inference(flattening,[],[f22])).
% 1.14/0.64  fof(f22,plain,(
% 1.14/0.64    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 1.14/0.64    inference(ennf_transformation,[],[f9])).
% 1.14/0.64  fof(f9,axiom,(
% 1.14/0.64    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k1_relat_1(X0)))),
% 1.14/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).
% 1.14/0.64  % SZS output end Proof for theBenchmark
% 1.14/0.64  % (10317)------------------------------
% 1.14/0.64  % (10317)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.14/0.64  % (10317)Termination reason: Refutation
% 1.14/0.64  
% 1.14/0.64  % (10317)Memory used [KB]: 6140
% 1.14/0.64  % (10317)Time elapsed: 0.057 s
% 1.14/0.64  % (10317)------------------------------
% 1.14/0.64  % (10317)------------------------------
% 1.14/0.64  % (10170)Success in time 0.281 s
%------------------------------------------------------------------------------
