%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:05 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 508 expanded)
%              Number of leaves         :    9 ( 123 expanded)
%              Depth                    :   19
%              Number of atoms          :  190 (1880 expanded)
%              Number of equality atoms :   67 ( 716 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f964,plain,(
    $false ),
    inference(global_subsumption,[],[f269,f950])).

fof(f950,plain,(
    r2_hidden(k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f371,f852])).

fof(f852,plain,(
    k1_xboole_0 = sK5(sK7(k1_xboole_0),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f460,f582])).

fof(f582,plain,(
    ! [X0,X1] :
      ( ~ sP4(X0,sK7(X1))
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f575])).

fof(f575,plain,(
    ! [X0,X1] :
      ( ~ sP4(X0,sK7(X1))
      | k1_xboole_0 = X0
      | ~ sP4(X0,sK7(X1)) ) ),
    inference(resolution,[],[f203,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(sK7(X0),X1),X0)
      | ~ sP4(X1,sK7(X0)) ) ),
    inference(superposition,[],[f27,f37])).

fof(f37,plain,(
    ! [X0] : k1_relat_1(sK7(X0)) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(f27,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK5(X0,X2),k1_relat_1(X0))
      | ~ sP4(X2,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f203,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(sK7(X0),X1),X0)
      | ~ sP4(X1,sK7(X0))
      | k1_xboole_0 = X1 ) ),
    inference(superposition,[],[f28,f34])).

fof(f34,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = k1_funct_1(sK7(X0),X2)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f28,plain,(
    ! [X2,X0] :
      ( k1_funct_1(X0,sK5(X0,X2)) = X2
      | ~ sP4(X2,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f460,plain,(
    ! [X0] : sP4(sK5(sK7(k1_xboole_0),k1_xboole_0),sK7(X0)) ),
    inference(unit_resulting_resolution,[],[f35,f36,f398,f46])).

fof(f46,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | sP4(X2,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | sP4(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f398,plain,(
    ! [X0] : r2_hidden(sK5(sK7(k1_xboole_0),k1_xboole_0),X0) ),
    inference(global_subsumption,[],[f21,f397])).

fof(f397,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK7(k1_xboole_0),k1_xboole_0),X0)
      | ~ r1_tarski(k1_xboole_0,X0) ) ),
    inference(forward_demodulation,[],[f375,f347])).

fof(f347,plain,(
    k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f20,f180])).

fof(f180,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f178,f33])).

fof(f33,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f178,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = sK1 ) ),
    inference(resolution,[],[f177,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f177,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_tarski(X0),sK0)
      | k1_xboole_0 = sK1 ) ),
    inference(duplicate_literal_removal,[],[f176])).

fof(f176,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_tarski(X0),sK0)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f80,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).

fof(f80,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK2(sK1,X0)),sK0)
      | k1_xboole_0 = sK1 ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | ~ r1_tarski(k2_relat_1(sK2(X0,X1)),sK0)
      | k1_xboole_0 = X0 ) ),
    inference(global_subsumption,[],[f23,f22,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | ~ v1_funct_1(sK2(X0,X1))
      | ~ v1_relat_1(sK2(X0,X1))
      | ~ r1_tarski(k2_relat_1(sK2(X0,X1)),sK0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f19,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK2(X0,X1)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f19,plain,(
    ! [X2] :
      ( k1_relat_1(X2) != sK1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),sK0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f20,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f12])).

fof(f375,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | r2_hidden(sK5(sK7(sK1),k1_xboole_0),X0) ) ),
    inference(backward_demodulation,[],[f285,f347])).

fof(f285,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK7(sK1),k1_xboole_0),X0)
      | ~ r1_tarski(sK1,X0) ) ),
    inference(forward_demodulation,[],[f240,f242])).

fof(f242,plain,(
    k1_xboole_0 = sK8(k2_relat_1(sK7(sK1)),sK0) ),
    inference(backward_demodulation,[],[f215,f238])).

fof(f238,plain,(
    k1_xboole_0 = k1_funct_1(sK7(sK1),sK5(sK7(sK1),sK8(k2_relat_1(sK7(sK1)),sK0))) ),
    inference(unit_resulting_resolution,[],[f218,f34])).

fof(f218,plain,(
    r2_hidden(sK5(sK7(sK1),sK8(k2_relat_1(sK7(sK1)),sK0)),sK1) ),
    inference(forward_demodulation,[],[f216,f37])).

fof(f216,plain,(
    r2_hidden(sK5(sK7(sK1),sK8(k2_relat_1(sK7(sK1)),sK0)),k1_relat_1(sK7(sK1))) ),
    inference(unit_resulting_resolution,[],[f208,f27])).

fof(f208,plain,(
    sP4(sK8(k2_relat_1(sK7(sK1)),sK0),sK7(sK1)) ),
    inference(unit_resulting_resolution,[],[f35,f36,f61,f46])).

fof(f61,plain,(
    r2_hidden(sK8(k2_relat_1(sK7(sK1)),sK0),k2_relat_1(sK7(sK1))) ),
    inference(unit_resulting_resolution,[],[f51,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f51,plain,(
    ~ r1_tarski(k2_relat_1(sK7(sK1)),sK0) ),
    inference(unit_resulting_resolution,[],[f36,f35,f37,f19])).

fof(f215,plain,(
    sK8(k2_relat_1(sK7(sK1)),sK0) = k1_funct_1(sK7(sK1),sK5(sK7(sK1),sK8(k2_relat_1(sK7(sK1)),sK0))) ),
    inference(unit_resulting_resolution,[],[f208,f28])).

fof(f240,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK7(sK1),sK8(k2_relat_1(sK7(sK1)),sK0)),X0)
      | ~ r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f218,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f21,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f36,plain,(
    ! [X0] : v1_funct_1(sK7(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f35,plain,(
    ! [X0] : v1_relat_1(sK7(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f371,plain,(
    r2_hidden(sK5(sK7(k1_xboole_0),k1_xboole_0),k1_xboole_0) ),
    inference(backward_demodulation,[],[f279,f347])).

fof(f279,plain,(
    r2_hidden(sK5(sK7(sK1),k1_xboole_0),sK1) ),
    inference(backward_demodulation,[],[f218,f242])).

fof(f269,plain,(
    ~ r2_hidden(k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f120,f242])).

fof(f120,plain,(
    ~ r2_hidden(sK8(k2_relat_1(sK7(sK1)),sK0),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f21,f110])).

fof(f110,plain,
    ( ~ r2_hidden(sK8(k2_relat_1(sK7(sK1)),sK0),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK0) ),
    inference(superposition,[],[f66,f104])).

fof(f104,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_tarski(X0)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f96,f44])).

fof(f96,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f40,f21])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f66,plain,(
    ~ r1_tarski(k1_tarski(sK8(k2_relat_1(sK7(sK1)),sK0)),sK0) ),
    inference(unit_resulting_resolution,[],[f63,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f63,plain,(
    ~ r2_hidden(sK8(k2_relat_1(sK7(sK1)),sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f51,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK8(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:48:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (29048)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.50  % (29024)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.50  % (29027)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (29029)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (29028)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (29029)Refutation not found, incomplete strategy% (29029)------------------------------
% 0.21/0.51  % (29029)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (29029)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (29029)Memory used [KB]: 10746
% 0.21/0.51  % (29029)Time elapsed: 0.094 s
% 0.21/0.51  % (29029)------------------------------
% 0.21/0.51  % (29029)------------------------------
% 0.21/0.51  % (29044)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (29035)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (29043)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (29036)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (29045)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.52  % (29026)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (29037)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (29034)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (29021)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (29021)Refutation not found, incomplete strategy% (29021)------------------------------
% 0.21/0.53  % (29021)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (29021)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (29021)Memory used [KB]: 1663
% 0.21/0.53  % (29021)Time elapsed: 0.115 s
% 0.21/0.53  % (29021)------------------------------
% 0.21/0.53  % (29021)------------------------------
% 0.21/0.53  % (29033)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (29038)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (29038)Refutation not found, incomplete strategy% (29038)------------------------------
% 0.21/0.54  % (29038)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (29038)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (29038)Memory used [KB]: 10618
% 0.21/0.54  % (29038)Time elapsed: 0.084 s
% 0.21/0.54  % (29038)------------------------------
% 0.21/0.54  % (29038)------------------------------
% 0.21/0.54  % (29023)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (29050)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (29023)Refutation not found, incomplete strategy% (29023)------------------------------
% 0.21/0.54  % (29023)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (29023)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (29023)Memory used [KB]: 10746
% 0.21/0.54  % (29023)Time elapsed: 0.133 s
% 0.21/0.54  % (29023)------------------------------
% 0.21/0.54  % (29023)------------------------------
% 0.21/0.54  % (29042)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (29030)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (29049)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (29042)Refutation not found, incomplete strategy% (29042)------------------------------
% 0.21/0.54  % (29042)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (29042)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (29042)Memory used [KB]: 1663
% 0.21/0.54  % (29042)Time elapsed: 0.128 s
% 0.21/0.54  % (29042)------------------------------
% 0.21/0.54  % (29042)------------------------------
% 1.39/0.54  % (29025)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.39/0.54  % (29031)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.39/0.55  % (29046)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.39/0.55  % (29032)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.39/0.55  % (29039)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.39/0.55  % (29041)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.39/0.55  % (29022)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.39/0.55  % (29040)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.39/0.55  % (29041)Refutation not found, incomplete strategy% (29041)------------------------------
% 1.39/0.55  % (29041)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (29041)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  
% 1.39/0.55  % (29041)Memory used [KB]: 10746
% 1.39/0.55  % (29041)Time elapsed: 0.140 s
% 1.39/0.55  % (29041)------------------------------
% 1.39/0.55  % (29041)------------------------------
% 1.39/0.56  % (29031)Refutation not found, incomplete strategy% (29031)------------------------------
% 1.39/0.56  % (29031)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (29031)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.56  
% 1.39/0.56  % (29031)Memory used [KB]: 10746
% 1.39/0.56  % (29031)Time elapsed: 0.127 s
% 1.39/0.56  % (29031)------------------------------
% 1.39/0.56  % (29031)------------------------------
% 1.53/0.57  % (29045)Refutation found. Thanks to Tanya!
% 1.53/0.57  % SZS status Theorem for theBenchmark
% 1.53/0.57  % SZS output start Proof for theBenchmark
% 1.53/0.57  fof(f964,plain,(
% 1.53/0.57    $false),
% 1.53/0.57    inference(global_subsumption,[],[f269,f950])).
% 1.53/0.57  fof(f950,plain,(
% 1.53/0.57    r2_hidden(k1_xboole_0,k1_xboole_0)),
% 1.53/0.57    inference(backward_demodulation,[],[f371,f852])).
% 1.53/0.57  fof(f852,plain,(
% 1.53/0.57    k1_xboole_0 = sK5(sK7(k1_xboole_0),k1_xboole_0)),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f460,f582])).
% 1.53/0.57  fof(f582,plain,(
% 1.53/0.57    ( ! [X0,X1] : (~sP4(X0,sK7(X1)) | k1_xboole_0 = X0) )),
% 1.53/0.57    inference(duplicate_literal_removal,[],[f575])).
% 1.53/0.57  fof(f575,plain,(
% 1.53/0.57    ( ! [X0,X1] : (~sP4(X0,sK7(X1)) | k1_xboole_0 = X0 | ~sP4(X0,sK7(X1))) )),
% 1.53/0.57    inference(resolution,[],[f203,f81])).
% 1.53/0.57  fof(f81,plain,(
% 1.53/0.57    ( ! [X0,X1] : (r2_hidden(sK5(sK7(X0),X1),X0) | ~sP4(X1,sK7(X0))) )),
% 1.53/0.57    inference(superposition,[],[f27,f37])).
% 1.53/0.57  fof(f37,plain,(
% 1.53/0.57    ( ! [X0] : (k1_relat_1(sK7(X0)) = X0) )),
% 1.53/0.57    inference(cnf_transformation,[],[f17])).
% 1.53/0.57  fof(f17,plain,(
% 1.53/0.57    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.53/0.57    inference(ennf_transformation,[],[f7])).
% 1.53/0.57  fof(f7,axiom,(
% 1.53/0.57    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).
% 1.53/0.57  fof(f27,plain,(
% 1.53/0.57    ( ! [X2,X0] : (r2_hidden(sK5(X0,X2),k1_relat_1(X0)) | ~sP4(X2,X0)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f15])).
% 1.53/0.57  fof(f15,plain,(
% 1.53/0.57    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.53/0.57    inference(flattening,[],[f14])).
% 1.53/0.57  fof(f14,plain,(
% 1.53/0.57    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.53/0.57    inference(ennf_transformation,[],[f6])).
% 1.53/0.57  fof(f6,axiom,(
% 1.53/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 1.53/0.57  fof(f203,plain,(
% 1.53/0.57    ( ! [X0,X1] : (~r2_hidden(sK5(sK7(X0),X1),X0) | ~sP4(X1,sK7(X0)) | k1_xboole_0 = X1) )),
% 1.53/0.57    inference(superposition,[],[f28,f34])).
% 1.53/0.57  fof(f34,plain,(
% 1.53/0.57    ( ! [X2,X0] : (k1_xboole_0 = k1_funct_1(sK7(X0),X2) | ~r2_hidden(X2,X0)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f17])).
% 1.53/0.57  fof(f28,plain,(
% 1.53/0.57    ( ! [X2,X0] : (k1_funct_1(X0,sK5(X0,X2)) = X2 | ~sP4(X2,X0)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f15])).
% 1.53/0.57  fof(f460,plain,(
% 1.53/0.57    ( ! [X0] : (sP4(sK5(sK7(k1_xboole_0),k1_xboole_0),sK7(X0))) )),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f35,f36,f398,f46])).
% 1.53/0.57  fof(f46,plain,(
% 1.53/0.57    ( ! [X2,X0] : (~r2_hidden(X2,k2_relat_1(X0)) | ~v1_funct_1(X0) | sP4(X2,X0) | ~v1_relat_1(X0)) )),
% 1.53/0.57    inference(equality_resolution,[],[f30])).
% 1.53/0.57  fof(f30,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | sP4(X2,X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.53/0.57    inference(cnf_transformation,[],[f15])).
% 1.53/0.57  fof(f398,plain,(
% 1.53/0.57    ( ! [X0] : (r2_hidden(sK5(sK7(k1_xboole_0),k1_xboole_0),X0)) )),
% 1.53/0.57    inference(global_subsumption,[],[f21,f397])).
% 1.53/0.57  fof(f397,plain,(
% 1.53/0.57    ( ! [X0] : (r2_hidden(sK5(sK7(k1_xboole_0),k1_xboole_0),X0) | ~r1_tarski(k1_xboole_0,X0)) )),
% 1.53/0.57    inference(forward_demodulation,[],[f375,f347])).
% 1.53/0.57  fof(f347,plain,(
% 1.53/0.57    k1_xboole_0 = sK1),
% 1.53/0.57    inference(global_subsumption,[],[f20,f180])).
% 1.53/0.57  fof(f180,plain,(
% 1.53/0.57    k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.53/0.57    inference(resolution,[],[f178,f33])).
% 1.53/0.57  fof(f33,plain,(
% 1.53/0.57    ( ! [X0] : (r2_hidden(sK6(X0),X0) | k1_xboole_0 = X0) )),
% 1.53/0.57    inference(cnf_transformation,[],[f16])).
% 1.53/0.57  fof(f16,plain,(
% 1.53/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.53/0.57    inference(ennf_transformation,[],[f2])).
% 1.53/0.57  fof(f2,axiom,(
% 1.53/0.57    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.53/0.57  fof(f178,plain,(
% 1.53/0.57    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_xboole_0 = sK1) )),
% 1.53/0.57    inference(resolution,[],[f177,f44])).
% 1.53/0.57  fof(f44,plain,(
% 1.53/0.57    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f5])).
% 1.53/0.57  fof(f5,axiom,(
% 1.53/0.57    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.53/0.57  fof(f177,plain,(
% 1.53/0.57    ( ! [X0] : (~r1_tarski(k1_tarski(X0),sK0) | k1_xboole_0 = sK1) )),
% 1.53/0.57    inference(duplicate_literal_removal,[],[f176])).
% 1.53/0.57  fof(f176,plain,(
% 1.53/0.57    ( ! [X0] : (~r1_tarski(k1_tarski(X0),sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK1) )),
% 1.53/0.57    inference(superposition,[],[f80,f25])).
% 1.53/0.57  fof(f25,plain,(
% 1.53/0.57    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.53/0.57    inference(cnf_transformation,[],[f13])).
% 1.53/0.57  fof(f13,plain,(
% 1.53/0.57    ! [X0] : (! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 1.53/0.57    inference(ennf_transformation,[],[f8])).
% 1.53/0.57  fof(f8,axiom,(
% 1.53/0.57    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).
% 1.53/0.57  fof(f80,plain,(
% 1.53/0.57    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2(sK1,X0)),sK0) | k1_xboole_0 = sK1) )),
% 1.53/0.57    inference(equality_resolution,[],[f74])).
% 1.53/0.57  fof(f74,plain,(
% 1.53/0.57    ( ! [X0,X1] : (sK1 != X0 | ~r1_tarski(k2_relat_1(sK2(X0,X1)),sK0) | k1_xboole_0 = X0) )),
% 1.53/0.57    inference(global_subsumption,[],[f23,f22,f73])).
% 1.53/0.57  fof(f73,plain,(
% 1.53/0.57    ( ! [X0,X1] : (sK1 != X0 | ~v1_funct_1(sK2(X0,X1)) | ~v1_relat_1(sK2(X0,X1)) | ~r1_tarski(k2_relat_1(sK2(X0,X1)),sK0) | k1_xboole_0 = X0) )),
% 1.53/0.57    inference(superposition,[],[f19,f24])).
% 1.53/0.57  fof(f24,plain,(
% 1.53/0.57    ( ! [X0,X1] : (k1_relat_1(sK2(X0,X1)) = X0 | k1_xboole_0 = X0) )),
% 1.53/0.57    inference(cnf_transformation,[],[f13])).
% 1.53/0.57  fof(f19,plain,(
% 1.53/0.57    ( ! [X2] : (k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),sK0)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f12])).
% 1.53/0.57  fof(f12,plain,(
% 1.53/0.57    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.53/0.57    inference(flattening,[],[f11])).
% 1.53/0.57  fof(f11,plain,(
% 1.53/0.57    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.53/0.57    inference(ennf_transformation,[],[f10])).
% 1.53/0.57  fof(f10,negated_conjecture,(
% 1.53/0.57    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.53/0.57    inference(negated_conjecture,[],[f9])).
% 1.53/0.57  fof(f9,conjecture,(
% 1.53/0.57    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).
% 1.53/0.57  fof(f22,plain,(
% 1.53/0.57    ( ! [X0,X1] : (v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.53/0.57    inference(cnf_transformation,[],[f13])).
% 1.53/0.57  fof(f23,plain,(
% 1.53/0.57    ( ! [X0,X1] : (v1_funct_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.53/0.57    inference(cnf_transformation,[],[f13])).
% 1.53/0.57  fof(f20,plain,(
% 1.53/0.57    k1_xboole_0 != sK0 | k1_xboole_0 = sK1),
% 1.53/0.57    inference(cnf_transformation,[],[f12])).
% 1.53/0.57  fof(f375,plain,(
% 1.53/0.57    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | r2_hidden(sK5(sK7(sK1),k1_xboole_0),X0)) )),
% 1.53/0.57    inference(backward_demodulation,[],[f285,f347])).
% 1.53/0.57  fof(f285,plain,(
% 1.53/0.57    ( ! [X0] : (r2_hidden(sK5(sK7(sK1),k1_xboole_0),X0) | ~r1_tarski(sK1,X0)) )),
% 1.53/0.57    inference(forward_demodulation,[],[f240,f242])).
% 1.53/0.57  fof(f242,plain,(
% 1.53/0.57    k1_xboole_0 = sK8(k2_relat_1(sK7(sK1)),sK0)),
% 1.53/0.57    inference(backward_demodulation,[],[f215,f238])).
% 1.53/0.57  fof(f238,plain,(
% 1.53/0.57    k1_xboole_0 = k1_funct_1(sK7(sK1),sK5(sK7(sK1),sK8(k2_relat_1(sK7(sK1)),sK0)))),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f218,f34])).
% 1.53/0.57  fof(f218,plain,(
% 1.53/0.57    r2_hidden(sK5(sK7(sK1),sK8(k2_relat_1(sK7(sK1)),sK0)),sK1)),
% 1.53/0.57    inference(forward_demodulation,[],[f216,f37])).
% 1.53/0.57  fof(f216,plain,(
% 1.53/0.57    r2_hidden(sK5(sK7(sK1),sK8(k2_relat_1(sK7(sK1)),sK0)),k1_relat_1(sK7(sK1)))),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f208,f27])).
% 1.53/0.57  fof(f208,plain,(
% 1.53/0.57    sP4(sK8(k2_relat_1(sK7(sK1)),sK0),sK7(sK1))),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f35,f36,f61,f46])).
% 1.53/0.57  fof(f61,plain,(
% 1.53/0.57    r2_hidden(sK8(k2_relat_1(sK7(sK1)),sK0),k2_relat_1(sK7(sK1)))),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f51,f42])).
% 1.53/0.57  fof(f42,plain,(
% 1.53/0.57    ( ! [X0,X1] : (r2_hidden(sK8(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f18])).
% 1.53/0.57  fof(f18,plain,(
% 1.53/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.53/0.57    inference(ennf_transformation,[],[f1])).
% 1.53/0.57  fof(f1,axiom,(
% 1.53/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.53/0.57  fof(f51,plain,(
% 1.53/0.57    ~r1_tarski(k2_relat_1(sK7(sK1)),sK0)),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f36,f35,f37,f19])).
% 1.53/0.57  fof(f215,plain,(
% 1.53/0.57    sK8(k2_relat_1(sK7(sK1)),sK0) = k1_funct_1(sK7(sK1),sK5(sK7(sK1),sK8(k2_relat_1(sK7(sK1)),sK0)))),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f208,f28])).
% 1.53/0.57  fof(f240,plain,(
% 1.53/0.57    ( ! [X0] : (r2_hidden(sK5(sK7(sK1),sK8(k2_relat_1(sK7(sK1)),sK0)),X0) | ~r1_tarski(sK1,X0)) )),
% 1.53/0.57    inference(resolution,[],[f218,f41])).
% 1.53/0.57  fof(f41,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f18])).
% 1.53/0.57  fof(f21,plain,(
% 1.53/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f4])).
% 1.53/0.57  fof(f4,axiom,(
% 1.53/0.57    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.53/0.57  fof(f36,plain,(
% 1.53/0.57    ( ! [X0] : (v1_funct_1(sK7(X0))) )),
% 1.53/0.57    inference(cnf_transformation,[],[f17])).
% 1.53/0.57  fof(f35,plain,(
% 1.53/0.57    ( ! [X0] : (v1_relat_1(sK7(X0))) )),
% 1.53/0.57    inference(cnf_transformation,[],[f17])).
% 1.53/0.57  fof(f371,plain,(
% 1.53/0.57    r2_hidden(sK5(sK7(k1_xboole_0),k1_xboole_0),k1_xboole_0)),
% 1.53/0.57    inference(backward_demodulation,[],[f279,f347])).
% 1.53/0.57  fof(f279,plain,(
% 1.53/0.57    r2_hidden(sK5(sK7(sK1),k1_xboole_0),sK1)),
% 1.53/0.57    inference(backward_demodulation,[],[f218,f242])).
% 1.53/0.57  fof(f269,plain,(
% 1.53/0.57    ~r2_hidden(k1_xboole_0,k1_xboole_0)),
% 1.53/0.57    inference(backward_demodulation,[],[f120,f242])).
% 1.53/0.57  fof(f120,plain,(
% 1.53/0.57    ~r2_hidden(sK8(k2_relat_1(sK7(sK1)),sK0),k1_xboole_0)),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f21,f110])).
% 1.53/0.57  fof(f110,plain,(
% 1.53/0.57    ~r2_hidden(sK8(k2_relat_1(sK7(sK1)),sK0),k1_xboole_0) | ~r1_tarski(k1_xboole_0,sK0)),
% 1.53/0.57    inference(superposition,[],[f66,f104])).
% 1.53/0.57  fof(f104,plain,(
% 1.53/0.57    ( ! [X0] : (k1_xboole_0 = k1_tarski(X0) | ~r2_hidden(X0,k1_xboole_0)) )),
% 1.53/0.57    inference(resolution,[],[f96,f44])).
% 1.53/0.57  fof(f96,plain,(
% 1.53/0.57    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.53/0.57    inference(resolution,[],[f40,f21])).
% 1.53/0.57  fof(f40,plain,(
% 1.53/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.53/0.57    inference(cnf_transformation,[],[f3])).
% 1.53/0.57  fof(f3,axiom,(
% 1.53/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.53/0.57  fof(f66,plain,(
% 1.53/0.57    ~r1_tarski(k1_tarski(sK8(k2_relat_1(sK7(sK1)),sK0)),sK0)),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f63,f45])).
% 1.53/0.57  fof(f45,plain,(
% 1.53/0.57    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f5])).
% 1.53/0.57  fof(f63,plain,(
% 1.53/0.57    ~r2_hidden(sK8(k2_relat_1(sK7(sK1)),sK0),sK0)),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f51,f43])).
% 1.53/0.57  fof(f43,plain,(
% 1.53/0.57    ( ! [X0,X1] : (~r2_hidden(sK8(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f18])).
% 1.53/0.57  % SZS output end Proof for theBenchmark
% 1.53/0.57  % (29045)------------------------------
% 1.53/0.57  % (29045)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.57  % (29045)Termination reason: Refutation
% 1.53/0.57  
% 1.53/0.57  % (29045)Memory used [KB]: 6908
% 1.53/0.57  % (29045)Time elapsed: 0.147 s
% 1.53/0.57  % (29045)------------------------------
% 1.53/0.57  % (29045)------------------------------
% 1.53/0.57  % (29047)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.53/0.58  % (29020)Success in time 0.208 s
%------------------------------------------------------------------------------
