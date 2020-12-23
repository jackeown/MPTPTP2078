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
% DateTime   : Thu Dec  3 12:53:25 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 122 expanded)
%              Number of leaves         :   12 (  29 expanded)
%              Depth                    :   19
%              Number of atoms          :  165 ( 298 expanded)
%              Number of equality atoms :   82 ( 138 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f198,plain,(
    $false ),
    inference(subsumption_resolution,[],[f193,f75])).

fof(f75,plain,(
    ! [X4,X0,X1] : r2_hidden(X4,k2_enumset1(X0,X0,X1,X4)) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X4,X0,X3,X1] :
      ( r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X4) != X3 ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f55,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f193,plain,(
    ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f187,f25])).

fof(f25,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k11_relat_1(X1,X0) != k1_tarski(k1_funct_1(X1,X0))
      & r2_hidden(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k11_relat_1(X1,X0) != k1_tarski(k1_funct_1(X1,X0))
      & r2_hidden(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r2_hidden(X0,k1_relat_1(X1))
         => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

fof(f187,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) ) ),
    inference(superposition,[],[f72,f175])).

fof(f175,plain,(
    k1_relat_1(sK1) = k4_xboole_0(k1_relat_1(sK1),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f167,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f167,plain,(
    r1_xboole_0(k1_relat_1(sK1),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(trivial_inequality_removal,[],[f161])).

fof(f161,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK1),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f100,f155])).

fof(f155,plain,(
    k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f148])).

fof(f148,plain,
    ( k11_relat_1(sK1,sK0) != k11_relat_1(sK1,sK0)
    | k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    inference(superposition,[],[f58,f146])).

fof(f146,plain,(
    ! [X0] :
      ( k11_relat_1(sK1,X0) = k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0))
      | k1_xboole_0 = k11_relat_1(sK1,X0) ) ),
    inference(equality_resolution,[],[f144])).

fof(f144,plain,(
    ! [X2,X3] :
      ( k1_funct_1(sK1,X2) != X3
      | k1_xboole_0 = k11_relat_1(sK1,X2)
      | k11_relat_1(sK1,X2) = k2_enumset1(X3,X3,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f143])).

fof(f143,plain,(
    ! [X2,X3] :
      ( k1_funct_1(sK1,X2) != X3
      | k1_xboole_0 = k11_relat_1(sK1,X2)
      | k11_relat_1(sK1,X2) = k2_enumset1(X3,X3,X3,X3)
      | k1_xboole_0 = k11_relat_1(sK1,X2)
      | k11_relat_1(sK1,X2) = k2_enumset1(X3,X3,X3,X3) ) ),
    inference(superposition,[],[f60,f95])).

fof(f95,plain,(
    ! [X6,X5] :
      ( k1_funct_1(sK1,X5) = sK2(k11_relat_1(sK1,X5),X6)
      | k1_xboole_0 = k11_relat_1(sK1,X5)
      | k11_relat_1(sK1,X5) = k2_enumset1(X6,X6,X6,X6) ) ),
    inference(resolution,[],[f91,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f34,f57])).

fof(f57,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f27,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f29,f36])).

fof(f29,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f27,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k11_relat_1(sK1,X0))
      | k1_funct_1(sK1,X0) = X1 ) ),
    inference(resolution,[],[f89,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,X0),sK1)
      | ~ r2_hidden(X0,k11_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f23,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

fof(f23,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f89,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),sK1)
      | k1_funct_1(sK1,X2) = X3 ) ),
    inference(subsumption_resolution,[],[f86,f23])).

fof(f86,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(sK1)
      | k1_funct_1(sK1,X2) = X3
      | ~ r2_hidden(k4_tarski(X2,X3),sK1) ) ),
    inference(resolution,[],[f24,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f24,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f60,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X1
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f35,f57])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | sK2(X0,X1) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f58,plain,(
    k11_relat_1(sK1,sK0) != k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) ),
    inference(definition_unfolding,[],[f26,f57])).

fof(f26,plain,(
    k11_relat_1(sK1,sK0) != k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f100,plain,(
    ! [X0] :
      ( k1_xboole_0 != k11_relat_1(sK1,X0)
      | r1_xboole_0(k1_relat_1(sK1),k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(subsumption_resolution,[],[f99,f23])).

fof(f99,plain,(
    ! [X0] :
      ( k1_xboole_0 != k11_relat_1(sK1,X0)
      | r1_xboole_0(k1_relat_1(sK1),k2_enumset1(X0,X0,X0,X0))
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f31,f84])).

fof(f84,plain,(
    ! [X5] : k11_relat_1(sK1,X5) = k9_relat_1(sK1,k2_enumset1(X5,X5,X5,X5)) ),
    inference(resolution,[],[f23,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f28,f57])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

% (29331)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.15  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 14:58:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.53  % (29323)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.23/0.53  % (29324)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.23/0.54  % (29341)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.23/0.54  % (29322)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.23/0.54  % (29334)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.23/0.54  % (29326)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.23/0.55  % (29320)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.23/0.55  % (29340)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.44/0.55  % (29327)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.44/0.55  % (29345)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.44/0.55  % (29342)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.44/0.55  % (29341)Refutation found. Thanks to Tanya!
% 1.44/0.55  % SZS status Theorem for theBenchmark
% 1.44/0.55  % (29348)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.44/0.55  % SZS output start Proof for theBenchmark
% 1.44/0.55  fof(f198,plain,(
% 1.44/0.55    $false),
% 1.44/0.55    inference(subsumption_resolution,[],[f193,f75])).
% 1.44/0.55  fof(f75,plain,(
% 1.44/0.55    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_enumset1(X0,X0,X1,X4))) )),
% 1.44/0.55    inference(equality_resolution,[],[f74])).
% 1.44/0.55  fof(f74,plain,(
% 1.44/0.55    ( ! [X4,X0,X3,X1] : (r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X4) != X3) )),
% 1.44/0.55    inference(equality_resolution,[],[f62])).
% 1.44/0.55  fof(f62,plain,(
% 1.44/0.55    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.44/0.55    inference(definition_unfolding,[],[f55,f36])).
% 1.44/0.55  fof(f36,plain,(
% 1.44/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f6])).
% 1.44/0.55  fof(f6,axiom,(
% 1.44/0.55    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.44/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.44/0.55  fof(f55,plain,(
% 1.44/0.55    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.44/0.55    inference(cnf_transformation,[],[f22])).
% 1.44/0.55  fof(f22,plain,(
% 1.44/0.55    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.44/0.55    inference(ennf_transformation,[],[f3])).
% 1.44/0.55  fof(f3,axiom,(
% 1.44/0.55    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.44/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.44/0.55  fof(f193,plain,(
% 1.44/0.55    ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.44/0.55    inference(resolution,[],[f187,f25])).
% 1.44/0.55  fof(f25,plain,(
% 1.44/0.55    r2_hidden(sK0,k1_relat_1(sK1))),
% 1.44/0.55    inference(cnf_transformation,[],[f15])).
% 1.44/0.55  fof(f15,plain,(
% 1.44/0.55    ? [X0,X1] : (k11_relat_1(X1,X0) != k1_tarski(k1_funct_1(X1,X0)) & r2_hidden(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.44/0.55    inference(flattening,[],[f14])).
% 1.44/0.55  fof(f14,plain,(
% 1.44/0.55    ? [X0,X1] : ((k11_relat_1(X1,X0) != k1_tarski(k1_funct_1(X1,X0)) & r2_hidden(X0,k1_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.44/0.55    inference(ennf_transformation,[],[f13])).
% 1.44/0.55  fof(f13,negated_conjecture,(
% 1.44/0.55    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.44/0.55    inference(negated_conjecture,[],[f12])).
% 1.44/0.55  fof(f12,conjecture,(
% 1.44/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.44/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).
% 1.44/0.55  fof(f187,plain,(
% 1.44/0.55    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | ~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))) )),
% 1.44/0.55    inference(superposition,[],[f72,f175])).
% 1.44/0.55  fof(f175,plain,(
% 1.44/0.55    k1_relat_1(sK1) = k4_xboole_0(k1_relat_1(sK1),k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.44/0.55    inference(resolution,[],[f167,f33])).
% 1.44/0.55  fof(f33,plain,(
% 1.44/0.55    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 1.44/0.55    inference(cnf_transformation,[],[f2])).
% 1.44/0.55  fof(f2,axiom,(
% 1.44/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.44/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.44/0.55  fof(f167,plain,(
% 1.44/0.55    r1_xboole_0(k1_relat_1(sK1),k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.44/0.55    inference(trivial_inequality_removal,[],[f161])).
% 1.44/0.55  fof(f161,plain,(
% 1.44/0.55    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_relat_1(sK1),k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.44/0.55    inference(superposition,[],[f100,f155])).
% 1.44/0.55  fof(f155,plain,(
% 1.44/0.55    k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 1.44/0.55    inference(trivial_inequality_removal,[],[f148])).
% 1.44/0.55  fof(f148,plain,(
% 1.44/0.55    k11_relat_1(sK1,sK0) != k11_relat_1(sK1,sK0) | k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 1.44/0.55    inference(superposition,[],[f58,f146])).
% 1.44/0.55  fof(f146,plain,(
% 1.44/0.55    ( ! [X0] : (k11_relat_1(sK1,X0) = k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0)) | k1_xboole_0 = k11_relat_1(sK1,X0)) )),
% 1.44/0.55    inference(equality_resolution,[],[f144])).
% 1.44/0.55  fof(f144,plain,(
% 1.44/0.55    ( ! [X2,X3] : (k1_funct_1(sK1,X2) != X3 | k1_xboole_0 = k11_relat_1(sK1,X2) | k11_relat_1(sK1,X2) = k2_enumset1(X3,X3,X3,X3)) )),
% 1.44/0.55    inference(duplicate_literal_removal,[],[f143])).
% 1.44/0.55  fof(f143,plain,(
% 1.44/0.55    ( ! [X2,X3] : (k1_funct_1(sK1,X2) != X3 | k1_xboole_0 = k11_relat_1(sK1,X2) | k11_relat_1(sK1,X2) = k2_enumset1(X3,X3,X3,X3) | k1_xboole_0 = k11_relat_1(sK1,X2) | k11_relat_1(sK1,X2) = k2_enumset1(X3,X3,X3,X3)) )),
% 1.44/0.55    inference(superposition,[],[f60,f95])).
% 1.44/0.55  fof(f95,plain,(
% 1.44/0.55    ( ! [X6,X5] : (k1_funct_1(sK1,X5) = sK2(k11_relat_1(sK1,X5),X6) | k1_xboole_0 = k11_relat_1(sK1,X5) | k11_relat_1(sK1,X5) = k2_enumset1(X6,X6,X6,X6)) )),
% 1.44/0.55    inference(resolution,[],[f91,f61])).
% 1.44/0.55  fof(f61,plain,(
% 1.44/0.55    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 1.44/0.55    inference(definition_unfolding,[],[f34,f57])).
% 1.44/0.55  fof(f57,plain,(
% 1.44/0.55    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.44/0.55    inference(definition_unfolding,[],[f27,f56])).
% 1.44/0.55  fof(f56,plain,(
% 1.44/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.44/0.55    inference(definition_unfolding,[],[f29,f36])).
% 1.44/0.55  fof(f29,plain,(
% 1.44/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f5])).
% 1.44/0.55  fof(f5,axiom,(
% 1.44/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.44/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.44/0.55  fof(f27,plain,(
% 1.44/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f4])).
% 1.44/0.55  fof(f4,axiom,(
% 1.44/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.44/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.44/0.55  fof(f34,plain,(
% 1.44/0.55    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | r2_hidden(sK2(X0,X1),X0)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f18])).
% 1.44/0.55  fof(f18,plain,(
% 1.44/0.55    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 1.44/0.55    inference(ennf_transformation,[],[f7])).
% 1.44/0.55  fof(f7,axiom,(
% 1.44/0.55    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 1.44/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).
% 1.44/0.55  fof(f91,plain,(
% 1.44/0.55    ( ! [X0,X1] : (~r2_hidden(X1,k11_relat_1(sK1,X0)) | k1_funct_1(sK1,X0) = X1) )),
% 1.44/0.55    inference(resolution,[],[f89,f81])).
% 1.44/0.55  fof(f81,plain,(
% 1.44/0.55    ( ! [X0,X1] : (r2_hidden(k4_tarski(X1,X0),sK1) | ~r2_hidden(X0,k11_relat_1(sK1,X1))) )),
% 1.44/0.55    inference(resolution,[],[f23,f37])).
% 1.44/0.55  fof(f37,plain,(
% 1.44/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X1,k11_relat_1(X2,X0)) | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f19])).
% 1.44/0.56  fof(f19,plain,(
% 1.44/0.56    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 1.44/0.56    inference(ennf_transformation,[],[f10])).
% 1.44/0.56  fof(f10,axiom,(
% 1.44/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).
% 1.44/0.56  fof(f23,plain,(
% 1.44/0.56    v1_relat_1(sK1)),
% 1.44/0.56    inference(cnf_transformation,[],[f15])).
% 1.44/0.56  fof(f89,plain,(
% 1.44/0.56    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK1) | k1_funct_1(sK1,X2) = X3) )),
% 1.44/0.56    inference(subsumption_resolution,[],[f86,f23])).
% 1.44/0.56  fof(f86,plain,(
% 1.44/0.56    ( ! [X2,X3] : (~v1_relat_1(sK1) | k1_funct_1(sK1,X2) = X3 | ~r2_hidden(k4_tarski(X2,X3),sK1)) )),
% 1.44/0.56    inference(resolution,[],[f24,f40])).
% 1.44/0.56  fof(f40,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f21])).
% 1.44/0.56  fof(f21,plain,(
% 1.44/0.56    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.44/0.56    inference(flattening,[],[f20])).
% 1.44/0.56  fof(f20,plain,(
% 1.44/0.56    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.44/0.56    inference(ennf_transformation,[],[f11])).
% 1.44/0.56  fof(f11,axiom,(
% 1.44/0.56    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 1.44/0.56  fof(f24,plain,(
% 1.44/0.56    v1_funct_1(sK1)),
% 1.44/0.56    inference(cnf_transformation,[],[f15])).
% 1.44/0.56  fof(f60,plain,(
% 1.44/0.56    ( ! [X0,X1] : (sK2(X0,X1) != X1 | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 1.44/0.56    inference(definition_unfolding,[],[f35,f57])).
% 1.44/0.56  fof(f35,plain,(
% 1.44/0.56    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | sK2(X0,X1) != X1) )),
% 1.44/0.56    inference(cnf_transformation,[],[f18])).
% 1.44/0.56  fof(f58,plain,(
% 1.44/0.56    k11_relat_1(sK1,sK0) != k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))),
% 1.44/0.56    inference(definition_unfolding,[],[f26,f57])).
% 1.44/0.56  fof(f26,plain,(
% 1.44/0.56    k11_relat_1(sK1,sK0) != k1_tarski(k1_funct_1(sK1,sK0))),
% 1.44/0.56    inference(cnf_transformation,[],[f15])).
% 1.44/0.56  fof(f100,plain,(
% 1.44/0.56    ( ! [X0] : (k1_xboole_0 != k11_relat_1(sK1,X0) | r1_xboole_0(k1_relat_1(sK1),k2_enumset1(X0,X0,X0,X0))) )),
% 1.44/0.56    inference(subsumption_resolution,[],[f99,f23])).
% 1.44/0.56  fof(f99,plain,(
% 1.44/0.56    ( ! [X0] : (k1_xboole_0 != k11_relat_1(sK1,X0) | r1_xboole_0(k1_relat_1(sK1),k2_enumset1(X0,X0,X0,X0)) | ~v1_relat_1(sK1)) )),
% 1.44/0.56    inference(superposition,[],[f31,f84])).
% 1.44/0.56  fof(f84,plain,(
% 1.44/0.56    ( ! [X5] : (k11_relat_1(sK1,X5) = k9_relat_1(sK1,k2_enumset1(X5,X5,X5,X5))) )),
% 1.44/0.56    inference(resolution,[],[f23,f59])).
% 1.44/0.56  fof(f59,plain,(
% 1.44/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 1.44/0.56    inference(definition_unfolding,[],[f28,f57])).
% 1.44/0.56  fof(f28,plain,(
% 1.44/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))) )),
% 1.44/0.56    inference(cnf_transformation,[],[f16])).
% 1.44/0.56  fof(f16,plain,(
% 1.44/0.56    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 1.44/0.56    inference(ennf_transformation,[],[f8])).
% 1.44/0.56  fof(f8,axiom,(
% 1.44/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).
% 1.44/0.56  fof(f31,plain,(
% 1.44/0.56    ( ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f17])).
% 1.44/0.56  % (29331)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.44/0.56  fof(f17,plain,(
% 1.44/0.56    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.44/0.56    inference(ennf_transformation,[],[f9])).
% 1.44/0.56  fof(f9,axiom,(
% 1.44/0.56    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).
% 1.44/0.56  fof(f72,plain,(
% 1.44/0.56    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 1.44/0.56    inference(equality_resolution,[],[f46])).
% 1.44/0.56  fof(f46,plain,(
% 1.44/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.44/0.56    inference(cnf_transformation,[],[f1])).
% 1.44/0.56  fof(f1,axiom,(
% 1.44/0.56    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.44/0.56  % SZS output end Proof for theBenchmark
% 1.44/0.56  % (29341)------------------------------
% 1.44/0.56  % (29341)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (29341)Termination reason: Refutation
% 1.44/0.56  
% 1.44/0.56  % (29341)Memory used [KB]: 1791
% 1.44/0.56  % (29341)Time elapsed: 0.070 s
% 1.44/0.56  % (29341)------------------------------
% 1.44/0.56  % (29341)------------------------------
% 1.44/0.56  % (29331)Refutation not found, incomplete strategy% (29331)------------------------------
% 1.44/0.56  % (29331)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (29325)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.44/0.56  % (29314)Success in time 0.185 s
%------------------------------------------------------------------------------
