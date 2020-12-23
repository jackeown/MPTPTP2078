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
% DateTime   : Thu Dec  3 12:51:53 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 171 expanded)
%              Number of leaves         :   11 (  42 expanded)
%              Depth                    :   24
%              Number of atoms          :  180 ( 423 expanded)
%              Number of equality atoms :   59 ( 183 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f278,plain,(
    $false ),
    inference(subsumption_resolution,[],[f277,f75])).

fof(f75,plain,(
    r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) ),
    inference(superposition,[],[f61,f48])).

fof(f48,plain,(
    k1_relat_1(sK1) = k2_tarski(sK0,sK0) ),
    inference(definition_unfolding,[],[f24,f26])).

fof(f26,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f24,plain,(
    k1_tarski(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_tarski(X0) = k1_relat_1(X1)
         => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(f61,plain,(
    ! [X1] : r1_tarski(k2_tarski(X1,X1),k2_tarski(X1,X1)) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) != X0
      | r1_tarski(X0,k2_tarski(X1,X1)) ) ),
    inference(definition_unfolding,[],[f43,f26,f26])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) != X0
      | r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f277,plain,(
    ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f275,f48])).

fof(f275,plain,(
    ~ r1_tarski(k2_tarski(sK0,sK0),k1_relat_1(sK1)) ),
    inference(resolution,[],[f273,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k2_tarski(X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f45,f26])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f273,plain,(
    ~ r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(resolution,[],[f264,f74])).

fof(f74,plain,(
    ! [X5] :
      ( ~ r1_xboole_0(k1_relat_1(sK1),X5)
      | ~ r2_hidden(sK0,X5) ) ),
    inference(superposition,[],[f56,f48])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k2_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f26])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f264,plain,(
    r1_xboole_0(k1_relat_1(sK1),k1_relat_1(sK1)) ),
    inference(trivial_inequality_removal,[],[f246])).

fof(f246,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK1),k1_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f81,f241])).

fof(f241,plain,(
    k1_xboole_0 = k2_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f240,f47])).

fof(f47,plain,(
    k2_relat_1(sK1) != k2_tarski(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) ),
    inference(definition_unfolding,[],[f25,f26])).

fof(f25,plain,(
    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f240,plain,
    ( k2_relat_1(sK1) = k2_tarski(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))
    | k1_xboole_0 = k2_relat_1(sK1) ),
    inference(resolution,[],[f238,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_tarski(X1,X1))
      | k2_tarski(X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f41,f26,f26])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f238,plain,(
    ! [X1] : r1_tarski(k2_relat_1(sK1),k2_tarski(k1_funct_1(sK1,sK0),X1)) ),
    inference(resolution,[],[f224,f49])).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(k2_tarski(X0,X0),k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f34,f26])).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f224,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_tarski(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)),X0)
      | r1_tarski(k2_relat_1(sK1),X0) ) ),
    inference(resolution,[],[f220,f54])).

fof(f220,plain,(
    ! [X2] :
      ( ~ r2_hidden(k1_funct_1(sK1,sK0),X2)
      | r1_tarski(k2_relat_1(sK1),X2) ) ),
    inference(duplicate_literal_removal,[],[f219])).

fof(f219,plain,(
    ! [X2] :
      ( ~ r2_hidden(k1_funct_1(sK1,sK0),X2)
      | r1_tarski(k2_relat_1(sK1),X2)
      | r1_tarski(k2_relat_1(sK1),X2) ) ),
    inference(superposition,[],[f40,f214])).

fof(f214,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,sK0) = sK5(k2_relat_1(sK1),X0)
      | r1_tarski(k2_relat_1(sK1),X0) ) ),
    inference(subsumption_resolution,[],[f210,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f210,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,sK0) = sK5(k2_relat_1(sK1),X0)
      | r1_tarski(k2_relat_1(sK1),X0)
      | ~ r2_hidden(sK5(k2_relat_1(sK1),X0),k2_relat_1(sK1)) ) ),
    inference(superposition,[],[f119,f97])).

fof(f97,plain,(
    ! [X3] :
      ( sK0 = sK3(sK1,X3)
      | ~ r2_hidden(X3,k2_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f96,f22])).

fof(f22,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f96,plain,(
    ! [X3] :
      ( sK0 = sK3(sK1,X3)
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(X3,k2_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f93,f23])).

fof(f23,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f93,plain,(
    ! [X3] :
      ( sK0 = sK3(sK1,X3)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(X3,k2_relat_1(sK1)) ) ),
    inference(resolution,[],[f89,f60])).

fof(f60,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK3(X0,X2),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK3(X0,X2),k1_relat_1(X0))
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f89,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | sK0 = X0 ) ),
    inference(resolution,[],[f71,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f26])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f71,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_tarski(X2,X2),k1_relat_1(sK1))
      | sK0 = X2 ) ),
    inference(superposition,[],[f50,f48])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X0),k2_tarski(X1,X1))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f37,f26,f26])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(f119,plain,(
    ! [X4] :
      ( sK5(k2_relat_1(sK1),X4) = k1_funct_1(sK1,sK3(sK1,sK5(k2_relat_1(sK1),X4)))
      | r1_tarski(k2_relat_1(sK1),X4) ) ),
    inference(resolution,[],[f68,f39])).

fof(f68,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_relat_1(sK1))
      | k1_funct_1(sK1,sK3(sK1,X1)) = X1 ) ),
    inference(subsumption_resolution,[],[f66,f22])).

fof(f66,plain,(
    ! [X1] :
      ( ~ v1_relat_1(sK1)
      | k1_funct_1(sK1,sK3(sK1,X1)) = X1
      | ~ r2_hidden(X1,k2_relat_1(sK1)) ) ),
    inference(resolution,[],[f23,f59])).

fof(f59,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_funct_1(X0,sK3(X0,X2)) = X2
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK3(X0,X2)) = X2
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f81,plain,
    ( k1_xboole_0 != k2_relat_1(sK1)
    | r1_xboole_0(k1_relat_1(sK1),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f80,f22])).

fof(f80,plain,
    ( k1_xboole_0 != k2_relat_1(sK1)
    | r1_xboole_0(k1_relat_1(sK1),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f36,f64])).

fof(f64,plain,(
    k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1)) ),
    inference(resolution,[],[f22,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:12:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (10034)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.49  % (10045)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (10029)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (10052)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (10036)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.34/0.54  % (10027)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.34/0.54  % (10033)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.34/0.54  % (10026)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.34/0.54  % (10027)Refutation not found, incomplete strategy% (10027)------------------------------
% 1.34/0.54  % (10027)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (10027)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (10027)Memory used [KB]: 10746
% 1.34/0.54  % (10027)Time elapsed: 0.125 s
% 1.34/0.54  % (10027)------------------------------
% 1.34/0.54  % (10027)------------------------------
% 1.34/0.54  % (10047)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.34/0.54  % (10039)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.34/0.54  % (10030)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.34/0.54  % (10054)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.34/0.54  % (10042)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.34/0.55  % (10037)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.34/0.55  % (10028)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.34/0.55  % (10041)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.34/0.55  % (10025)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.34/0.55  % (10035)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.34/0.55  % (10053)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.34/0.55  % (10044)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.34/0.55  % (10049)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.34/0.55  % (10040)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.34/0.55  % (10046)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.34/0.55  % (10048)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.34/0.55  % (10051)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.34/0.56  % (10031)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.53/0.56  % (10050)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.53/0.56  % (10038)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.53/0.56  % (10043)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.53/0.56  % (10032)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.53/0.58  % (10046)Refutation found. Thanks to Tanya!
% 1.53/0.58  % SZS status Theorem for theBenchmark
% 1.53/0.58  % SZS output start Proof for theBenchmark
% 1.53/0.58  fof(f278,plain,(
% 1.53/0.58    $false),
% 1.53/0.58    inference(subsumption_resolution,[],[f277,f75])).
% 1.53/0.58  fof(f75,plain,(
% 1.53/0.58    r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))),
% 1.53/0.58    inference(superposition,[],[f61,f48])).
% 1.53/0.58  fof(f48,plain,(
% 1.53/0.58    k1_relat_1(sK1) = k2_tarski(sK0,sK0)),
% 1.53/0.58    inference(definition_unfolding,[],[f24,f26])).
% 1.53/0.58  fof(f26,plain,(
% 1.53/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f2])).
% 1.53/0.58  fof(f2,axiom,(
% 1.53/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.53/0.58  fof(f24,plain,(
% 1.53/0.58    k1_tarski(sK0) = k1_relat_1(sK1)),
% 1.53/0.58    inference(cnf_transformation,[],[f14])).
% 1.53/0.58  fof(f14,plain,(
% 1.53/0.58    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.53/0.58    inference(flattening,[],[f13])).
% 1.53/0.58  fof(f13,plain,(
% 1.53/0.58    ? [X0,X1] : ((k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.53/0.58    inference(ennf_transformation,[],[f12])).
% 1.53/0.58  fof(f12,negated_conjecture,(
% 1.53/0.58    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.53/0.58    inference(negated_conjecture,[],[f11])).
% 1.53/0.58  fof(f11,conjecture,(
% 1.53/0.58    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).
% 1.53/0.58  fof(f61,plain,(
% 1.53/0.58    ( ! [X1] : (r1_tarski(k2_tarski(X1,X1),k2_tarski(X1,X1))) )),
% 1.53/0.58    inference(equality_resolution,[],[f51])).
% 1.53/0.58  fof(f51,plain,(
% 1.53/0.58    ( ! [X0,X1] : (k2_tarski(X1,X1) != X0 | r1_tarski(X0,k2_tarski(X1,X1))) )),
% 1.53/0.58    inference(definition_unfolding,[],[f43,f26,f26])).
% 1.53/0.58  fof(f43,plain,(
% 1.53/0.58    ( ! [X0,X1] : (k1_tarski(X1) != X0 | r1_tarski(X0,k1_tarski(X1))) )),
% 1.53/0.58    inference(cnf_transformation,[],[f5])).
% 1.53/0.58  fof(f5,axiom,(
% 1.53/0.58    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.53/0.58  fof(f277,plain,(
% 1.53/0.58    ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))),
% 1.53/0.58    inference(forward_demodulation,[],[f275,f48])).
% 1.53/0.58  fof(f275,plain,(
% 1.53/0.58    ~r1_tarski(k2_tarski(sK0,sK0),k1_relat_1(sK1))),
% 1.53/0.58    inference(resolution,[],[f273,f54])).
% 1.53/0.58  fof(f54,plain,(
% 1.53/0.58    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k2_tarski(X0,X0),X1)) )),
% 1.53/0.58    inference(definition_unfolding,[],[f45,f26])).
% 1.53/0.58  fof(f45,plain,(
% 1.53/0.58    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f3])).
% 1.53/0.58  fof(f3,axiom,(
% 1.53/0.58    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.53/0.58  fof(f273,plain,(
% 1.53/0.58    ~r2_hidden(sK0,k1_relat_1(sK1))),
% 1.53/0.58    inference(resolution,[],[f264,f74])).
% 1.53/0.58  fof(f74,plain,(
% 1.53/0.58    ( ! [X5] : (~r1_xboole_0(k1_relat_1(sK1),X5) | ~r2_hidden(sK0,X5)) )),
% 1.53/0.58    inference(superposition,[],[f56,f48])).
% 1.53/0.58  fof(f56,plain,(
% 1.53/0.58    ( ! [X0,X1] : (~r1_xboole_0(k2_tarski(X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.53/0.58    inference(definition_unfolding,[],[f46,f26])).
% 1.53/0.58  fof(f46,plain,(
% 1.53/0.58    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f21])).
% 1.53/0.58  fof(f21,plain,(
% 1.53/0.58    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 1.53/0.58    inference(ennf_transformation,[],[f4])).
% 1.53/0.58  fof(f4,axiom,(
% 1.53/0.58    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 1.53/0.58  fof(f264,plain,(
% 1.53/0.58    r1_xboole_0(k1_relat_1(sK1),k1_relat_1(sK1))),
% 1.53/0.58    inference(trivial_inequality_removal,[],[f246])).
% 1.53/0.58  fof(f246,plain,(
% 1.53/0.58    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_relat_1(sK1),k1_relat_1(sK1))),
% 1.53/0.58    inference(backward_demodulation,[],[f81,f241])).
% 1.53/0.58  fof(f241,plain,(
% 1.53/0.58    k1_xboole_0 = k2_relat_1(sK1)),
% 1.53/0.58    inference(subsumption_resolution,[],[f240,f47])).
% 1.53/0.58  fof(f47,plain,(
% 1.53/0.58    k2_relat_1(sK1) != k2_tarski(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))),
% 1.53/0.58    inference(definition_unfolding,[],[f25,f26])).
% 1.53/0.58  fof(f25,plain,(
% 1.53/0.58    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))),
% 1.53/0.58    inference(cnf_transformation,[],[f14])).
% 1.53/0.58  fof(f240,plain,(
% 1.53/0.58    k2_relat_1(sK1) = k2_tarski(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) | k1_xboole_0 = k2_relat_1(sK1)),
% 1.53/0.58    inference(resolution,[],[f238,f53])).
% 1.53/0.58  fof(f53,plain,(
% 1.53/0.58    ( ! [X0,X1] : (~r1_tarski(X0,k2_tarski(X1,X1)) | k2_tarski(X1,X1) = X0 | k1_xboole_0 = X0) )),
% 1.53/0.58    inference(definition_unfolding,[],[f41,f26,f26])).
% 1.53/0.58  fof(f41,plain,(
% 1.53/0.58    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.53/0.58    inference(cnf_transformation,[],[f5])).
% 1.53/0.58  fof(f238,plain,(
% 1.53/0.58    ( ! [X1] : (r1_tarski(k2_relat_1(sK1),k2_tarski(k1_funct_1(sK1,sK0),X1))) )),
% 1.53/0.58    inference(resolution,[],[f224,f49])).
% 1.53/0.58  fof(f49,plain,(
% 1.53/0.58    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X0),k2_tarski(X0,X1))) )),
% 1.53/0.58    inference(definition_unfolding,[],[f34,f26])).
% 1.53/0.58  fof(f34,plain,(
% 1.53/0.58    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 1.53/0.58    inference(cnf_transformation,[],[f6])).
% 1.53/0.58  fof(f6,axiom,(
% 1.53/0.58    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 1.53/0.58  fof(f224,plain,(
% 1.53/0.58    ( ! [X0] : (~r1_tarski(k2_tarski(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)),X0) | r1_tarski(k2_relat_1(sK1),X0)) )),
% 1.53/0.58    inference(resolution,[],[f220,f54])).
% 1.53/0.58  fof(f220,plain,(
% 1.53/0.58    ( ! [X2] : (~r2_hidden(k1_funct_1(sK1,sK0),X2) | r1_tarski(k2_relat_1(sK1),X2)) )),
% 1.53/0.58    inference(duplicate_literal_removal,[],[f219])).
% 1.53/0.58  fof(f219,plain,(
% 1.53/0.58    ( ! [X2] : (~r2_hidden(k1_funct_1(sK1,sK0),X2) | r1_tarski(k2_relat_1(sK1),X2) | r1_tarski(k2_relat_1(sK1),X2)) )),
% 1.53/0.58    inference(superposition,[],[f40,f214])).
% 1.53/0.58  fof(f214,plain,(
% 1.53/0.58    ( ! [X0] : (k1_funct_1(sK1,sK0) = sK5(k2_relat_1(sK1),X0) | r1_tarski(k2_relat_1(sK1),X0)) )),
% 1.53/0.58    inference(subsumption_resolution,[],[f210,f39])).
% 1.53/0.58  fof(f39,plain,(
% 1.53/0.58    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f20])).
% 1.53/0.58  fof(f20,plain,(
% 1.53/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.53/0.58    inference(ennf_transformation,[],[f1])).
% 1.53/0.58  fof(f1,axiom,(
% 1.53/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.53/0.58  fof(f210,plain,(
% 1.53/0.58    ( ! [X0] : (k1_funct_1(sK1,sK0) = sK5(k2_relat_1(sK1),X0) | r1_tarski(k2_relat_1(sK1),X0) | ~r2_hidden(sK5(k2_relat_1(sK1),X0),k2_relat_1(sK1))) )),
% 1.53/0.58    inference(superposition,[],[f119,f97])).
% 1.53/0.58  fof(f97,plain,(
% 1.53/0.58    ( ! [X3] : (sK0 = sK3(sK1,X3) | ~r2_hidden(X3,k2_relat_1(sK1))) )),
% 1.53/0.58    inference(subsumption_resolution,[],[f96,f22])).
% 1.53/0.58  fof(f22,plain,(
% 1.53/0.58    v1_relat_1(sK1)),
% 1.53/0.58    inference(cnf_transformation,[],[f14])).
% 1.53/0.58  fof(f96,plain,(
% 1.53/0.58    ( ! [X3] : (sK0 = sK3(sK1,X3) | ~v1_relat_1(sK1) | ~r2_hidden(X3,k2_relat_1(sK1))) )),
% 1.53/0.58    inference(subsumption_resolution,[],[f93,f23])).
% 1.53/0.58  fof(f23,plain,(
% 1.53/0.58    v1_funct_1(sK1)),
% 1.53/0.58    inference(cnf_transformation,[],[f14])).
% 1.53/0.58  fof(f93,plain,(
% 1.53/0.58    ( ! [X3] : (sK0 = sK3(sK1,X3) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~r2_hidden(X3,k2_relat_1(sK1))) )),
% 1.53/0.58    inference(resolution,[],[f89,f60])).
% 1.53/0.58  fof(f60,plain,(
% 1.53/0.58    ( ! [X2,X0] : (r2_hidden(sK3(X0,X2),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 1.53/0.58    inference(equality_resolution,[],[f31])).
% 1.53/0.58  fof(f31,plain,(
% 1.53/0.58    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK3(X0,X2),k1_relat_1(X0)) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.53/0.58    inference(cnf_transformation,[],[f17])).
% 1.53/0.58  fof(f17,plain,(
% 1.53/0.58    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.53/0.58    inference(flattening,[],[f16])).
% 1.53/0.58  fof(f16,plain,(
% 1.53/0.58    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.53/0.58    inference(ennf_transformation,[],[f10])).
% 1.53/0.58  fof(f10,axiom,(
% 1.53/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 1.53/0.58  fof(f89,plain,(
% 1.53/0.58    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | sK0 = X0) )),
% 1.53/0.58    inference(resolution,[],[f71,f55])).
% 1.53/0.58  fof(f55,plain,(
% 1.53/0.58    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.53/0.58    inference(definition_unfolding,[],[f44,f26])).
% 1.53/0.58  fof(f44,plain,(
% 1.53/0.58    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f3])).
% 1.53/0.58  fof(f71,plain,(
% 1.53/0.58    ( ! [X2] : (~r1_tarski(k2_tarski(X2,X2),k1_relat_1(sK1)) | sK0 = X2) )),
% 1.53/0.58    inference(superposition,[],[f50,f48])).
% 1.53/0.58  fof(f50,plain,(
% 1.53/0.58    ( ! [X0,X1] : (~r1_tarski(k2_tarski(X0,X0),k2_tarski(X1,X1)) | X0 = X1) )),
% 1.53/0.58    inference(definition_unfolding,[],[f37,f26,f26])).
% 1.53/0.58  fof(f37,plain,(
% 1.53/0.58    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 1.53/0.58    inference(cnf_transformation,[],[f19])).
% 1.53/0.58  fof(f19,plain,(
% 1.53/0.58    ! [X0,X1] : (X0 = X1 | ~r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 1.53/0.58    inference(ennf_transformation,[],[f7])).
% 1.53/0.58  fof(f7,axiom,(
% 1.53/0.58    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).
% 1.53/0.58  fof(f119,plain,(
% 1.53/0.58    ( ! [X4] : (sK5(k2_relat_1(sK1),X4) = k1_funct_1(sK1,sK3(sK1,sK5(k2_relat_1(sK1),X4))) | r1_tarski(k2_relat_1(sK1),X4)) )),
% 1.53/0.58    inference(resolution,[],[f68,f39])).
% 1.53/0.58  fof(f68,plain,(
% 1.53/0.58    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(sK1)) | k1_funct_1(sK1,sK3(sK1,X1)) = X1) )),
% 1.53/0.58    inference(subsumption_resolution,[],[f66,f22])).
% 1.53/0.58  fof(f66,plain,(
% 1.53/0.58    ( ! [X1] : (~v1_relat_1(sK1) | k1_funct_1(sK1,sK3(sK1,X1)) = X1 | ~r2_hidden(X1,k2_relat_1(sK1))) )),
% 1.53/0.58    inference(resolution,[],[f23,f59])).
% 1.53/0.58  fof(f59,plain,(
% 1.53/0.58    ( ! [X2,X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_funct_1(X0,sK3(X0,X2)) = X2 | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 1.53/0.58    inference(equality_resolution,[],[f32])).
% 1.53/0.58  fof(f32,plain,(
% 1.53/0.58    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK3(X0,X2)) = X2 | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.53/0.58    inference(cnf_transformation,[],[f17])).
% 1.53/0.58  fof(f40,plain,(
% 1.53/0.58    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f20])).
% 1.53/0.58  fof(f81,plain,(
% 1.53/0.58    k1_xboole_0 != k2_relat_1(sK1) | r1_xboole_0(k1_relat_1(sK1),k1_relat_1(sK1))),
% 1.53/0.58    inference(subsumption_resolution,[],[f80,f22])).
% 1.53/0.58  fof(f80,plain,(
% 1.53/0.58    k1_xboole_0 != k2_relat_1(sK1) | r1_xboole_0(k1_relat_1(sK1),k1_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 1.53/0.58    inference(superposition,[],[f36,f64])).
% 1.53/0.58  fof(f64,plain,(
% 1.53/0.58    k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1))),
% 1.53/0.58    inference(resolution,[],[f22,f27])).
% 1.53/0.58  fof(f27,plain,(
% 1.53/0.58    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f15])).
% 1.53/0.58  fof(f15,plain,(
% 1.53/0.58    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 1.53/0.58    inference(ennf_transformation,[],[f8])).
% 1.53/0.58  fof(f8,axiom,(
% 1.53/0.58    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 1.53/0.58  fof(f36,plain,(
% 1.53/0.58    ( ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f18])).
% 1.53/0.58  fof(f18,plain,(
% 1.53/0.58    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.53/0.58    inference(ennf_transformation,[],[f9])).
% 1.53/0.58  fof(f9,axiom,(
% 1.53/0.58    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).
% 1.53/0.58  % SZS output end Proof for theBenchmark
% 1.53/0.58  % (10046)------------------------------
% 1.53/0.58  % (10046)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.58  % (10046)Termination reason: Refutation
% 1.53/0.58  
% 1.53/0.58  % (10046)Memory used [KB]: 1791
% 1.53/0.58  % (10046)Time elapsed: 0.157 s
% 1.53/0.58  % (10046)------------------------------
% 1.53/0.58  % (10046)------------------------------
% 1.53/0.58  % (10024)Success in time 0.219 s
%------------------------------------------------------------------------------
