%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:39 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 197 expanded)
%              Number of leaves         :   10 (  45 expanded)
%              Depth                    :   17
%              Number of atoms          :  202 ( 818 expanded)
%              Number of equality atoms :   31 ( 158 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f414,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f402])).

fof(f402,plain,(
    sK0 != sK0 ),
    inference(superposition,[],[f41,f382])).

fof(f382,plain,(
    sK0 = k10_relat_1(sK1,k9_relat_1(sK1,sK0)) ),
    inference(resolution,[],[f377,f142])).

fof(f142,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    | sK0 = k10_relat_1(sK1,k9_relat_1(sK1,sK0)) ),
    inference(resolution,[],[f137,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f137,plain,(
    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(resolution,[],[f121,f54])).

fof(f54,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f121,plain,(
    ! [X4] :
      ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),X4)
      | r1_tarski(sK0,X4) ) ),
    inference(resolution,[],[f74,f39])).

fof(f39,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))
    & v2_funct_1(sK1)
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f33])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
        & v2_funct_1(X1)
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))
      & v2_funct_1(sK1)
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( v2_funct_1(X1)
            & r1_tarski(X0,k1_relat_1(X1)) )
         => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(sK1))
      | ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X1)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f59,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f59,plain,(
    ! [X4] :
      ( r1_tarski(X4,k10_relat_1(sK1,k9_relat_1(sK1,X4)))
      | ~ r1_tarski(X4,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f37,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f37,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f377,plain,(
    r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    inference(resolution,[],[f287,f54])).

fof(f287,plain,(
    ! [X0] :
      ( ~ r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK1,X0))
      | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),X0) ) ),
    inference(superposition,[],[f224,f127])).

fof(f127,plain,(
    k9_relat_1(sK1,sK0) = k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(resolution,[],[f116,f78])).

fof(f78,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_relat_1(sK1))
      | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0 ) ),
    inference(resolution,[],[f60,f37])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK1)
      | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(sK1)) ) ),
    inference(resolution,[],[f38,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f38,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f116,plain,(
    r1_tarski(k9_relat_1(sK1,sK0),k2_relat_1(sK1)) ),
    inference(resolution,[],[f115,f54])).

fof(f115,plain,(
    ! [X15] :
      ( ~ r1_tarski(X15,sK0)
      | r1_tarski(k9_relat_1(sK1,X15),k2_relat_1(sK1)) ) ),
    inference(forward_demodulation,[],[f113,f81])).

fof(f81,plain,(
    k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f79,f55])).

fof(f55,plain,(
    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) ),
    inference(resolution,[],[f37,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f79,plain,(
    k2_relat_1(sK1) = k9_relat_1(sK1,k10_relat_1(sK1,k2_relat_1(sK1))) ),
    inference(resolution,[],[f78,f54])).

fof(f113,plain,(
    ! [X15] :
      ( r1_tarski(k9_relat_1(sK1,X15),k9_relat_1(sK1,k1_relat_1(sK1)))
      | ~ r1_tarski(X15,sK0) ) ),
    inference(resolution,[],[f98,f39])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f72,f57])).

fof(f57,plain,(
    ! [X2,X1] :
      ( r1_tarski(k9_relat_1(sK1,X1),k9_relat_1(sK1,X2))
      | ~ r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f37,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k9_relat_1(sK1,X1),X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(k9_relat_1(sK1,X0),X2) ) ),
    inference(resolution,[],[f57,f49])).

fof(f224,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X2)),k9_relat_1(sK1,X3))
      | r1_tarski(k10_relat_1(sK1,X2),X3) ) ),
    inference(resolution,[],[f135,f58])).

fof(f58,plain,(
    ! [X3] : r1_tarski(k10_relat_1(sK1,X3),k1_relat_1(sK1)) ),
    inference(resolution,[],[f37,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(sK1))
      | r1_tarski(X0,X1)
      | ~ r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f87,f37])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK1)
      | ~ r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
      | r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f61,f38])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(sK1)
      | ~ r1_tarski(X0,k1_relat_1(sK1))
      | ~ r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f40,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ v2_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ v2_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).

fof(f40,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f41,plain,(
    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:10:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (16906)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.51  % (16926)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.51  % (16918)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.51  % (16905)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.51  % (16921)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.51  % (16908)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (16910)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (16904)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (16913)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.53  % (16907)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (16920)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.53  % (16927)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.53  % (16932)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.54  % (16909)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.54  % (16905)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f414,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f402])).
% 0.20/0.54  fof(f402,plain,(
% 0.20/0.54    sK0 != sK0),
% 0.20/0.54    inference(superposition,[],[f41,f382])).
% 0.20/0.54  fof(f382,plain,(
% 0.20/0.54    sK0 = k10_relat_1(sK1,k9_relat_1(sK1,sK0))),
% 0.20/0.54    inference(resolution,[],[f377,f142])).
% 0.20/0.54  fof(f142,plain,(
% 0.20/0.54    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) | sK0 = k10_relat_1(sK1,k9_relat_1(sK1,sK0))),
% 0.20/0.54    inference(resolution,[],[f137,f44])).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.20/0.54    inference(cnf_transformation,[],[f36])).
% 0.20/0.54  fof(f36,plain,(
% 0.20/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.54    inference(flattening,[],[f35])).
% 0.20/0.54  fof(f35,plain,(
% 0.20/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.54    inference(nnf_transformation,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.54  fof(f137,plain,(
% 0.20/0.54    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 0.20/0.54    inference(resolution,[],[f121,f54])).
% 0.20/0.54  fof(f54,plain,(
% 0.20/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.54    inference(equality_resolution,[],[f42])).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.20/0.54    inference(cnf_transformation,[],[f36])).
% 0.20/0.54  fof(f121,plain,(
% 0.20/0.54    ( ! [X4] : (~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),X4) | r1_tarski(sK0,X4)) )),
% 0.20/0.54    inference(resolution,[],[f74,f39])).
% 0.20/0.54  fof(f39,plain,(
% 0.20/0.54    r1_tarski(sK0,k1_relat_1(sK1))),
% 0.20/0.54    inference(cnf_transformation,[],[f34])).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f33])).
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f19,plain,(
% 0.20/0.54    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.54    inference(flattening,[],[f18])).
% 0.20/0.54  fof(f18,plain,(
% 0.20/0.54    ? [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & (v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.20/0.54    inference(ennf_transformation,[],[f17])).
% 0.20/0.54  fof(f17,negated_conjecture,(
% 0.20/0.54    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.20/0.54    inference(negated_conjecture,[],[f16])).
% 0.20/0.54  fof(f16,conjecture,(
% 0.20/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).
% 0.20/0.54  fof(f74,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(sK1)) | ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(resolution,[],[f59,f49])).
% 0.20/0.54  fof(f49,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f28])).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.54    inference(flattening,[],[f27])).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.54    inference(ennf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.54  fof(f59,plain,(
% 0.20/0.54    ( ! [X4] : (r1_tarski(X4,k10_relat_1(sK1,k9_relat_1(sK1,X4))) | ~r1_tarski(X4,k1_relat_1(sK1))) )),
% 0.20/0.54    inference(resolution,[],[f37,f45])).
% 0.20/0.54  fof(f45,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f21])).
% 0.20/0.54  fof(f21,plain,(
% 0.20/0.54    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(flattening,[],[f20])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f13])).
% 0.20/0.54  fof(f13,axiom,(
% 0.20/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 0.20/0.54  fof(f37,plain,(
% 0.20/0.54    v1_relat_1(sK1)),
% 0.20/0.54    inference(cnf_transformation,[],[f34])).
% 0.20/0.54  fof(f377,plain,(
% 0.20/0.54    r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),
% 0.20/0.54    inference(resolution,[],[f287,f54])).
% 0.20/0.54  fof(f287,plain,(
% 0.20/0.54    ( ! [X0] : (~r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK1,X0)) | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),X0)) )),
% 0.20/0.54    inference(superposition,[],[f224,f127])).
% 0.20/0.54  fof(f127,plain,(
% 0.20/0.54    k9_relat_1(sK1,sK0) = k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 0.20/0.54    inference(resolution,[],[f116,f78])).
% 0.20/0.54  fof(f78,plain,(
% 0.20/0.54    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK1)) | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0) )),
% 0.20/0.54    inference(resolution,[],[f60,f37])).
% 0.20/0.54  fof(f60,plain,(
% 0.20/0.54    ( ! [X0] : (~v1_relat_1(sK1) | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(sK1))) )),
% 0.20/0.54    inference(resolution,[],[f38,f50])).
% 0.20/0.54  fof(f50,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f30])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(flattening,[],[f29])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.54    inference(ennf_transformation,[],[f14])).
% 0.20/0.54  fof(f14,axiom,(
% 0.20/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 0.20/0.54  fof(f38,plain,(
% 0.20/0.54    v1_funct_1(sK1)),
% 0.20/0.54    inference(cnf_transformation,[],[f34])).
% 0.20/0.54  fof(f116,plain,(
% 0.20/0.54    r1_tarski(k9_relat_1(sK1,sK0),k2_relat_1(sK1))),
% 0.20/0.54    inference(resolution,[],[f115,f54])).
% 0.20/0.54  fof(f115,plain,(
% 0.20/0.54    ( ! [X15] : (~r1_tarski(X15,sK0) | r1_tarski(k9_relat_1(sK1,X15),k2_relat_1(sK1))) )),
% 0.20/0.54    inference(forward_demodulation,[],[f113,f81])).
% 0.20/0.54  fof(f81,plain,(
% 0.20/0.54    k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1))),
% 0.20/0.54    inference(forward_demodulation,[],[f79,f55])).
% 0.20/0.54  fof(f55,plain,(
% 0.20/0.54    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))),
% 0.20/0.54    inference(resolution,[],[f37,f52])).
% 0.20/0.54  fof(f52,plain,(
% 0.20/0.54    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f32])).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f11])).
% 0.20/0.54  fof(f11,axiom,(
% 0.20/0.54    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 0.20/0.54  fof(f79,plain,(
% 0.20/0.54    k2_relat_1(sK1) = k9_relat_1(sK1,k10_relat_1(sK1,k2_relat_1(sK1)))),
% 0.20/0.54    inference(resolution,[],[f78,f54])).
% 0.20/0.54  fof(f113,plain,(
% 0.20/0.54    ( ! [X15] : (r1_tarski(k9_relat_1(sK1,X15),k9_relat_1(sK1,k1_relat_1(sK1))) | ~r1_tarski(X15,sK0)) )),
% 0.20/0.54    inference(resolution,[],[f98,f39])).
% 0.20/0.54  fof(f98,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X2)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(resolution,[],[f72,f57])).
% 0.20/0.54  fof(f57,plain,(
% 0.20/0.54    ( ! [X2,X1] : (r1_tarski(k9_relat_1(sK1,X1),k9_relat_1(sK1,X2)) | ~r1_tarski(X1,X2)) )),
% 0.20/0.54    inference(resolution,[],[f37,f47])).
% 0.20/0.54  fof(f47,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f24])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.20/0.54    inference(flattening,[],[f23])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.20/0.54    inference(ennf_transformation,[],[f9])).
% 0.20/0.54  fof(f9,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).
% 0.20/0.54  fof(f72,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~r1_tarski(k9_relat_1(sK1,X1),X2) | ~r1_tarski(X0,X1) | r1_tarski(k9_relat_1(sK1,X0),X2)) )),
% 0.20/0.54    inference(resolution,[],[f57,f49])).
% 0.20/0.54  fof(f224,plain,(
% 0.20/0.54    ( ! [X2,X3] : (~r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X2)),k9_relat_1(sK1,X3)) | r1_tarski(k10_relat_1(sK1,X2),X3)) )),
% 0.20/0.54    inference(resolution,[],[f135,f58])).
% 0.20/0.54  fof(f58,plain,(
% 0.20/0.54    ( ! [X3] : (r1_tarski(k10_relat_1(sK1,X3),k1_relat_1(sK1))) )),
% 0.20/0.54    inference(resolution,[],[f37,f46])).
% 0.20/0.54  fof(f46,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f22])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f10])).
% 0.20/0.54  fof(f10,axiom,(
% 0.20/0.54    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 0.20/0.54  fof(f135,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(sK1)) | r1_tarski(X0,X1) | ~r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))) )),
% 0.20/0.54    inference(resolution,[],[f87,f37])).
% 0.20/0.54  fof(f87,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~v1_relat_1(sK1) | ~r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) | r1_tarski(X0,X1) | ~r1_tarski(X0,k1_relat_1(sK1))) )),
% 0.20/0.54    inference(resolution,[],[f61,f38])).
% 0.20/0.54  fof(f61,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~v1_funct_1(sK1) | ~r1_tarski(X0,k1_relat_1(sK1)) | ~r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) | r1_tarski(X0,X1) | ~v1_relat_1(sK1)) )),
% 0.20/0.54    inference(resolution,[],[f40,f48])).
% 0.20/0.54  fof(f48,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | r1_tarski(X0,X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f26])).
% 0.20/0.54  fof(f26,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~v2_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.54    inference(flattening,[],[f25])).
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((r1_tarski(X0,X1) | (~v2_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.54    inference(ennf_transformation,[],[f15])).
% 0.20/0.54  fof(f15,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).
% 0.20/0.54  fof(f40,plain,(
% 0.20/0.54    v2_funct_1(sK1)),
% 0.20/0.54    inference(cnf_transformation,[],[f34])).
% 0.20/0.54  fof(f41,plain,(
% 0.20/0.54    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))),
% 0.20/0.54    inference(cnf_transformation,[],[f34])).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (16905)------------------------------
% 0.20/0.54  % (16905)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (16905)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (16905)Memory used [KB]: 1791
% 0.20/0.54  % (16905)Time elapsed: 0.113 s
% 0.20/0.54  % (16905)------------------------------
% 0.20/0.54  % (16905)------------------------------
% 0.20/0.54  % (16922)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.54  % (16931)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.54  % (16903)Success in time 0.185 s
%------------------------------------------------------------------------------
