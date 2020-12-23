%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:47 EST 2020

% Result     : Theorem 1.97s
% Output     : Refutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 147 expanded)
%              Number of leaves         :    8 (  32 expanded)
%              Depth                    :   14
%              Number of atoms          :  180 ( 393 expanded)
%              Number of equality atoms :   26 (  72 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1741,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1737,f93])).

fof(f93,plain,(
    ~ r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1))) ),
    inference(subsumption_resolution,[],[f92,f19])).

fof(f19,plain,(
    k1_relat_1(k5_relat_1(sK0,sK1)) != k10_relat_1(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) != k10_relat_1(X0,k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f92,plain,
    ( ~ r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1)))
    | k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1)) ),
    inference(resolution,[],[f90,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f90,plain,(
    r1_tarski(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(superposition,[],[f87,f44])).

fof(f44,plain,(
    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) ),
    inference(resolution,[],[f21,f18])).

fof(f18,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f87,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK0,k10_relat_1(sK1,X0)),k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f86,f20])).

fof(f20,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f86,plain,(
    ! [X0] :
      ( r1_tarski(k10_relat_1(sK0,k10_relat_1(sK1,X0)),k1_relat_1(k5_relat_1(sK0,sK1)))
      | ~ v1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f85,f18])).

fof(f85,plain,(
    ! [X0] :
      ( r1_tarski(k10_relat_1(sK0,k10_relat_1(sK1,X0)),k1_relat_1(k5_relat_1(sK0,sK1)))
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f69,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f69,plain,(
    ! [X1] :
      ( ~ v1_relat_1(k5_relat_1(sK0,sK1))
      | r1_tarski(k10_relat_1(sK0,k10_relat_1(sK1,X1)),k1_relat_1(k5_relat_1(sK0,sK1))) ) ),
    inference(superposition,[],[f28,f64])).

fof(f64,plain,(
    ! [X1] : k10_relat_1(k5_relat_1(sK0,sK1),X1) = k10_relat_1(sK0,k10_relat_1(sK1,X1)) ),
    inference(resolution,[],[f60,f20])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(k5_relat_1(X0,sK1),X1) = k10_relat_1(X0,k10_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f29,f18])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f1737,plain,(
    r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1))) ),
    inference(resolution,[],[f1728,f413])).

fof(f413,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ),
    inference(duplicate_literal_removal,[],[f410])).

fof(f410,plain,(
    ! [X0] :
      ( r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))
      | r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f408,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f408,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(k10_relat_1(sK1,X0),X1),k1_relat_1(sK1))
      | r1_tarski(k10_relat_1(sK1,X0),X1) ) ),
    inference(resolution,[],[f405,f40])).

fof(f40,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f405,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(sK1,X2))
      | r2_hidden(sK5(X0,X1),k1_relat_1(sK1))
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f59,f18])).

fof(f59,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ v1_relat_1(X5)
      | r2_hidden(sK5(X3,X4),k1_relat_1(X5))
      | ~ r1_tarski(X3,k10_relat_1(X5,X6))
      | r1_tarski(X3,X4) ) ),
    inference(resolution,[],[f53,f28])).

fof(f53,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ r1_tarski(X3,X5)
      | r1_tarski(X2,X4)
      | r2_hidden(sK5(X2,X4),X5)
      | ~ r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f51,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1),X2)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f34,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1728,plain,(
    ! [X1] :
      ( ~ r1_tarski(k10_relat_1(sK1,k2_relat_1(k5_relat_1(sK0,sK1))),X1)
      | r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,X1)) ) ),
    inference(superposition,[],[f1704,f613])).

fof(f613,plain,(
    k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k10_relat_1(sK1,k2_relat_1(k5_relat_1(sK0,sK1)))) ),
    inference(superposition,[],[f610,f64])).

fof(f610,plain,(
    k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(k5_relat_1(sK0,sK1),k2_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(resolution,[],[f470,f18])).

fof(f470,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(sK0,X1)) = k10_relat_1(k5_relat_1(sK0,X1),k2_relat_1(k5_relat_1(sK0,X1))) ) ),
    inference(resolution,[],[f46,f20])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(k5_relat_1(X0,X1),k2_relat_1(k5_relat_1(X0,X1))) ) ),
    inference(resolution,[],[f21,f30])).

fof(f1704,plain,(
    ! [X10,X9] :
      ( r1_tarski(k10_relat_1(sK0,X9),k10_relat_1(sK0,X10))
      | ~ r1_tarski(X9,X10) ) ),
    inference(duplicate_literal_removal,[],[f1696])).

fof(f1696,plain,(
    ! [X10,X9] :
      ( ~ r1_tarski(X9,X10)
      | r1_tarski(k10_relat_1(sK0,X9),k10_relat_1(sK0,X10))
      | r1_tarski(k10_relat_1(sK0,X9),k10_relat_1(sK0,X10)) ) ),
    inference(resolution,[],[f999,f36])).

fof(f999,plain,(
    ! [X26,X27,X25] :
      ( r2_hidden(sK5(k10_relat_1(sK0,X25),X26),k10_relat_1(sK0,X27))
      | ~ r1_tarski(X25,X27)
      | r1_tarski(k10_relat_1(sK0,X25),X26) ) ),
    inference(resolution,[],[f978,f35])).

fof(f978,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,k10_relat_1(sK0,X4))
      | r2_hidden(X3,k10_relat_1(sK0,X5))
      | ~ r1_tarski(X4,X5) ) ),
    inference(resolution,[],[f744,f20])).

fof(f744,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ v1_relat_1(X4)
      | ~ r2_hidden(X3,k10_relat_1(X4,X5))
      | r2_hidden(X3,k10_relat_1(X4,X6))
      | ~ r1_tarski(X5,X6) ) ),
    inference(duplicate_literal_removal,[],[f743])).

fof(f743,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ r2_hidden(X3,k10_relat_1(X4,X5))
      | ~ v1_relat_1(X4)
      | r2_hidden(X3,k10_relat_1(X4,X6))
      | ~ r2_hidden(X3,k10_relat_1(X4,X5))
      | ~ v1_relat_1(X4)
      | ~ r1_tarski(X5,X6) ) ),
    inference(resolution,[],[f104,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK3(X0,X2,X1),X3)
      | ~ r2_hidden(X1,k10_relat_1(X0,X2))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f38,f34])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK3(X0,X1,X3),X1)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK3(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

fof(f104,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_hidden(sK3(X4,X6,X5),X7)
      | ~ r2_hidden(X5,k10_relat_1(X4,X6))
      | ~ v1_relat_1(X4)
      | r2_hidden(X5,k10_relat_1(X4,X7)) ) ),
    inference(duplicate_literal_removal,[],[f103])).

fof(f103,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ v1_relat_1(X4)
      | ~ r2_hidden(X5,k10_relat_1(X4,X6))
      | ~ v1_relat_1(X4)
      | ~ r2_hidden(sK3(X4,X6,X5),X7)
      | r2_hidden(X5,k10_relat_1(X4,X7)) ) ),
    inference(resolution,[],[f39,f37])).

fof(f37,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k4_tarski(X3,sK3(X0,X1,X3)),X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,sK3(X0,X1,X3)),X0)
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:28:47 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (23924)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (23932)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.51  % (23940)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.51  % (23923)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.51  % (23940)Refutation not found, incomplete strategy% (23940)------------------------------
% 0.22/0.51  % (23940)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (23921)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.51  % (23940)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (23940)Memory used [KB]: 10746
% 0.22/0.51  % (23940)Time elapsed: 0.109 s
% 0.22/0.51  % (23940)------------------------------
% 0.22/0.51  % (23940)------------------------------
% 0.22/0.52  % (23926)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.52  % (23933)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (23938)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.27/0.52  % (23928)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.27/0.52  % (23920)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.27/0.52  % (23941)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.27/0.53  % (23930)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.27/0.53  % (23939)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.27/0.53  % (23922)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.27/0.53  % (23936)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.27/0.53  % (23925)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.27/0.53  % (23919)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.27/0.53  % (23931)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.27/0.53  % (23934)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.27/0.53  % (23929)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.27/0.53  % (23918)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.27/0.54  % (23945)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.36/0.54  % (23946)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.36/0.54  % (23944)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.36/0.54  % (23937)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.36/0.54  % (23947)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.36/0.54  % (23927)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.36/0.55  % (23935)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.36/0.55  % (23935)Refutation not found, incomplete strategy% (23935)------------------------------
% 1.36/0.55  % (23935)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (23935)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  % (23935)Memory used [KB]: 10618
% 1.36/0.55  % (23935)Time elapsed: 0.141 s
% 1.36/0.55  % (23935)------------------------------
% 1.36/0.55  % (23935)------------------------------
% 1.36/0.55  % (23942)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.36/0.55  % (23943)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.97/0.63  % (23951)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.97/0.64  % (23924)Refutation found. Thanks to Tanya!
% 1.97/0.64  % SZS status Theorem for theBenchmark
% 1.97/0.64  % SZS output start Proof for theBenchmark
% 1.97/0.64  fof(f1741,plain,(
% 1.97/0.64    $false),
% 1.97/0.64    inference(subsumption_resolution,[],[f1737,f93])).
% 1.97/0.64  fof(f93,plain,(
% 1.97/0.64    ~r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1)))),
% 1.97/0.64    inference(subsumption_resolution,[],[f92,f19])).
% 1.97/0.64  fof(f19,plain,(
% 1.97/0.64    k1_relat_1(k5_relat_1(sK0,sK1)) != k10_relat_1(sK0,k1_relat_1(sK1))),
% 1.97/0.64    inference(cnf_transformation,[],[f10])).
% 1.97/0.64  fof(f10,plain,(
% 1.97/0.64    ? [X0] : (? [X1] : (k1_relat_1(k5_relat_1(X0,X1)) != k10_relat_1(X0,k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.97/0.64    inference(ennf_transformation,[],[f9])).
% 1.97/0.64  fof(f9,negated_conjecture,(
% 1.97/0.64    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 1.97/0.64    inference(negated_conjecture,[],[f8])).
% 1.97/0.64  fof(f8,conjecture,(
% 1.97/0.64    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 1.97/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 1.97/0.64  fof(f92,plain,(
% 1.97/0.64    ~r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1))) | k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1))),
% 1.97/0.64    inference(resolution,[],[f90,f33])).
% 1.97/0.64  fof(f33,plain,(
% 1.97/0.64    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.97/0.64    inference(cnf_transformation,[],[f2])).
% 1.97/0.64  fof(f2,axiom,(
% 1.97/0.64    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.97/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.97/0.64  fof(f90,plain,(
% 1.97/0.64    r1_tarski(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(sK0,sK1)))),
% 1.97/0.64    inference(superposition,[],[f87,f44])).
% 1.97/0.64  fof(f44,plain,(
% 1.97/0.64    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))),
% 1.97/0.64    inference(resolution,[],[f21,f18])).
% 1.97/0.64  fof(f18,plain,(
% 1.97/0.64    v1_relat_1(sK1)),
% 1.97/0.64    inference(cnf_transformation,[],[f10])).
% 1.97/0.64  fof(f21,plain,(
% 1.97/0.64    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 1.97/0.64    inference(cnf_transformation,[],[f11])).
% 1.97/0.64  fof(f11,plain,(
% 1.97/0.64    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.97/0.64    inference(ennf_transformation,[],[f6])).
% 1.97/0.64  fof(f6,axiom,(
% 1.97/0.64    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.97/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 1.97/0.64  fof(f87,plain,(
% 1.97/0.64    ( ! [X0] : (r1_tarski(k10_relat_1(sK0,k10_relat_1(sK1,X0)),k1_relat_1(k5_relat_1(sK0,sK1)))) )),
% 1.97/0.64    inference(subsumption_resolution,[],[f86,f20])).
% 1.97/0.64  fof(f20,plain,(
% 1.97/0.64    v1_relat_1(sK0)),
% 1.97/0.64    inference(cnf_transformation,[],[f10])).
% 1.97/0.64  fof(f86,plain,(
% 1.97/0.64    ( ! [X0] : (r1_tarski(k10_relat_1(sK0,k10_relat_1(sK1,X0)),k1_relat_1(k5_relat_1(sK0,sK1))) | ~v1_relat_1(sK0)) )),
% 1.97/0.64    inference(subsumption_resolution,[],[f85,f18])).
% 1.97/0.64  fof(f85,plain,(
% 1.97/0.64    ( ! [X0] : (r1_tarski(k10_relat_1(sK0,k10_relat_1(sK1,X0)),k1_relat_1(k5_relat_1(sK0,sK1))) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)) )),
% 1.97/0.64    inference(resolution,[],[f69,f30])).
% 1.97/0.64  fof(f30,plain,(
% 1.97/0.64    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.97/0.64    inference(cnf_transformation,[],[f16])).
% 1.97/0.64  fof(f16,plain,(
% 1.97/0.64    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.97/0.64    inference(flattening,[],[f15])).
% 1.97/0.64  fof(f15,plain,(
% 1.97/0.64    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.97/0.64    inference(ennf_transformation,[],[f4])).
% 1.97/0.64  fof(f4,axiom,(
% 1.97/0.64    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.97/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.97/0.64  fof(f69,plain,(
% 1.97/0.64    ( ! [X1] : (~v1_relat_1(k5_relat_1(sK0,sK1)) | r1_tarski(k10_relat_1(sK0,k10_relat_1(sK1,X1)),k1_relat_1(k5_relat_1(sK0,sK1)))) )),
% 1.97/0.64    inference(superposition,[],[f28,f64])).
% 1.97/0.64  fof(f64,plain,(
% 1.97/0.64    ( ! [X1] : (k10_relat_1(k5_relat_1(sK0,sK1),X1) = k10_relat_1(sK0,k10_relat_1(sK1,X1))) )),
% 1.97/0.64    inference(resolution,[],[f60,f20])).
% 1.97/0.64  fof(f60,plain,(
% 1.97/0.64    ( ! [X0,X1] : (~v1_relat_1(X0) | k10_relat_1(k5_relat_1(X0,sK1),X1) = k10_relat_1(X0,k10_relat_1(sK1,X1))) )),
% 1.97/0.64    inference(resolution,[],[f29,f18])).
% 1.97/0.64  fof(f29,plain,(
% 1.97/0.64    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_relat_1(X1) | k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))) )),
% 1.97/0.64    inference(cnf_transformation,[],[f14])).
% 1.97/0.64  fof(f14,plain,(
% 1.97/0.64    ! [X0,X1] : (! [X2] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.97/0.64    inference(ennf_transformation,[],[f7])).
% 1.97/0.64  fof(f7,axiom,(
% 1.97/0.64    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))))),
% 1.97/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).
% 1.97/0.64  fof(f28,plain,(
% 1.97/0.64    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.97/0.64    inference(cnf_transformation,[],[f13])).
% 1.97/0.64  fof(f13,plain,(
% 1.97/0.64    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.97/0.64    inference(ennf_transformation,[],[f5])).
% 1.97/0.64  fof(f5,axiom,(
% 1.97/0.64    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 1.97/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 1.97/0.64  fof(f1737,plain,(
% 1.97/0.64    r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1)))),
% 1.97/0.64    inference(resolution,[],[f1728,f413])).
% 1.97/0.64  fof(f413,plain,(
% 1.97/0.64    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))) )),
% 1.97/0.64    inference(duplicate_literal_removal,[],[f410])).
% 1.97/0.64  fof(f410,plain,(
% 1.97/0.64    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1)) | r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))) )),
% 1.97/0.64    inference(resolution,[],[f408,f36])).
% 1.97/0.64  fof(f36,plain,(
% 1.97/0.64    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.97/0.64    inference(cnf_transformation,[],[f17])).
% 1.97/0.64  fof(f17,plain,(
% 1.97/0.64    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.97/0.64    inference(ennf_transformation,[],[f1])).
% 1.97/0.64  fof(f1,axiom,(
% 1.97/0.64    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.97/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.97/0.64  fof(f408,plain,(
% 1.97/0.64    ( ! [X0,X1] : (r2_hidden(sK5(k10_relat_1(sK1,X0),X1),k1_relat_1(sK1)) | r1_tarski(k10_relat_1(sK1,X0),X1)) )),
% 1.97/0.64    inference(resolution,[],[f405,f40])).
% 1.97/0.64  fof(f40,plain,(
% 1.97/0.64    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.97/0.64    inference(equality_resolution,[],[f32])).
% 1.97/0.64  fof(f32,plain,(
% 1.97/0.64    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.97/0.64    inference(cnf_transformation,[],[f2])).
% 1.97/0.64  fof(f405,plain,(
% 1.97/0.64    ( ! [X2,X0,X1] : (~r1_tarski(X0,k10_relat_1(sK1,X2)) | r2_hidden(sK5(X0,X1),k1_relat_1(sK1)) | r1_tarski(X0,X1)) )),
% 1.97/0.64    inference(resolution,[],[f59,f18])).
% 1.97/0.64  fof(f59,plain,(
% 1.97/0.64    ( ! [X6,X4,X5,X3] : (~v1_relat_1(X5) | r2_hidden(sK5(X3,X4),k1_relat_1(X5)) | ~r1_tarski(X3,k10_relat_1(X5,X6)) | r1_tarski(X3,X4)) )),
% 1.97/0.64    inference(resolution,[],[f53,f28])).
% 1.97/0.64  fof(f53,plain,(
% 1.97/0.64    ( ! [X4,X2,X5,X3] : (~r1_tarski(X3,X5) | r1_tarski(X2,X4) | r2_hidden(sK5(X2,X4),X5) | ~r1_tarski(X2,X3)) )),
% 1.97/0.64    inference(resolution,[],[f51,f34])).
% 1.97/0.65  fof(f34,plain,(
% 1.97/0.65    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.97/0.65    inference(cnf_transformation,[],[f17])).
% 1.97/0.65  fof(f51,plain,(
% 1.97/0.65    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1),X2) | ~r1_tarski(X0,X2) | r1_tarski(X0,X1)) )),
% 1.97/0.65    inference(resolution,[],[f34,f35])).
% 1.97/0.65  fof(f35,plain,(
% 1.97/0.65    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.97/0.65    inference(cnf_transformation,[],[f17])).
% 1.97/0.65  fof(f1728,plain,(
% 1.97/0.65    ( ! [X1] : (~r1_tarski(k10_relat_1(sK1,k2_relat_1(k5_relat_1(sK0,sK1))),X1) | r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,X1))) )),
% 1.97/0.65    inference(superposition,[],[f1704,f613])).
% 1.97/0.65  fof(f613,plain,(
% 1.97/0.65    k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k10_relat_1(sK1,k2_relat_1(k5_relat_1(sK0,sK1))))),
% 1.97/0.65    inference(superposition,[],[f610,f64])).
% 1.97/0.65  fof(f610,plain,(
% 1.97/0.65    k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(k5_relat_1(sK0,sK1),k2_relat_1(k5_relat_1(sK0,sK1)))),
% 1.97/0.65    inference(resolution,[],[f470,f18])).
% 1.97/0.65  fof(f470,plain,(
% 1.97/0.65    ( ! [X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(sK0,X1)) = k10_relat_1(k5_relat_1(sK0,X1),k2_relat_1(k5_relat_1(sK0,X1)))) )),
% 1.97/0.65    inference(resolution,[],[f46,f20])).
% 1.97/0.65  fof(f46,plain,(
% 1.97/0.65    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(k5_relat_1(X0,X1),k2_relat_1(k5_relat_1(X0,X1)))) )),
% 1.97/0.65    inference(resolution,[],[f21,f30])).
% 1.97/0.65  fof(f1704,plain,(
% 1.97/0.65    ( ! [X10,X9] : (r1_tarski(k10_relat_1(sK0,X9),k10_relat_1(sK0,X10)) | ~r1_tarski(X9,X10)) )),
% 1.97/0.65    inference(duplicate_literal_removal,[],[f1696])).
% 1.97/0.65  fof(f1696,plain,(
% 1.97/0.65    ( ! [X10,X9] : (~r1_tarski(X9,X10) | r1_tarski(k10_relat_1(sK0,X9),k10_relat_1(sK0,X10)) | r1_tarski(k10_relat_1(sK0,X9),k10_relat_1(sK0,X10))) )),
% 1.97/0.65    inference(resolution,[],[f999,f36])).
% 1.97/0.65  fof(f999,plain,(
% 1.97/0.65    ( ! [X26,X27,X25] : (r2_hidden(sK5(k10_relat_1(sK0,X25),X26),k10_relat_1(sK0,X27)) | ~r1_tarski(X25,X27) | r1_tarski(k10_relat_1(sK0,X25),X26)) )),
% 1.97/0.65    inference(resolution,[],[f978,f35])).
% 1.97/0.65  fof(f978,plain,(
% 1.97/0.65    ( ! [X4,X5,X3] : (~r2_hidden(X3,k10_relat_1(sK0,X4)) | r2_hidden(X3,k10_relat_1(sK0,X5)) | ~r1_tarski(X4,X5)) )),
% 1.97/0.65    inference(resolution,[],[f744,f20])).
% 1.97/0.65  fof(f744,plain,(
% 1.97/0.65    ( ! [X6,X4,X5,X3] : (~v1_relat_1(X4) | ~r2_hidden(X3,k10_relat_1(X4,X5)) | r2_hidden(X3,k10_relat_1(X4,X6)) | ~r1_tarski(X5,X6)) )),
% 1.97/0.65    inference(duplicate_literal_removal,[],[f743])).
% 1.97/0.65  fof(f743,plain,(
% 1.97/0.65    ( ! [X6,X4,X5,X3] : (~r2_hidden(X3,k10_relat_1(X4,X5)) | ~v1_relat_1(X4) | r2_hidden(X3,k10_relat_1(X4,X6)) | ~r2_hidden(X3,k10_relat_1(X4,X5)) | ~v1_relat_1(X4) | ~r1_tarski(X5,X6)) )),
% 1.97/0.65    inference(resolution,[],[f104,f55])).
% 1.97/0.65  fof(f55,plain,(
% 1.97/0.65    ( ! [X2,X0,X3,X1] : (r2_hidden(sK3(X0,X2,X1),X3) | ~r2_hidden(X1,k10_relat_1(X0,X2)) | ~v1_relat_1(X0) | ~r1_tarski(X2,X3)) )),
% 1.97/0.65    inference(resolution,[],[f38,f34])).
% 1.97/0.65  fof(f38,plain,(
% 1.97/0.65    ( ! [X0,X3,X1] : (r2_hidden(sK3(X0,X1,X3),X1) | ~v1_relat_1(X0) | ~r2_hidden(X3,k10_relat_1(X0,X1))) )),
% 1.97/0.65    inference(equality_resolution,[],[f26])).
% 1.97/0.65  fof(f26,plain,(
% 1.97/0.65    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | r2_hidden(sK3(X0,X1,X3),X1) | ~r2_hidden(X3,X2) | k10_relat_1(X0,X1) != X2) )),
% 1.97/0.65    inference(cnf_transformation,[],[f12])).
% 1.97/0.65  fof(f12,plain,(
% 1.97/0.65    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 1.97/0.65    inference(ennf_transformation,[],[f3])).
% 1.97/0.65  fof(f3,axiom,(
% 1.97/0.65    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 1.97/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).
% 1.97/0.65  fof(f104,plain,(
% 1.97/0.65    ( ! [X6,X4,X7,X5] : (~r2_hidden(sK3(X4,X6,X5),X7) | ~r2_hidden(X5,k10_relat_1(X4,X6)) | ~v1_relat_1(X4) | r2_hidden(X5,k10_relat_1(X4,X7))) )),
% 1.97/0.65    inference(duplicate_literal_removal,[],[f103])).
% 1.97/0.65  fof(f103,plain,(
% 1.97/0.65    ( ! [X6,X4,X7,X5] : (~v1_relat_1(X4) | ~r2_hidden(X5,k10_relat_1(X4,X6)) | ~v1_relat_1(X4) | ~r2_hidden(sK3(X4,X6,X5),X7) | r2_hidden(X5,k10_relat_1(X4,X7))) )),
% 1.97/0.65    inference(resolution,[],[f39,f37])).
% 1.97/0.65  fof(f37,plain,(
% 1.97/0.65    ( ! [X4,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X4),X0) | ~v1_relat_1(X0) | ~r2_hidden(X4,X1) | r2_hidden(X3,k10_relat_1(X0,X1))) )),
% 1.97/0.65    inference(equality_resolution,[],[f27])).
% 1.97/0.65  fof(f27,plain,(
% 1.97/0.65    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X4,X1) | r2_hidden(X3,X2) | k10_relat_1(X0,X1) != X2) )),
% 1.97/0.65    inference(cnf_transformation,[],[f12])).
% 1.97/0.65  fof(f39,plain,(
% 1.97/0.65    ( ! [X0,X3,X1] : (r2_hidden(k4_tarski(X3,sK3(X0,X1,X3)),X0) | ~v1_relat_1(X0) | ~r2_hidden(X3,k10_relat_1(X0,X1))) )),
% 1.97/0.65    inference(equality_resolution,[],[f25])).
% 1.97/0.65  fof(f25,plain,(
% 1.97/0.65    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(X3,sK3(X0,X1,X3)),X0) | ~r2_hidden(X3,X2) | k10_relat_1(X0,X1) != X2) )),
% 1.97/0.65    inference(cnf_transformation,[],[f12])).
% 1.97/0.65  % SZS output end Proof for theBenchmark
% 1.97/0.65  % (23924)------------------------------
% 1.97/0.65  % (23924)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.97/0.65  % (23924)Termination reason: Refutation
% 1.97/0.65  
% 1.97/0.65  % (23924)Memory used [KB]: 8571
% 1.97/0.65  % (23924)Time elapsed: 0.215 s
% 1.97/0.65  % (23924)------------------------------
% 1.97/0.65  % (23924)------------------------------
% 1.97/0.65  % (23917)Success in time 0.288 s
%------------------------------------------------------------------------------
