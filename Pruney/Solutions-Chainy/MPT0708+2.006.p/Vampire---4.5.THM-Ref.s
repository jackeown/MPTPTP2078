%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 110 expanded)
%              Number of leaves         :    4 (  20 expanded)
%              Depth                    :   19
%              Number of atoms          :  150 ( 422 expanded)
%              Number of equality atoms :    6 (  12 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f92,plain,(
    $false ),
    inference(subsumption_resolution,[],[f91,f15])).

fof(f15,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k10_relat_1(X2,X1))
      & r1_tarski(k9_relat_1(X2,X0),X1)
      & r1_tarski(X0,k1_relat_1(X2))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k10_relat_1(X2,X1))
      & r1_tarski(k9_relat_1(X2,X0),X1)
      & r1_tarski(X0,k1_relat_1(X2))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
            & r1_tarski(X0,k1_relat_1(X2)) )
         => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

fof(f91,plain,(
    ~ r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f88,f42])).

fof(f42,plain,(
    r2_hidden(sK4(sK0,k10_relat_1(sK2,sK1)),sK0) ),
    inference(resolution,[],[f17,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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

fof(f17,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f88,plain,
    ( ~ r2_hidden(sK4(sK0,k10_relat_1(sK2,sK1)),sK0)
    | ~ r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(resolution,[],[f87,f31])).

fof(f31,plain,(
    ! [X0] :
      ( r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0)))
      | ~ r1_tarski(X0,k1_relat_1(sK2)) ) ),
    inference(resolution,[],[f13,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f13,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f87,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))
      | ~ r2_hidden(sK4(sK0,k10_relat_1(sK2,sK1)),X0) ) ),
    inference(duplicate_literal_removal,[],[f86])).

fof(f86,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))
      | ~ r2_hidden(sK4(sK0,k10_relat_1(sK2,sK1)),X0)
      | ~ r2_hidden(sK4(sK0,k10_relat_1(sK2,sK1)),X0) ) ),
    inference(condensation,[],[f85])).

fof(f85,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X2,k10_relat_1(sK2,X3))
      | ~ r2_hidden(sK4(sK0,k10_relat_1(sK2,sK1)),X2)
      | ~ r2_hidden(sK4(sK0,k10_relat_1(sK2,sK1)),X4)
      | ~ r1_tarski(X4,k10_relat_1(sK2,k9_relat_1(sK2,sK0))) ) ),
    inference(resolution,[],[f82,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(sK0,k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k9_relat_1(sK2,sK0)))
      | ~ r1_tarski(X0,k10_relat_1(sK2,X1))
      | ~ r2_hidden(sK4(sK0,k10_relat_1(sK2,sK1)),X0) ) ),
    inference(resolution,[],[f81,f40])).

fof(f40,plain,(
    ! [X6,X7] :
      ( r2_hidden(k1_funct_1(sK2,X6),X7)
      | ~ r2_hidden(X6,k10_relat_1(sK2,X7)) ) ),
    inference(subsumption_resolution,[],[f35,f13])).

fof(f35,plain,(
    ! [X6,X7] :
      ( ~ v1_relat_1(sK2)
      | r2_hidden(k1_funct_1(sK2,X6),X7)
      | ~ r2_hidden(X6,k10_relat_1(sK2,X7)) ) ),
    inference(resolution,[],[f14,f29])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(k1_funct_1(X0,X3),X1)
      | ~ r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(k1_funct_1(X0,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).

fof(f14,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f81,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(k1_funct_1(sK2,sK4(sK0,k10_relat_1(sK2,sK1))),k9_relat_1(sK2,sK0))
      | ~ r2_hidden(sK4(sK0,k10_relat_1(sK2,sK1)),X3)
      | ~ r1_tarski(X3,k10_relat_1(sK2,X4)) ) ),
    inference(resolution,[],[f65,f16])).

fof(f16,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f65,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X2,sK1)
      | ~ r2_hidden(k1_funct_1(sK2,sK4(sK0,k10_relat_1(sK2,sK1))),X2)
      | ~ r2_hidden(sK4(sK0,k10_relat_1(sK2,sK1)),X3)
      | ~ r1_tarski(X3,k10_relat_1(sK2,X4)) ) ),
    inference(resolution,[],[f55,f25])).

fof(f55,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(sK4(sK0,k10_relat_1(sK2,sK1)),k10_relat_1(sK2,X1))
      | ~ r2_hidden(k1_funct_1(sK2,sK4(sK0,k10_relat_1(sK2,sK1))),X2)
      | ~ r1_tarski(X2,sK1) ) ),
    inference(resolution,[],[f52,f25])).

fof(f52,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_funct_1(sK2,sK4(sK0,k10_relat_1(sK2,sK1))),sK1)
      | ~ r2_hidden(sK4(sK0,k10_relat_1(sK2,sK1)),k10_relat_1(sK2,X0)) ) ),
    inference(resolution,[],[f51,f39])).

fof(f39,plain,(
    ! [X4,X5] :
      ( r2_hidden(X4,k1_relat_1(sK2))
      | ~ r2_hidden(X4,k10_relat_1(sK2,X5)) ) ),
    inference(subsumption_resolution,[],[f34,f13])).

fof(f34,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(sK2)
      | r2_hidden(X4,k1_relat_1(sK2))
      | ~ r2_hidden(X4,k10_relat_1(sK2,X5)) ) ),
    inference(resolution,[],[f14,f30])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f51,plain,
    ( ~ r2_hidden(sK4(sK0,k10_relat_1(sK2,sK1)),k1_relat_1(sK2))
    | ~ r2_hidden(k1_funct_1(sK2,sK4(sK0,k10_relat_1(sK2,sK1))),sK1) ),
    inference(resolution,[],[f44,f17])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(sK2,X1))
      | ~ r2_hidden(sK4(X0,k10_relat_1(sK2,X1)),k1_relat_1(sK2))
      | ~ r2_hidden(k1_funct_1(sK2,sK4(X0,k10_relat_1(sK2,X1))),X1) ) ),
    inference(resolution,[],[f41,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f41,plain,(
    ! [X8,X9] :
      ( r2_hidden(X8,k10_relat_1(sK2,X9))
      | ~ r2_hidden(k1_funct_1(sK2,X8),X9)
      | ~ r2_hidden(X8,k1_relat_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f36,f13])).

fof(f36,plain,(
    ! [X8,X9] :
      ( ~ v1_relat_1(sK2)
      | ~ r2_hidden(X8,k1_relat_1(sK2))
      | ~ r2_hidden(k1_funct_1(sK2,X8),X9)
      | r2_hidden(X8,k10_relat_1(sK2,X9)) ) ),
    inference(resolution,[],[f14,f28])).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(k1_funct_1(X0,X3),X1)
      | r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(k1_funct_1(X0,X3),X1)
      | r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:12:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (28891)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.49  % (28882)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (28873)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (28891)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f91,f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    r1_tarski(sK0,k1_relat_1(sK2))),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (~r1_tarski(X0,k10_relat_1(X2,X1)) & r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.51    inference(flattening,[],[f6])).
% 0.21/0.51  fof(f6,plain,(
% 0.21/0.51    ? [X0,X1,X2] : ((~r1_tarski(X0,k10_relat_1(X2,X1)) & (r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 0.21/0.51    inference(negated_conjecture,[],[f4])).
% 0.21/0.51  fof(f4,conjecture,(
% 0.21/0.51    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    ~r1_tarski(sK0,k1_relat_1(sK2))),
% 0.21/0.51    inference(subsumption_resolution,[],[f88,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    r2_hidden(sK4(sK0,k10_relat_1(sK2,sK1)),sK0)),
% 0.21/0.51    inference(resolution,[],[f17,f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ~r1_tarski(sK0,k10_relat_1(sK2,sK1))),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    ~r2_hidden(sK4(sK0,k10_relat_1(sK2,sK1)),sK0) | ~r1_tarski(sK0,k1_relat_1(sK2))),
% 0.21/0.51    inference(resolution,[],[f87,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0))) | ~r1_tarski(X0,k1_relat_1(sK2))) )),
% 0.21/0.51    inference(resolution,[],[f13,f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    v1_relat_1(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,sK0))) | ~r2_hidden(sK4(sK0,k10_relat_1(sK2,sK1)),X0)) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f86])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,sK0))) | ~r2_hidden(sK4(sK0,k10_relat_1(sK2,sK1)),X0) | ~r2_hidden(sK4(sK0,k10_relat_1(sK2,sK1)),X0)) )),
% 0.21/0.51    inference(condensation,[],[f85])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    ( ! [X4,X2,X3] : (~r1_tarski(X2,k10_relat_1(sK2,X3)) | ~r2_hidden(sK4(sK0,k10_relat_1(sK2,sK1)),X2) | ~r2_hidden(sK4(sK0,k10_relat_1(sK2,sK1)),X4) | ~r1_tarski(X4,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))) )),
% 0.21/0.51    inference(resolution,[],[f82,f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(sK4(sK0,k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k9_relat_1(sK2,sK0))) | ~r1_tarski(X0,k10_relat_1(sK2,X1)) | ~r2_hidden(sK4(sK0,k10_relat_1(sK2,sK1)),X0)) )),
% 0.21/0.51    inference(resolution,[],[f81,f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X6,X7] : (r2_hidden(k1_funct_1(sK2,X6),X7) | ~r2_hidden(X6,k10_relat_1(sK2,X7))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f35,f13])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X6,X7] : (~v1_relat_1(sK2) | r2_hidden(k1_funct_1(sK2,X6),X7) | ~r2_hidden(X6,k10_relat_1(sK2,X7))) )),
% 0.21/0.51    inference(resolution,[],[f14,f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k10_relat_1(X0,X1))) )),
% 0.21/0.51    inference(equality_resolution,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,X2) | k10_relat_1(X0,X1) != X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f8])).
% 0.21/0.51  fof(f8,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    v1_funct_1(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    ( ! [X4,X3] : (~r2_hidden(k1_funct_1(sK2,sK4(sK0,k10_relat_1(sK2,sK1))),k9_relat_1(sK2,sK0)) | ~r2_hidden(sK4(sK0,k10_relat_1(sK2,sK1)),X3) | ~r1_tarski(X3,k10_relat_1(sK2,X4))) )),
% 0.21/0.51    inference(resolution,[],[f65,f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    r1_tarski(k9_relat_1(sK2,sK0),sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    ( ! [X4,X2,X3] : (~r1_tarski(X2,sK1) | ~r2_hidden(k1_funct_1(sK2,sK4(sK0,k10_relat_1(sK2,sK1))),X2) | ~r2_hidden(sK4(sK0,k10_relat_1(sK2,sK1)),X3) | ~r1_tarski(X3,k10_relat_1(sK2,X4))) )),
% 0.21/0.51    inference(resolution,[],[f55,f25])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X2,X1] : (~r2_hidden(sK4(sK0,k10_relat_1(sK2,sK1)),k10_relat_1(sK2,X1)) | ~r2_hidden(k1_funct_1(sK2,sK4(sK0,k10_relat_1(sK2,sK1))),X2) | ~r1_tarski(X2,sK1)) )),
% 0.21/0.51    inference(resolution,[],[f52,f25])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(k1_funct_1(sK2,sK4(sK0,k10_relat_1(sK2,sK1))),sK1) | ~r2_hidden(sK4(sK0,k10_relat_1(sK2,sK1)),k10_relat_1(sK2,X0))) )),
% 0.21/0.51    inference(resolution,[],[f51,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X4,X5] : (r2_hidden(X4,k1_relat_1(sK2)) | ~r2_hidden(X4,k10_relat_1(sK2,X5))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f34,f13])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X4,X5] : (~v1_relat_1(sK2) | r2_hidden(X4,k1_relat_1(sK2)) | ~r2_hidden(X4,k10_relat_1(sK2,X5))) )),
% 0.21/0.51    inference(resolution,[],[f14,f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,k10_relat_1(X0,X1))) )),
% 0.21/0.51    inference(equality_resolution,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2) | k10_relat_1(X0,X1) != X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ~r2_hidden(sK4(sK0,k10_relat_1(sK2,sK1)),k1_relat_1(sK2)) | ~r2_hidden(k1_funct_1(sK2,sK4(sK0,k10_relat_1(sK2,sK1))),sK1)),
% 0.21/0.51    inference(resolution,[],[f44,f17])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(sK2,X1)) | ~r2_hidden(sK4(X0,k10_relat_1(sK2,X1)),k1_relat_1(sK2)) | ~r2_hidden(k1_funct_1(sK2,sK4(X0,k10_relat_1(sK2,X1))),X1)) )),
% 0.21/0.51    inference(resolution,[],[f41,f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X8,X9] : (r2_hidden(X8,k10_relat_1(sK2,X9)) | ~r2_hidden(k1_funct_1(sK2,X8),X9) | ~r2_hidden(X8,k1_relat_1(sK2))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f36,f13])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X8,X9] : (~v1_relat_1(sK2) | ~r2_hidden(X8,k1_relat_1(sK2)) | ~r2_hidden(k1_funct_1(sK2,X8),X9) | r2_hidden(X8,k10_relat_1(sK2,X9))) )),
% 0.21/0.51    inference(resolution,[],[f14,f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(k1_funct_1(X0,X3),X1) | r2_hidden(X3,k10_relat_1(X0,X1))) )),
% 0.21/0.51    inference(equality_resolution,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(k1_funct_1(X0,X3),X1) | r2_hidden(X3,X2) | k10_relat_1(X0,X1) != X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (28891)------------------------------
% 0.21/0.51  % (28891)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (28891)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (28891)Memory used [KB]: 1791
% 0.21/0.51  % (28891)Time elapsed: 0.086 s
% 0.21/0.51  % (28891)------------------------------
% 0.21/0.51  % (28891)------------------------------
% 0.21/0.51  % (28869)Success in time 0.147 s
%------------------------------------------------------------------------------
