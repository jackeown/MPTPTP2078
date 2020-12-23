%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 453 expanded)
%              Number of leaves         :    5 ( 101 expanded)
%              Depth                    :   21
%              Number of atoms          :  202 (1537 expanded)
%              Number of equality atoms :   24 ( 144 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f108,plain,(
    $false ),
    inference(subsumption_resolution,[],[f107,f57])).

fof(f57,plain,(
    r2_hidden(sK0,sK2) ),
    inference(subsumption_resolution,[],[f56,f39])).

fof(f39,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),k6_relat_1(X0))
      | r2_hidden(X2,X0) ) ),
    inference(subsumption_resolution,[],[f36,f16])).

fof(f16,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f36,plain,(
    ! [X2,X0,X3] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | r2_hidden(X2,X0)
      | ~ r2_hidden(k4_tarski(X2,X3),k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | r2_hidden(X2,X0)
      | ~ r2_hidden(k4_tarski(X2,X3),X1)
      | k6_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_relat_1)).

fof(f56,plain,
    ( r2_hidden(k4_tarski(sK0,sK6(k6_relat_1(sK2),sK3,sK0,sK1)),k6_relat_1(sK2))
    | r2_hidden(sK0,sK2) ),
    inference(subsumption_resolution,[],[f55,f16])).

fof(f55,plain,
    ( r2_hidden(k4_tarski(sK0,sK6(k6_relat_1(sK2),sK3,sK0,sK1)),k6_relat_1(sK2))
    | ~ v1_relat_1(k6_relat_1(sK2))
    | r2_hidden(sK0,sK2) ),
    inference(subsumption_resolution,[],[f52,f15])).

fof(f15,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      <~> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) ) )
      & v1_relat_1(X3) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
        <=> ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X0,X2) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_relat_1)).

fof(f52,plain,
    ( ~ v1_relat_1(sK3)
    | r2_hidden(k4_tarski(sK0,sK6(k6_relat_1(sK2),sK3,sK0,sK1)),k6_relat_1(sK2))
    | ~ v1_relat_1(k6_relat_1(sK2))
    | r2_hidden(sK0,sK2) ),
    inference(resolution,[],[f41,f13])).

fof(f13,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(k6_relat_1(sK2),sK3))
    | r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f41,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | r2_hidden(k4_tarski(X3,sK6(X0,X1,X3,X4)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f32,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f32,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X3,sK6(X0,X1,X3,X4)),X0)
      | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X3,sK6(X0,X1,X3,X4)),X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k5_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

fof(f107,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(resolution,[],[f105,f37])).

fof(f37,plain,(
    ! [X0,X3] :
      ( r2_hidden(k4_tarski(X3,X3),k6_relat_1(X0))
      | ~ r2_hidden(X3,X0) ) ),
    inference(subsumption_resolution,[],[f34,f16])).

fof(f34,plain,(
    ! [X0,X3] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | ~ r2_hidden(X3,X0)
      | r2_hidden(k4_tarski(X3,X3),k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(k4_tarski(X3,X3),X1)
      | k6_relat_1(X0) != X1 ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X2,X0)
      | X2 != X3
      | r2_hidden(k4_tarski(X2,X3),X1)
      | k6_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f105,plain,(
    ~ r2_hidden(k4_tarski(sK0,sK0),k6_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f100,f16])).

fof(f100,plain,
    ( ~ v1_relat_1(k6_relat_1(sK2))
    | ~ r2_hidden(k4_tarski(sK0,sK0),k6_relat_1(sK2)) ),
    inference(resolution,[],[f91,f88])).

fof(f88,plain,(
    ~ r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(k6_relat_1(sK2),sK3)) ),
    inference(subsumption_resolution,[],[f58,f87])).

fof(f87,plain,(
    r2_hidden(k4_tarski(sK0,sK1),sK3) ),
    inference(duplicate_literal_removal,[],[f85])).

fof(f85,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK3)
    | r2_hidden(k4_tarski(sK0,sK1),sK3) ),
    inference(backward_demodulation,[],[f66,f83])).

fof(f83,plain,(
    sK0 = sK6(k6_relat_1(sK2),sK3,sK0,sK1) ),
    inference(subsumption_resolution,[],[f82,f57])).

fof(f82,plain,
    ( sK0 = sK6(k6_relat_1(sK2),sK3,sK0,sK1)
    | ~ r2_hidden(sK0,sK2) ),
    inference(resolution,[],[f81,f37])).

fof(f81,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK0),k6_relat_1(sK2))
    | sK0 = sK6(k6_relat_1(sK2),sK3,sK0,sK1) ),
    inference(subsumption_resolution,[],[f80,f62])).

fof(f62,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK3)
    | sK0 = sK6(k6_relat_1(sK2),sK3,sK0,sK1) ),
    inference(resolution,[],[f54,f38])).

fof(f38,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),k6_relat_1(X0))
      | X2 = X3 ) ),
    inference(subsumption_resolution,[],[f35,f16])).

fof(f35,plain,(
    ! [X2,X0,X3] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | X2 = X3
      | ~ r2_hidden(k4_tarski(X2,X3),k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | X2 = X3
      | ~ r2_hidden(k4_tarski(X2,X3),X1)
      | k6_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f54,plain,
    ( r2_hidden(k4_tarski(sK0,sK6(k6_relat_1(sK2),sK3,sK0,sK1)),k6_relat_1(sK2))
    | r2_hidden(k4_tarski(sK0,sK1),sK3) ),
    inference(subsumption_resolution,[],[f53,f16])).

fof(f53,plain,
    ( r2_hidden(k4_tarski(sK0,sK6(k6_relat_1(sK2),sK3,sK0,sK1)),k6_relat_1(sK2))
    | ~ v1_relat_1(k6_relat_1(sK2))
    | r2_hidden(k4_tarski(sK0,sK1),sK3) ),
    inference(subsumption_resolution,[],[f51,f15])).

fof(f51,plain,
    ( ~ v1_relat_1(sK3)
    | r2_hidden(k4_tarski(sK0,sK6(k6_relat_1(sK2),sK3,sK0,sK1)),k6_relat_1(sK2))
    | ~ v1_relat_1(k6_relat_1(sK2))
    | r2_hidden(k4_tarski(sK0,sK1),sK3) ),
    inference(resolution,[],[f41,f14])).

fof(f14,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(k6_relat_1(sK2),sK3))
    | r2_hidden(k4_tarski(sK0,sK1),sK3) ),
    inference(cnf_transformation,[],[f7])).

fof(f80,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK0),k6_relat_1(sK2))
    | sK0 = sK6(k6_relat_1(sK2),sK3,sK0,sK1)
    | ~ r2_hidden(k4_tarski(sK0,sK1),sK3) ),
    inference(subsumption_resolution,[],[f75,f16])).

fof(f75,plain,
    ( ~ v1_relat_1(k6_relat_1(sK2))
    | ~ r2_hidden(k4_tarski(sK0,sK0),k6_relat_1(sK2))
    | sK0 = sK6(k6_relat_1(sK2),sK3,sK0,sK1)
    | ~ r2_hidden(k4_tarski(sK0,sK1),sK3) ),
    inference(resolution,[],[f71,f58])).

% (13382)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
fof(f71,plain,(
    ! [X4,X3] :
      ( r2_hidden(k4_tarski(X3,sK1),k5_relat_1(X4,sK3))
      | ~ v1_relat_1(X4)
      | ~ r2_hidden(k4_tarski(X3,sK0),X4)
      | sK0 = sK6(k6_relat_1(sK2),sK3,sK0,sK1) ) ),
    inference(resolution,[],[f67,f62])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),sK3)
      | ~ r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X1,X3),k5_relat_1(X0,sK3)) ) ),
    inference(resolution,[],[f43,f15])).

fof(f43,plain,(
    ! [X4,X0,X5,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X3,X5),X0)
      | ~ r2_hidden(k4_tarski(X5,X4),X1)
      | r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f30,f29])).

fof(f30,plain,(
    ! [X4,X0,X5,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X3,X5),X0)
      | ~ r2_hidden(k4_tarski(X5,X4),X1)
      | r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X3,X5),X0)
      | ~ r2_hidden(k4_tarski(X5,X4),X1)
      | r2_hidden(k4_tarski(X3,X4),X2)
      | k5_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f66,plain,
    ( r2_hidden(k4_tarski(sK6(k6_relat_1(sK2),sK3,sK0,sK1),sK1),sK3)
    | r2_hidden(k4_tarski(sK0,sK1),sK3) ),
    inference(subsumption_resolution,[],[f65,f16])).

fof(f65,plain,
    ( r2_hidden(k4_tarski(sK6(k6_relat_1(sK2),sK3,sK0,sK1),sK1),sK3)
    | ~ v1_relat_1(k6_relat_1(sK2))
    | r2_hidden(k4_tarski(sK0,sK1),sK3) ),
    inference(subsumption_resolution,[],[f63,f15])).

fof(f63,plain,
    ( ~ v1_relat_1(sK3)
    | r2_hidden(k4_tarski(sK6(k6_relat_1(sK2),sK3,sK0,sK1),sK1),sK3)
    | ~ v1_relat_1(k6_relat_1(sK2))
    | r2_hidden(k4_tarski(sK0,sK1),sK3) ),
    inference(resolution,[],[f42,f14])).

fof(f42,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | r2_hidden(k4_tarski(sK6(X0,X1,X3,X4),X4),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f31,f29])).

fof(f31,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | r2_hidden(k4_tarski(sK6(X0,X1,X3,X4),X4),X1)
      | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK6(X0,X1,X3,X4),X4),X1)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k5_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f58,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(k6_relat_1(sK2),sK3))
    | ~ r2_hidden(k4_tarski(sK0,sK1),sK3) ),
    inference(subsumption_resolution,[],[f12,f57])).

fof(f12,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(k6_relat_1(sK2),sK3))
    | ~ r2_hidden(k4_tarski(sK0,sK1),sK3)
    | ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X0,sK1),k5_relat_1(X1,sK3))
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(X0,sK0),X1) ) ),
    inference(resolution,[],[f87,f67])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:45:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.48  % (13380)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.49  % (13364)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.49  % (13365)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.49  % (13357)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (13363)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.50  % (13376)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.50  % (13358)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (13358)Refutation not found, incomplete strategy% (13358)------------------------------
% 0.21/0.50  % (13358)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (13358)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (13358)Memory used [KB]: 10618
% 0.21/0.50  % (13358)Time elapsed: 0.096 s
% 0.21/0.50  % (13358)------------------------------
% 0.21/0.50  % (13358)------------------------------
% 0.21/0.50  % (13362)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (13360)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (13369)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.50  % (13361)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (13359)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (13378)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % (13367)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.51  % (13371)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (13374)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.51  % (13372)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (13373)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.52  % (13376)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (13377)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.52  % (13379)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.52  % (13366)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f107,f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    r2_hidden(sK0,sK2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f56,f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X2,X3),k6_relat_1(X0)) | r2_hidden(X2,X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f36,f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ( ! [X2,X0,X3] : (~v1_relat_1(k6_relat_1(X0)) | r2_hidden(X2,X0) | ~r2_hidden(k4_tarski(X2,X3),k6_relat_1(X0))) )),
% 0.21/0.52    inference(equality_resolution,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X1) | r2_hidden(X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1) | k6_relat_1(X0) != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> (X2 = X3 & r2_hidden(X2,X0)))) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => (k6_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> (X2 = X3 & r2_hidden(X2,X0)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_relat_1)).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK0,sK6(k6_relat_1(sK2),sK3,sK0,sK1)),k6_relat_1(sK2)) | r2_hidden(sK0,sK2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f55,f16])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK0,sK6(k6_relat_1(sK2),sK3,sK0,sK1)),k6_relat_1(sK2)) | ~v1_relat_1(k6_relat_1(sK2)) | r2_hidden(sK0,sK2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f52,f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    v1_relat_1(sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) <~> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2))) & v1_relat_1(X3))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2,X3] : (v1_relat_1(X3) => (r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2))))),
% 0.21/0.52    inference(negated_conjecture,[],[f5])).
% 0.21/0.52  fof(f5,conjecture,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (v1_relat_1(X3) => (r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_relat_1)).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ~v1_relat_1(sK3) | r2_hidden(k4_tarski(sK0,sK6(k6_relat_1(sK2),sK3,sK0,sK1)),k6_relat_1(sK2)) | ~v1_relat_1(k6_relat_1(sK2)) | r2_hidden(sK0,sK2)),
% 0.21/0.52    inference(resolution,[],[f41,f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(k6_relat_1(sK2),sK3)) | r2_hidden(sK0,sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X4,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | r2_hidden(k4_tarski(X3,sK6(X0,X1,X3,X4)),X0) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f32,f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(flattening,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X4,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(k5_relat_1(X0,X1)) | r2_hidden(k4_tarski(X3,sK6(X0,X1,X3,X4)),X0) | ~r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1))) )),
% 0.21/0.52    inference(equality_resolution,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(X3,sK6(X0,X1,X3,X4)),X0) | ~r2_hidden(k4_tarski(X3,X4),X2) | k5_relat_1(X0,X1) != X2) )),
% 0.21/0.52    inference(cnf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    ~r2_hidden(sK0,sK2)),
% 0.21/0.52    inference(resolution,[],[f105,f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X0,X3] : (r2_hidden(k4_tarski(X3,X3),k6_relat_1(X0)) | ~r2_hidden(X3,X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f34,f16])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X0,X3] : (~v1_relat_1(k6_relat_1(X0)) | ~r2_hidden(X3,X0) | r2_hidden(k4_tarski(X3,X3),k6_relat_1(X0))) )),
% 0.21/0.52    inference(equality_resolution,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (~v1_relat_1(X1) | ~r2_hidden(X3,X0) | r2_hidden(k4_tarski(X3,X3),X1) | k6_relat_1(X0) != X1) )),
% 0.21/0.52    inference(equality_resolution,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X1) | ~r2_hidden(X2,X0) | X2 != X3 | r2_hidden(k4_tarski(X2,X3),X1) | k6_relat_1(X0) != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    ~r2_hidden(k4_tarski(sK0,sK0),k6_relat_1(sK2))),
% 0.21/0.52    inference(subsumption_resolution,[],[f100,f16])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    ~v1_relat_1(k6_relat_1(sK2)) | ~r2_hidden(k4_tarski(sK0,sK0),k6_relat_1(sK2))),
% 0.21/0.52    inference(resolution,[],[f91,f88])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    ~r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(k6_relat_1(sK2),sK3))),
% 0.21/0.52    inference(subsumption_resolution,[],[f58,f87])).
% 0.21/0.52  fof(f87,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK0,sK1),sK3)),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f85])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK0,sK1),sK3) | r2_hidden(k4_tarski(sK0,sK1),sK3)),
% 0.21/0.52    inference(backward_demodulation,[],[f66,f83])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    sK0 = sK6(k6_relat_1(sK2),sK3,sK0,sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f82,f57])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    sK0 = sK6(k6_relat_1(sK2),sK3,sK0,sK1) | ~r2_hidden(sK0,sK2)),
% 0.21/0.52    inference(resolution,[],[f81,f37])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    ~r2_hidden(k4_tarski(sK0,sK0),k6_relat_1(sK2)) | sK0 = sK6(k6_relat_1(sK2),sK3,sK0,sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f80,f62])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK0,sK1),sK3) | sK0 = sK6(k6_relat_1(sK2),sK3,sK0,sK1)),
% 0.21/0.52    inference(resolution,[],[f54,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X2,X3),k6_relat_1(X0)) | X2 = X3) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f35,f16])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X2,X0,X3] : (~v1_relat_1(k6_relat_1(X0)) | X2 = X3 | ~r2_hidden(k4_tarski(X2,X3),k6_relat_1(X0))) )),
% 0.21/0.52    inference(equality_resolution,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X1) | X2 = X3 | ~r2_hidden(k4_tarski(X2,X3),X1) | k6_relat_1(X0) != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK0,sK6(k6_relat_1(sK2),sK3,sK0,sK1)),k6_relat_1(sK2)) | r2_hidden(k4_tarski(sK0,sK1),sK3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f53,f16])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK0,sK6(k6_relat_1(sK2),sK3,sK0,sK1)),k6_relat_1(sK2)) | ~v1_relat_1(k6_relat_1(sK2)) | r2_hidden(k4_tarski(sK0,sK1),sK3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f51,f15])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ~v1_relat_1(sK3) | r2_hidden(k4_tarski(sK0,sK6(k6_relat_1(sK2),sK3,sK0,sK1)),k6_relat_1(sK2)) | ~v1_relat_1(k6_relat_1(sK2)) | r2_hidden(k4_tarski(sK0,sK1),sK3)),
% 0.21/0.52    inference(resolution,[],[f41,f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(k6_relat_1(sK2),sK3)) | r2_hidden(k4_tarski(sK0,sK1),sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    ~r2_hidden(k4_tarski(sK0,sK0),k6_relat_1(sK2)) | sK0 = sK6(k6_relat_1(sK2),sK3,sK0,sK1) | ~r2_hidden(k4_tarski(sK0,sK1),sK3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f75,f16])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    ~v1_relat_1(k6_relat_1(sK2)) | ~r2_hidden(k4_tarski(sK0,sK0),k6_relat_1(sK2)) | sK0 = sK6(k6_relat_1(sK2),sK3,sK0,sK1) | ~r2_hidden(k4_tarski(sK0,sK1),sK3)),
% 0.21/0.52    inference(resolution,[],[f71,f58])).
% 0.21/0.52  % (13382)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    ( ! [X4,X3] : (r2_hidden(k4_tarski(X3,sK1),k5_relat_1(X4,sK3)) | ~v1_relat_1(X4) | ~r2_hidden(k4_tarski(X3,sK0),X4) | sK0 = sK6(k6_relat_1(sK2),sK3,sK0,sK1)) )),
% 0.21/0.52    inference(resolution,[],[f67,f62])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),sK3) | ~r2_hidden(k4_tarski(X1,X2),X0) | ~v1_relat_1(X0) | r2_hidden(k4_tarski(X1,X3),k5_relat_1(X0,sK3))) )),
% 0.21/0.52    inference(resolution,[],[f43,f15])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X4,X0,X5,X3,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X3,X5),X0) | ~r2_hidden(k4_tarski(X5,X4),X1) | r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f30,f29])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X4,X0,X5,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X3,X5),X0) | ~r2_hidden(k4_tarski(X5,X4),X1) | r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1))) )),
% 0.21/0.52    inference(equality_resolution,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X3,X5),X0) | ~r2_hidden(k4_tarski(X5,X4),X1) | r2_hidden(k4_tarski(X3,X4),X2) | k5_relat_1(X0,X1) != X2) )),
% 0.21/0.52    inference(cnf_transformation,[],[f8])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK6(k6_relat_1(sK2),sK3,sK0,sK1),sK1),sK3) | r2_hidden(k4_tarski(sK0,sK1),sK3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f65,f16])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK6(k6_relat_1(sK2),sK3,sK0,sK1),sK1),sK3) | ~v1_relat_1(k6_relat_1(sK2)) | r2_hidden(k4_tarski(sK0,sK1),sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f63,f15])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ~v1_relat_1(sK3) | r2_hidden(k4_tarski(sK6(k6_relat_1(sK2),sK3,sK0,sK1),sK1),sK3) | ~v1_relat_1(k6_relat_1(sK2)) | r2_hidden(k4_tarski(sK0,sK1),sK3)),
% 0.21/0.53    inference(resolution,[],[f42,f14])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X4,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | r2_hidden(k4_tarski(sK6(X0,X1,X3,X4),X4),X1) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f31,f29])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ( ! [X4,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(k5_relat_1(X0,X1)) | r2_hidden(k4_tarski(sK6(X0,X1,X3,X4),X4),X1) | ~r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1))) )),
% 0.21/0.53    inference(equality_resolution,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(sK6(X0,X1,X3,X4),X4),X1) | ~r2_hidden(k4_tarski(X3,X4),X2) | k5_relat_1(X0,X1) != X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ~r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(k6_relat_1(sK2),sK3)) | ~r2_hidden(k4_tarski(sK0,sK1),sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f12,f57])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ~r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(k6_relat_1(sK2),sK3)) | ~r2_hidden(k4_tarski(sK0,sK1),sK3) | ~r2_hidden(sK0,sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f7])).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,sK1),k5_relat_1(X1,sK3)) | ~v1_relat_1(X1) | ~r2_hidden(k4_tarski(X0,sK0),X1)) )),
% 0.21/0.53    inference(resolution,[],[f87,f67])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (13376)------------------------------
% 0.21/0.53  % (13376)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (13376)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (13376)Memory used [KB]: 1663
% 0.21/0.53  % (13376)Time elapsed: 0.113 s
% 0.21/0.53  % (13376)------------------------------
% 0.21/0.53  % (13376)------------------------------
% 0.21/0.53  % (13356)Success in time 0.169 s
%------------------------------------------------------------------------------
