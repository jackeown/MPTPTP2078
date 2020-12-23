%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:55 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 154 expanded)
%              Number of leaves         :    4 (  30 expanded)
%              Depth                    :   18
%              Number of atoms          :  130 ( 559 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f134,plain,(
    $false ),
    inference(subsumption_resolution,[],[f130,f15])).

fof(f15,plain,(
    ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_relat_1)).

fof(f130,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1)) ),
    inference(duplicate_literal_removal,[],[f128])).

fof(f128,plain,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1))
    | r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1)) ),
    inference(resolution,[],[f109,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
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

fof(f109,plain,(
    ! [X6] :
      ( r2_hidden(sK4(k9_relat_1(sK2,sK0),X6),k9_relat_1(sK3,sK1))
      | r1_tarski(k9_relat_1(sK2,sK0),X6) ) ),
    inference(duplicate_literal_removal,[],[f106])).

fof(f106,plain,(
    ! [X6] :
      ( r2_hidden(sK4(k9_relat_1(sK2,sK0),X6),k9_relat_1(sK3,sK1))
      | r1_tarski(k9_relat_1(sK2,sK0),X6)
      | r1_tarski(k9_relat_1(sK2,sK0),X6) ) ),
    inference(resolution,[],[f102,f75])).

fof(f75,plain,(
    ! [X4] :
      ( r2_hidden(sK5(sK4(k9_relat_1(sK2,sK0),X4),sK0,sK3),sK1)
      | r1_tarski(k9_relat_1(sK2,sK0),X4) ) ),
    inference(resolution,[],[f68,f14])).

fof(f14,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | r2_hidden(sK5(sK4(k9_relat_1(sK2,X0),X1),X0,sK3),X2)
      | r1_tarski(k9_relat_1(sK2,X0),X1) ) ),
    inference(resolution,[],[f67,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f67,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK5(sK4(k9_relat_1(sK2,X2),X3),X2,sK3),X2)
      | r1_tarski(k9_relat_1(sK2,X2),X3) ) ),
    inference(subsumption_resolution,[],[f62,f12])).

fof(f12,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f7])).

fof(f62,plain,(
    ! [X2,X3] :
      ( r1_tarski(k9_relat_1(sK2,X2),X3)
      | r2_hidden(sK5(sK4(k9_relat_1(sK2,X2),X3),X2,sK3),X2)
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f47,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK5(X0,X1,X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f47,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK4(k9_relat_1(sK2,X2),X3),k9_relat_1(sK3,X2))
      | r1_tarski(k9_relat_1(sK2,X2),X3) ) ),
    inference(resolution,[],[f45,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | r2_hidden(sK4(X0,X1),X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f18,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f45,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK3,X0)) ),
    inference(subsumption_resolution,[],[f44,f16])).

fof(f16,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK2)
      | r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f40,f12])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK3)
      | ~ v1_relat_1(sK2)
      | r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK3,X0)) ) ),
    inference(resolution,[],[f17,f13])).

fof(f13,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f7])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_relat_1)).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(sK4(k9_relat_1(sK2,X0),X1),X0,sK3),X2)
      | r2_hidden(sK4(k9_relat_1(sK2,X0),X1),k9_relat_1(sK3,X2))
      | r1_tarski(k9_relat_1(sK2,X0),X1) ) ),
    inference(subsumption_resolution,[],[f101,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(sK4(k9_relat_1(sK2,X0),X1),X0,sK3),k1_relat_1(sK3))
      | r1_tarski(k9_relat_1(sK2,X0),X1) ) ),
    inference(subsumption_resolution,[],[f61,f12])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(sK2,X0),X1)
      | r2_hidden(sK5(sK4(k9_relat_1(sK2,X0),X1),X0,sK3),k1_relat_1(sK3))
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f47,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(sK4(k9_relat_1(sK2,X0),X1),X0,sK3),k1_relat_1(sK3))
      | ~ r2_hidden(sK5(sK4(k9_relat_1(sK2,X0),X1),X0,sK3),X2)
      | r2_hidden(sK4(k9_relat_1(sK2,X0),X1),k9_relat_1(sK3,X2))
      | r1_tarski(k9_relat_1(sK2,X0),X1) ) ),
    inference(subsumption_resolution,[],[f100,f12])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(sK4(k9_relat_1(sK2,X0),X1),X0,sK3),k1_relat_1(sK3))
      | ~ v1_relat_1(sK3)
      | ~ r2_hidden(sK5(sK4(k9_relat_1(sK2,X0),X1),X0,sK3),X2)
      | r2_hidden(sK4(k9_relat_1(sK2,X0),X1),k9_relat_1(sK3,X2))
      | r1_tarski(k9_relat_1(sK2,X0),X1) ) ),
    inference(resolution,[],[f24,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK5(sK4(k9_relat_1(sK2,X0),X1),X0,sK3),sK4(k9_relat_1(sK2,X0),X1)),sK3)
      | r1_tarski(k9_relat_1(sK2,X0),X1) ) ),
    inference(subsumption_resolution,[],[f80,f12])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK5(sK4(k9_relat_1(sK2,X0),X1),X0,sK3),sK4(k9_relat_1(sK2,X0),X1)),sK3)
      | ~ v1_relat_1(sK3)
      | r1_tarski(k9_relat_1(sK2,X0),X1) ) ),
    inference(resolution,[],[f22,f47])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:07:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (21013)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.20/0.47  % (21011)WARNING: option uwaf not known.
% 0.20/0.47  % (21011)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.20/0.47  % (21005)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.20/0.48  % (21001)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.20/0.48  % (21007)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.20/0.48  % (21007)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f134,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(subsumption_resolution,[],[f130,f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ~r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1))),
% 0.20/0.48    inference(cnf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.20/0.48    inference(flattening,[],[f6])).
% 0.20/0.48  fof(f6,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) & (r1_tarski(X0,X1) & r1_tarski(X2,X3))) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)))))),
% 0.20/0.48    inference(negated_conjecture,[],[f4])).
% 0.20/0.48  fof(f4,conjecture,(
% 0.20/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_relat_1)).
% 0.20/0.48  fof(f130,plain,(
% 0.20/0.48    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1))),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f128])).
% 0.20/0.48  fof(f128,plain,(
% 0.20/0.48    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1)) | r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1))),
% 0.20/0.48    inference(resolution,[],[f109,f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.48  fof(f109,plain,(
% 0.20/0.48    ( ! [X6] : (r2_hidden(sK4(k9_relat_1(sK2,sK0),X6),k9_relat_1(sK3,sK1)) | r1_tarski(k9_relat_1(sK2,sK0),X6)) )),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f106])).
% 0.20/0.48  fof(f106,plain,(
% 0.20/0.48    ( ! [X6] : (r2_hidden(sK4(k9_relat_1(sK2,sK0),X6),k9_relat_1(sK3,sK1)) | r1_tarski(k9_relat_1(sK2,sK0),X6) | r1_tarski(k9_relat_1(sK2,sK0),X6)) )),
% 0.20/0.48    inference(resolution,[],[f102,f75])).
% 0.20/0.48  fof(f75,plain,(
% 0.20/0.48    ( ! [X4] : (r2_hidden(sK5(sK4(k9_relat_1(sK2,sK0),X4),sK0,sK3),sK1) | r1_tarski(k9_relat_1(sK2,sK0),X4)) )),
% 0.20/0.48    inference(resolution,[],[f68,f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    r1_tarski(sK0,sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f7])).
% 0.20/0.48  fof(f68,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | r2_hidden(sK5(sK4(k9_relat_1(sK2,X0),X1),X0,sK3),X2) | r1_tarski(k9_relat_1(sK2,X0),X1)) )),
% 0.20/0.48    inference(resolution,[],[f67,f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    ( ! [X2,X3] : (r2_hidden(sK5(sK4(k9_relat_1(sK2,X2),X3),X2,sK3),X2) | r1_tarski(k9_relat_1(sK2,X2),X3)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f62,f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    v1_relat_1(sK3)),
% 0.20/0.48    inference(cnf_transformation,[],[f7])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    ( ! [X2,X3] : (r1_tarski(k9_relat_1(sK2,X2),X3) | r2_hidden(sK5(sK4(k9_relat_1(sK2,X2),X3),X2,sK3),X2) | ~v1_relat_1(sK3)) )),
% 0.20/0.48    inference(resolution,[],[f47,f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK5(X0,X1,X2),X1) | ~v1_relat_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    ( ! [X2,X3] : (r2_hidden(sK4(k9_relat_1(sK2,X2),X3),k9_relat_1(sK3,X2)) | r1_tarski(k9_relat_1(sK2,X2),X3)) )),
% 0.20/0.48    inference(resolution,[],[f45,f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | r2_hidden(sK4(X0,X1),X2) | r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(resolution,[],[f18,f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    ( ! [X0] : (r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK3,X0))) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f44,f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    v1_relat_1(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f7])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_relat_1(sK2) | r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK3,X0))) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f40,f12])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_relat_1(sK3) | ~v1_relat_1(sK2) | r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK3,X0))) )),
% 0.20/0.48    inference(resolution,[],[f17,f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    r1_tarski(sK2,sK3)),
% 0.20/0.48    inference(cnf_transformation,[],[f7])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(flattening,[],[f8])).
% 0.20/0.48  fof(f8,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : ((r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_relat_1)).
% 0.20/0.48  fof(f102,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r2_hidden(sK5(sK4(k9_relat_1(sK2,X0),X1),X0,sK3),X2) | r2_hidden(sK4(k9_relat_1(sK2,X0),X1),k9_relat_1(sK3,X2)) | r1_tarski(k9_relat_1(sK2,X0),X1)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f101,f66])).
% 0.20/0.48  fof(f66,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(sK5(sK4(k9_relat_1(sK2,X0),X1),X0,sK3),k1_relat_1(sK3)) | r1_tarski(k9_relat_1(sK2,X0),X1)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f61,f12])).
% 0.20/0.48  fof(f61,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,X0),X1) | r2_hidden(sK5(sK4(k9_relat_1(sK2,X0),X1),X0,sK3),k1_relat_1(sK3)) | ~v1_relat_1(sK3)) )),
% 0.20/0.48    inference(resolution,[],[f47,f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f101,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r2_hidden(sK5(sK4(k9_relat_1(sK2,X0),X1),X0,sK3),k1_relat_1(sK3)) | ~r2_hidden(sK5(sK4(k9_relat_1(sK2,X0),X1),X0,sK3),X2) | r2_hidden(sK4(k9_relat_1(sK2,X0),X1),k9_relat_1(sK3,X2)) | r1_tarski(k9_relat_1(sK2,X0),X1)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f100,f12])).
% 0.20/0.48  fof(f100,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r2_hidden(sK5(sK4(k9_relat_1(sK2,X0),X1),X0,sK3),k1_relat_1(sK3)) | ~v1_relat_1(sK3) | ~r2_hidden(sK5(sK4(k9_relat_1(sK2,X0),X1),X0,sK3),X2) | r2_hidden(sK4(k9_relat_1(sK2,X0),X1),k9_relat_1(sK3,X2)) | r1_tarski(k9_relat_1(sK2,X0),X1)) )),
% 0.20/0.48    inference(resolution,[],[f24,f83])).
% 0.20/0.48  fof(f83,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK5(sK4(k9_relat_1(sK2,X0),X1),X0,sK3),sK4(k9_relat_1(sK2,X0),X1)),sK3) | r1_tarski(k9_relat_1(sK2,X0),X1)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f80,f12])).
% 0.20/0.48  fof(f80,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK5(sK4(k9_relat_1(sK2,X0),X1),X0,sK3),sK4(k9_relat_1(sK2,X0),X1)),sK3) | ~v1_relat_1(sK3) | r1_tarski(k9_relat_1(sK2,X0),X1)) )),
% 0.20/0.48    inference(resolution,[],[f22,f47])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2) | ~v1_relat_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)) | ~v1_relat_1(X2) | ~r2_hidden(X3,X1) | r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (21007)------------------------------
% 0.20/0.48  % (21007)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (21007)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (21007)Memory used [KB]: 5373
% 0.20/0.48  % (21007)Time elapsed: 0.064 s
% 0.20/0.48  % (21007)------------------------------
% 0.20/0.48  % (21007)------------------------------
% 0.20/0.49  % (20997)Success in time 0.129 s
%------------------------------------------------------------------------------
