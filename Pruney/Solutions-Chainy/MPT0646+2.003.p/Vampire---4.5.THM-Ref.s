%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:42 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 274 expanded)
%              Number of leaves         :    6 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :  193 (1534 expanded)
%              Number of equality atoms :   47 ( 297 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f462,plain,(
    $false ),
    inference(subsumption_resolution,[],[f461,f308])).

fof(f308,plain,(
    k5_relat_1(sK2(sK0),k5_relat_1(sK0,sK1)) = k5_relat_1(sK3(sK0),k5_relat_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f302,f159])).

fof(f159,plain,(
    k5_relat_1(sK2(sK0),k5_relat_1(sK0,sK1)) = k5_relat_1(k5_relat_1(sK2(sK0),sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f13,f43,f16,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f16,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ? [X1] :
          ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ? [X1] :
          ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( ? [X1] :
              ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & v1_funct_1(X1)
              & v1_relat_1(X1) )
         => v2_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ? [X1] :
            ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_funct_1)).

fof(f43,plain,(
    v1_relat_1(sK2(sK0)) ),
    inference(unit_resulting_resolution,[],[f18,f16,f17,f34])).

fof(f34,plain,(
    ! [X0] :
      ( v1_relat_1(sK2(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k5_relat_1(X1,X0) != k5_relat_1(X2,X0)
                | k1_relat_1(X1) != k1_relat_1(X2)
                | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k5_relat_1(X1,X0) != k5_relat_1(X2,X0)
                | k1_relat_1(X1) != k1_relat_1(X2)
                | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( k5_relat_1(X1,X0) = k5_relat_1(X2,X0)
                    & k1_relat_1(X1) = k1_relat_1(X2)
                    & r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                    & r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) )
                 => X1 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_funct_1)).

fof(f17,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f18,plain,(
    ~ v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f13,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f302,plain,(
    k5_relat_1(sK3(sK0),k5_relat_1(sK0,sK1)) = k5_relat_1(k5_relat_1(sK2(sK0),sK0),sK1) ),
    inference(forward_demodulation,[],[f165,f59])).

fof(f59,plain,(
    k5_relat_1(sK2(sK0),sK0) = k5_relat_1(sK3(sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f16,f18,f17,f31])).

fof(f31,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | k5_relat_1(sK2(X0),X0) = k5_relat_1(sK3(X0),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f165,plain,(
    k5_relat_1(sK3(sK0),k5_relat_1(sK0,sK1)) = k5_relat_1(k5_relat_1(sK3(sK0),sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f13,f41,f16,f25])).

fof(f41,plain,(
    v1_relat_1(sK3(sK0)) ),
    inference(unit_resulting_resolution,[],[f18,f16,f17,f26])).

fof(f26,plain,(
    ! [X0] :
      ( v1_relat_1(sK3(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f461,plain,(
    k5_relat_1(sK2(sK0),k5_relat_1(sK0,sK1)) != k5_relat_1(sK3(sK0),k5_relat_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f452,f15])).

fof(f15,plain,(
    k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f452,plain,(
    k5_relat_1(sK2(sK0),k6_relat_1(k1_relat_1(sK0))) != k5_relat_1(sK3(sK0),k6_relat_1(k1_relat_1(sK0))) ),
    inference(unit_resulting_resolution,[],[f44,f43,f42,f41,f49,f46,f45,f52,f399])).

fof(f399,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X1) != k1_relat_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X2),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X2,k6_relat_1(X0)) != k5_relat_1(X1,k6_relat_1(X0))
      | X1 = X2 ) ),
    inference(subsumption_resolution,[],[f398,f20])).

fof(f20,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f398,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X2),X0)
      | k1_relat_1(X1) != k1_relat_1(X2)
      | k5_relat_1(X2,k6_relat_1(X0)) != k5_relat_1(X1,k6_relat_1(X0))
      | X1 = X2
      | ~ v2_funct_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f397,f19])).

fof(f19,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f397,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X2),X0)
      | ~ v1_relat_1(k6_relat_1(X0))
      | k1_relat_1(X1) != k1_relat_1(X2)
      | k5_relat_1(X2,k6_relat_1(X0)) != k5_relat_1(X1,k6_relat_1(X0))
      | X1 = X2
      | ~ v2_funct_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f388,f22])).

fof(f22,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f388,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X2),X0)
      | ~ v1_relat_1(k6_relat_1(X0))
      | k1_relat_1(X1) != k1_relat_1(X2)
      | k5_relat_1(X2,k6_relat_1(X0)) != k5_relat_1(X1,k6_relat_1(X0))
      | X1 = X2
      | ~ v2_funct_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f33,f23])).

fof(f23,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k1_relat_1(X1) != k1_relat_1(X2)
      | k5_relat_1(X1,X0) != k5_relat_1(X2,X0)
      | X1 = X2
      | ~ v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f52,plain,(
    k1_relat_1(sK2(sK0)) = k1_relat_1(sK3(sK0)) ),
    inference(unit_resulting_resolution,[],[f16,f18,f17,f30])).

fof(f30,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | k1_relat_1(sK2(X0)) = k1_relat_1(sK3(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f45,plain,(
    sK3(sK0) != sK2(sK0) ),
    inference(unit_resulting_resolution,[],[f18,f16,f17,f32])).

fof(f32,plain,(
    ! [X0] :
      ( sK2(X0) != sK3(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f46,plain,(
    r1_tarski(k2_relat_1(sK2(sK0)),k1_relat_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f18,f16,f17,f28])).

fof(f28,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(sK2(X0)),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f49,plain,(
    r1_tarski(k2_relat_1(sK3(sK0)),k1_relat_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f18,f16,f17,f29])).

fof(f29,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(sK3(X0)),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f42,plain,(
    v1_funct_1(sK3(sK0)) ),
    inference(unit_resulting_resolution,[],[f18,f16,f17,f27])).

% (17811)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
fof(f27,plain,(
    ! [X0] :
      ( v1_funct_1(sK3(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f44,plain,(
    v1_funct_1(sK2(sK0)) ),
    inference(unit_resulting_resolution,[],[f18,f16,f17,f35])).

% (17805)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
fof(f35,plain,(
    ! [X0] :
      ( v1_funct_1(sK2(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:13:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (17815)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.50  % (17797)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.50  % (17793)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.51  % (17793)Refutation not found, incomplete strategy% (17793)------------------------------
% 0.22/0.51  % (17793)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (17806)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (17798)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (17813)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.51  % (17816)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.51  % (17800)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.51  % (17817)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.52  % (17803)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.52  % (17794)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (17807)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.52  % (17804)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  % (17801)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.52  % (17814)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.52  % (17818)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.52  % (17799)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.53  % (17795)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.53  % (17810)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.53  % (17802)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.53  % (17799)Refutation not found, incomplete strategy% (17799)------------------------------
% 0.22/0.53  % (17799)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (17799)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (17799)Memory used [KB]: 10618
% 0.22/0.53  % (17799)Time elapsed: 0.071 s
% 0.22/0.53  % (17799)------------------------------
% 0.22/0.53  % (17799)------------------------------
% 0.22/0.53  % (17793)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (17793)Memory used [KB]: 10874
% 0.22/0.53  % (17793)Time elapsed: 0.090 s
% 0.22/0.53  % (17793)------------------------------
% 0.22/0.53  % (17793)------------------------------
% 0.22/0.53  % (17796)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.53  % (17800)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f462,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(subsumption_resolution,[],[f461,f308])).
% 0.22/0.53  fof(f308,plain,(
% 0.22/0.53    k5_relat_1(sK2(sK0),k5_relat_1(sK0,sK1)) = k5_relat_1(sK3(sK0),k5_relat_1(sK0,sK1))),
% 0.22/0.53    inference(backward_demodulation,[],[f302,f159])).
% 0.22/0.53  fof(f159,plain,(
% 0.22/0.53    k5_relat_1(sK2(sK0),k5_relat_1(sK0,sK1)) = k5_relat_1(k5_relat_1(sK2(sK0),sK0),sK1)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f13,f43,f16,f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    v1_relat_1(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,plain,(
% 0.22/0.53    ? [X0] : (~v2_funct_1(X0) & ? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.53    inference(flattening,[],[f8])).
% 0.22/0.53  fof(f8,plain,(
% 0.22/0.53    ? [X0] : ((~v2_funct_1(X0) & ? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,negated_conjecture,(
% 0.22/0.53    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) => v2_funct_1(X0)))),
% 0.22/0.53    inference(negated_conjecture,[],[f6])).
% 0.22/0.53  fof(f6,conjecture,(
% 0.22/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) => v2_funct_1(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_funct_1)).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    v1_relat_1(sK2(sK0))),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f18,f16,f17,f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ( ! [X0] : (v1_relat_1(sK2(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v2_funct_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ! [X0] : ((v2_funct_1(X0) <=> ! [X1] : (! [X2] : (X1 = X2 | k5_relat_1(X1,X0) != k5_relat_1(X2,X0) | k1_relat_1(X1) != k1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(flattening,[],[f11])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ! [X0] : ((v2_funct_1(X0) <=> ! [X1] : (! [X2] : ((X1 = X2 | (k5_relat_1(X1,X0) != k5_relat_1(X2,X0) | k1_relat_1(X1) != k1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X1,X0) = k5_relat_1(X2,X0) & k1_relat_1(X1) = k1_relat_1(X2) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(X0))) => X1 = X2)))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_funct_1)).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    v1_funct_1(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f9])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ~v2_funct_1(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f9])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    v1_relat_1(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f9])).
% 0.22/0.53  fof(f302,plain,(
% 0.22/0.53    k5_relat_1(sK3(sK0),k5_relat_1(sK0,sK1)) = k5_relat_1(k5_relat_1(sK2(sK0),sK0),sK1)),
% 0.22/0.53    inference(forward_demodulation,[],[f165,f59])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    k5_relat_1(sK2(sK0),sK0) = k5_relat_1(sK3(sK0),sK0)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f16,f18,f17,f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ( ! [X0] : (v2_funct_1(X0) | ~v1_funct_1(X0) | k5_relat_1(sK2(X0),X0) = k5_relat_1(sK3(X0),X0) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f165,plain,(
% 0.22/0.53    k5_relat_1(sK3(sK0),k5_relat_1(sK0,sK1)) = k5_relat_1(k5_relat_1(sK3(sK0),sK0),sK1)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f13,f41,f16,f25])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    v1_relat_1(sK3(sK0))),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f18,f16,f17,f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ( ! [X0] : (v1_relat_1(sK3(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v2_funct_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f461,plain,(
% 0.22/0.53    k5_relat_1(sK2(sK0),k5_relat_1(sK0,sK1)) != k5_relat_1(sK3(sK0),k5_relat_1(sK0,sK1))),
% 0.22/0.53    inference(forward_demodulation,[],[f452,f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0))),
% 0.22/0.53    inference(cnf_transformation,[],[f9])).
% 0.22/0.53  fof(f452,plain,(
% 0.22/0.53    k5_relat_1(sK2(sK0),k6_relat_1(k1_relat_1(sK0))) != k5_relat_1(sK3(sK0),k6_relat_1(k1_relat_1(sK0)))),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f44,f43,f42,f41,f49,f46,f45,f52,f399])).
% 0.22/0.53  fof(f399,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k1_relat_1(X1) != k1_relat_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X2),X0) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X2,k6_relat_1(X0)) != k5_relat_1(X1,k6_relat_1(X0)) | X1 = X2) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f398,f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.22/0.53  fof(f398,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X1) != k1_relat_1(X2) | k5_relat_1(X2,k6_relat_1(X0)) != k5_relat_1(X1,k6_relat_1(X0)) | X1 = X2 | ~v2_funct_1(k6_relat_1(X0))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f397,f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f4])).
% 0.22/0.53  fof(f397,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X2),X0) | ~v1_relat_1(k6_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(X2) | k5_relat_1(X2,k6_relat_1(X0)) != k5_relat_1(X1,k6_relat_1(X0)) | X1 = X2 | ~v2_funct_1(k6_relat_1(X0))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f388,f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.22/0.53  fof(f388,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X2),X0) | ~v1_relat_1(k6_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(X2) | k5_relat_1(X2,k6_relat_1(X0)) != k5_relat_1(X1,k6_relat_1(X0)) | X1 = X2 | ~v2_funct_1(k6_relat_1(X0))) )),
% 0.22/0.53    inference(superposition,[],[f33,f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v1_relat_1(X0) | k1_relat_1(X1) != k1_relat_1(X2) | k5_relat_1(X1,X0) != k5_relat_1(X2,X0) | X1 = X2 | ~v2_funct_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    k1_relat_1(sK2(sK0)) = k1_relat_1(sK3(sK0))),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f16,f18,f17,f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ( ! [X0] : (v2_funct_1(X0) | ~v1_funct_1(X0) | k1_relat_1(sK2(X0)) = k1_relat_1(sK3(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    sK3(sK0) != sK2(sK0)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f18,f16,f17,f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ( ! [X0] : (sK2(X0) != sK3(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v2_funct_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    r1_tarski(k2_relat_1(sK2(sK0)),k1_relat_1(sK0))),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f18,f16,f17,f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ( ! [X0] : (r1_tarski(k2_relat_1(sK2(X0)),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v2_funct_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    r1_tarski(k2_relat_1(sK3(sK0)),k1_relat_1(sK0))),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f18,f16,f17,f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ( ! [X0] : (r1_tarski(k2_relat_1(sK3(X0)),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v2_funct_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    v1_funct_1(sK3(sK0))),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f18,f16,f17,f27])).
% 0.22/0.53  % (17811)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ( ! [X0] : (v1_funct_1(sK3(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v2_funct_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    v1_funct_1(sK2(sK0))),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f18,f16,f17,f35])).
% 0.22/0.53  % (17805)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ( ! [X0] : (v1_funct_1(sK2(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v2_funct_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (17800)------------------------------
% 0.22/0.53  % (17800)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (17800)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (17800)Memory used [KB]: 2174
% 0.22/0.53  % (17800)Time elapsed: 0.111 s
% 0.22/0.53  % (17800)------------------------------
% 0.22/0.53  % (17800)------------------------------
% 0.22/0.54  % (17792)Success in time 0.171 s
%------------------------------------------------------------------------------
