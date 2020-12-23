%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:42 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 274 expanded)
%              Number of leaves         :    6 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :  192 (1533 expanded)
%              Number of equality atoms :   47 ( 297 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f513,plain,(
    $false ),
    inference(subsumption_resolution,[],[f512,f327])).

fof(f327,plain,(
    k5_relat_1(sK2(sK0),k5_relat_1(sK0,sK1)) = k5_relat_1(sK3(sK0),k5_relat_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f321,f178])).

fof(f178,plain,(
    k5_relat_1(sK2(sK0),k5_relat_1(sK0,sK1)) = k5_relat_1(k5_relat_1(sK2(sK0),sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f16,f46,f19,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
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
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f19,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ? [X1] :
          ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ? [X1] :
          ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( ? [X1] :
              ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & v1_funct_1(X1)
              & v1_relat_1(X1) )
         => v2_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ? [X1] :
            ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_funct_1)).

fof(f46,plain,(
    v1_relat_1(sK2(sK0)) ),
    inference(unit_resulting_resolution,[],[f21,f19,f20,f37])).

fof(f37,plain,(
    ! [X0] :
      ( v1_relat_1(sK2(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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

fof(f20,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f21,plain,(
    ~ v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f16,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f321,plain,(
    k5_relat_1(sK3(sK0),k5_relat_1(sK0,sK1)) = k5_relat_1(k5_relat_1(sK2(sK0),sK0),sK1) ),
    inference(forward_demodulation,[],[f184,f62])).

fof(f62,plain,(
    k5_relat_1(sK2(sK0),sK0) = k5_relat_1(sK3(sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f19,f21,f20,f34])).

fof(f34,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | k5_relat_1(sK2(X0),X0) = k5_relat_1(sK3(X0),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f184,plain,(
    k5_relat_1(sK3(sK0),k5_relat_1(sK0,sK1)) = k5_relat_1(k5_relat_1(sK3(sK0),sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f16,f44,f19,f28])).

fof(f44,plain,(
    v1_relat_1(sK3(sK0)) ),
    inference(unit_resulting_resolution,[],[f21,f19,f20,f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_relat_1(sK3(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f512,plain,(
    k5_relat_1(sK2(sK0),k5_relat_1(sK0,sK1)) != k5_relat_1(sK3(sK0),k5_relat_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f495,f18])).

fof(f18,plain,(
    k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f495,plain,(
    k5_relat_1(sK2(sK0),k6_relat_1(k1_relat_1(sK0))) != k5_relat_1(sK3(sK0),k6_relat_1(k1_relat_1(sK0))) ),
    inference(unit_resulting_resolution,[],[f45,f44,f47,f46,f49,f52,f48,f55,f422])).

fof(f422,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X1) != k1_relat_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X2),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) != k5_relat_1(X2,k6_relat_1(X0))
      | X1 = X2 ) ),
    inference(subsumption_resolution,[],[f421,f22])).

fof(f22,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

fof(f421,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X2),X0)
      | k1_relat_1(X1) != k1_relat_1(X2)
      | k5_relat_1(X1,k6_relat_1(X0)) != k5_relat_1(X2,k6_relat_1(X0))
      | X1 = X2
      | ~ v2_funct_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f420,f23])).

fof(f23,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f420,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X2),X0)
      | ~ v1_relat_1(k6_relat_1(X0))
      | k1_relat_1(X1) != k1_relat_1(X2)
      | k5_relat_1(X1,k6_relat_1(X0)) != k5_relat_1(X2,k6_relat_1(X0))
      | X1 = X2
      | ~ v2_funct_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f410,f24])).

fof(f24,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f410,plain,(
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
      | k5_relat_1(X1,k6_relat_1(X0)) != k5_relat_1(X2,k6_relat_1(X0))
      | X1 = X2
      | ~ v2_funct_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f36,f25])).

fof(f25,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f36,plain,(
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
    inference(cnf_transformation,[],[f15])).

fof(f55,plain,(
    k1_relat_1(sK2(sK0)) = k1_relat_1(sK3(sK0)) ),
    inference(unit_resulting_resolution,[],[f19,f21,f20,f33])).

fof(f33,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | k1_relat_1(sK2(X0)) = k1_relat_1(sK3(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f48,plain,(
    sK3(sK0) != sK2(sK0) ),
    inference(unit_resulting_resolution,[],[f21,f19,f20,f35])).

fof(f35,plain,(
    ! [X0] :
      ( sK2(X0) != sK3(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f52,plain,(
    r1_tarski(k2_relat_1(sK3(sK0)),k1_relat_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f21,f19,f20,f32])).

fof(f32,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(sK3(X0)),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f49,plain,(
    r1_tarski(k2_relat_1(sK2(sK0)),k1_relat_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f21,f19,f20,f31])).

fof(f31,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(sK2(X0)),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f47,plain,(
    v1_funct_1(sK2(sK0)) ),
    inference(unit_resulting_resolution,[],[f21,f19,f20,f38])).

fof(f38,plain,(
    ! [X0] :
      ( v1_funct_1(sK2(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f45,plain,(
    v1_funct_1(sK3(sK0)) ),
    inference(unit_resulting_resolution,[],[f21,f19,f20,f30])).

fof(f30,plain,(
    ! [X0] :
      ( v1_funct_1(sK3(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:01:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (6915)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.49  % (6935)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.49  % (6914)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.49  % (6931)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.50  % (6927)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.50  % (6925)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.50  % (6922)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.50  % (6919)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.50  % (6928)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.50  % (6924)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.50  % (6917)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.50  % (6921)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.50  % (6930)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.50  % (6913)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.51  % (6937)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.51  % (6936)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.51  % (6919)Refutation not found, incomplete strategy% (6919)------------------------------
% 0.20/0.51  % (6919)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (6919)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (6919)Memory used [KB]: 10746
% 0.20/0.51  % (6919)Time elapsed: 0.063 s
% 0.20/0.51  % (6919)------------------------------
% 0.20/0.51  % (6919)------------------------------
% 0.20/0.51  % (6916)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.51  % (6929)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.51  % (6920)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.52  % (6938)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.52  % (6918)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.52  % (6933)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.52  % (6932)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.32/0.52  % (6923)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.32/0.53  % (6913)Refutation not found, incomplete strategy% (6913)------------------------------
% 1.32/0.53  % (6913)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  % (6913)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.53  
% 1.32/0.53  % (6913)Memory used [KB]: 10874
% 1.32/0.53  % (6913)Time elapsed: 0.122 s
% 1.32/0.53  % (6913)------------------------------
% 1.32/0.53  % (6913)------------------------------
% 1.32/0.53  % (6934)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.44/0.55  % (6926)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.44/0.56  % (6920)Refutation found. Thanks to Tanya!
% 1.44/0.56  % SZS status Theorem for theBenchmark
% 1.44/0.56  % SZS output start Proof for theBenchmark
% 1.44/0.56  fof(f513,plain,(
% 1.44/0.56    $false),
% 1.44/0.56    inference(subsumption_resolution,[],[f512,f327])).
% 1.44/0.56  fof(f327,plain,(
% 1.44/0.56    k5_relat_1(sK2(sK0),k5_relat_1(sK0,sK1)) = k5_relat_1(sK3(sK0),k5_relat_1(sK0,sK1))),
% 1.44/0.56    inference(backward_demodulation,[],[f321,f178])).
% 1.44/0.56  fof(f178,plain,(
% 1.44/0.56    k5_relat_1(sK2(sK0),k5_relat_1(sK0,sK1)) = k5_relat_1(k5_relat_1(sK2(sK0),sK0),sK1)),
% 1.44/0.56    inference(unit_resulting_resolution,[],[f16,f46,f19,f28])).
% 1.44/0.56  fof(f28,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))) )),
% 1.44/0.56    inference(cnf_transformation,[],[f13])).
% 1.44/0.56  fof(f13,plain,(
% 1.44/0.56    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.44/0.56    inference(ennf_transformation,[],[f2])).
% 1.44/0.56  fof(f2,axiom,(
% 1.44/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 1.44/0.56  fof(f19,plain,(
% 1.44/0.56    v1_relat_1(sK0)),
% 1.44/0.56    inference(cnf_transformation,[],[f10])).
% 1.44/0.56  fof(f10,plain,(
% 1.44/0.56    ? [X0] : (~v2_funct_1(X0) & ? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.44/0.56    inference(flattening,[],[f9])).
% 1.44/0.56  fof(f9,plain,(
% 1.44/0.56    ? [X0] : ((~v2_funct_1(X0) & ? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.44/0.56    inference(ennf_transformation,[],[f8])).
% 1.44/0.56  fof(f8,negated_conjecture,(
% 1.44/0.56    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) => v2_funct_1(X0)))),
% 1.44/0.56    inference(negated_conjecture,[],[f7])).
% 1.44/0.56  fof(f7,conjecture,(
% 1.44/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) => v2_funct_1(X0)))),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_funct_1)).
% 1.44/0.56  fof(f46,plain,(
% 1.44/0.56    v1_relat_1(sK2(sK0))),
% 1.44/0.56    inference(unit_resulting_resolution,[],[f21,f19,f20,f37])).
% 1.44/0.56  fof(f37,plain,(
% 1.44/0.56    ( ! [X0] : (v1_relat_1(sK2(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v2_funct_1(X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f15])).
% 1.44/0.56  fof(f15,plain,(
% 1.44/0.56    ! [X0] : ((v2_funct_1(X0) <=> ! [X1] : (! [X2] : (X1 = X2 | k5_relat_1(X1,X0) != k5_relat_1(X2,X0) | k1_relat_1(X1) != k1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.44/0.56    inference(flattening,[],[f14])).
% 1.44/0.56  fof(f14,plain,(
% 1.44/0.56    ! [X0] : ((v2_funct_1(X0) <=> ! [X1] : (! [X2] : ((X1 = X2 | (k5_relat_1(X1,X0) != k5_relat_1(X2,X0) | k1_relat_1(X1) != k1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.44/0.56    inference(ennf_transformation,[],[f5])).
% 1.44/0.56  fof(f5,axiom,(
% 1.44/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X1,X0) = k5_relat_1(X2,X0) & k1_relat_1(X1) = k1_relat_1(X2) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(X0))) => X1 = X2)))))),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_funct_1)).
% 1.44/0.56  fof(f20,plain,(
% 1.44/0.56    v1_funct_1(sK0)),
% 1.44/0.56    inference(cnf_transformation,[],[f10])).
% 1.44/0.56  fof(f21,plain,(
% 1.44/0.56    ~v2_funct_1(sK0)),
% 1.44/0.56    inference(cnf_transformation,[],[f10])).
% 1.44/0.56  fof(f16,plain,(
% 1.44/0.56    v1_relat_1(sK1)),
% 1.44/0.56    inference(cnf_transformation,[],[f10])).
% 1.44/0.56  fof(f321,plain,(
% 1.44/0.56    k5_relat_1(sK3(sK0),k5_relat_1(sK0,sK1)) = k5_relat_1(k5_relat_1(sK2(sK0),sK0),sK1)),
% 1.44/0.56    inference(forward_demodulation,[],[f184,f62])).
% 1.44/0.56  fof(f62,plain,(
% 1.44/0.56    k5_relat_1(sK2(sK0),sK0) = k5_relat_1(sK3(sK0),sK0)),
% 1.44/0.56    inference(unit_resulting_resolution,[],[f19,f21,f20,f34])).
% 1.44/0.56  fof(f34,plain,(
% 1.44/0.56    ( ! [X0] : (v2_funct_1(X0) | ~v1_funct_1(X0) | k5_relat_1(sK2(X0),X0) = k5_relat_1(sK3(X0),X0) | ~v1_relat_1(X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f15])).
% 1.44/0.56  fof(f184,plain,(
% 1.44/0.56    k5_relat_1(sK3(sK0),k5_relat_1(sK0,sK1)) = k5_relat_1(k5_relat_1(sK3(sK0),sK0),sK1)),
% 1.44/0.56    inference(unit_resulting_resolution,[],[f16,f44,f19,f28])).
% 1.44/0.56  fof(f44,plain,(
% 1.44/0.56    v1_relat_1(sK3(sK0))),
% 1.44/0.56    inference(unit_resulting_resolution,[],[f21,f19,f20,f29])).
% 1.44/0.56  fof(f29,plain,(
% 1.44/0.56    ( ! [X0] : (v1_relat_1(sK3(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v2_funct_1(X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f15])).
% 1.44/0.56  fof(f512,plain,(
% 1.44/0.56    k5_relat_1(sK2(sK0),k5_relat_1(sK0,sK1)) != k5_relat_1(sK3(sK0),k5_relat_1(sK0,sK1))),
% 1.44/0.56    inference(forward_demodulation,[],[f495,f18])).
% 1.44/0.56  fof(f18,plain,(
% 1.44/0.56    k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0))),
% 1.44/0.56    inference(cnf_transformation,[],[f10])).
% 1.44/0.56  fof(f495,plain,(
% 1.44/0.56    k5_relat_1(sK2(sK0),k6_relat_1(k1_relat_1(sK0))) != k5_relat_1(sK3(sK0),k6_relat_1(k1_relat_1(sK0)))),
% 1.44/0.56    inference(unit_resulting_resolution,[],[f45,f44,f47,f46,f49,f52,f48,f55,f422])).
% 1.44/0.56  fof(f422,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (k1_relat_1(X1) != k1_relat_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X2),X0) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) != k5_relat_1(X2,k6_relat_1(X0)) | X1 = X2) )),
% 1.44/0.56    inference(subsumption_resolution,[],[f421,f22])).
% 1.44/0.56  fof(f22,plain,(
% 1.44/0.56    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.44/0.56    inference(cnf_transformation,[],[f6])).
% 1.44/0.56  fof(f6,axiom,(
% 1.44/0.56    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).
% 1.44/0.56  fof(f421,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X1) != k1_relat_1(X2) | k5_relat_1(X1,k6_relat_1(X0)) != k5_relat_1(X2,k6_relat_1(X0)) | X1 = X2 | ~v2_funct_1(k6_relat_1(X0))) )),
% 1.44/0.56    inference(subsumption_resolution,[],[f420,f23])).
% 1.44/0.56  fof(f23,plain,(
% 1.44/0.56    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.44/0.56    inference(cnf_transformation,[],[f4])).
% 1.44/0.56  fof(f4,axiom,(
% 1.44/0.56    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.44/0.56  fof(f420,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X2),X0) | ~v1_relat_1(k6_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(X2) | k5_relat_1(X1,k6_relat_1(X0)) != k5_relat_1(X2,k6_relat_1(X0)) | X1 = X2 | ~v2_funct_1(k6_relat_1(X0))) )),
% 1.44/0.56    inference(subsumption_resolution,[],[f410,f24])).
% 1.44/0.56  fof(f24,plain,(
% 1.44/0.56    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 1.44/0.56    inference(cnf_transformation,[],[f4])).
% 1.44/0.56  fof(f410,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X2),X0) | ~v1_relat_1(k6_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(X2) | k5_relat_1(X1,k6_relat_1(X0)) != k5_relat_1(X2,k6_relat_1(X0)) | X1 = X2 | ~v2_funct_1(k6_relat_1(X0))) )),
% 1.44/0.56    inference(superposition,[],[f36,f25])).
% 1.44/0.56  fof(f25,plain,(
% 1.44/0.56    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.44/0.56    inference(cnf_transformation,[],[f3])).
% 1.44/0.56  fof(f3,axiom,(
% 1.44/0.56    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.44/0.56  fof(f36,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (~r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v1_relat_1(X0) | k1_relat_1(X1) != k1_relat_1(X2) | k5_relat_1(X1,X0) != k5_relat_1(X2,X0) | X1 = X2 | ~v2_funct_1(X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f15])).
% 1.44/0.56  fof(f55,plain,(
% 1.44/0.56    k1_relat_1(sK2(sK0)) = k1_relat_1(sK3(sK0))),
% 1.44/0.56    inference(unit_resulting_resolution,[],[f19,f21,f20,f33])).
% 1.44/0.56  fof(f33,plain,(
% 1.44/0.56    ( ! [X0] : (v2_funct_1(X0) | ~v1_funct_1(X0) | k1_relat_1(sK2(X0)) = k1_relat_1(sK3(X0)) | ~v1_relat_1(X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f15])).
% 1.44/0.56  fof(f48,plain,(
% 1.44/0.56    sK3(sK0) != sK2(sK0)),
% 1.44/0.56    inference(unit_resulting_resolution,[],[f21,f19,f20,f35])).
% 1.44/0.56  fof(f35,plain,(
% 1.44/0.56    ( ! [X0] : (sK2(X0) != sK3(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v2_funct_1(X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f15])).
% 1.44/0.56  fof(f52,plain,(
% 1.44/0.56    r1_tarski(k2_relat_1(sK3(sK0)),k1_relat_1(sK0))),
% 1.44/0.56    inference(unit_resulting_resolution,[],[f21,f19,f20,f32])).
% 1.44/0.56  fof(f32,plain,(
% 1.44/0.56    ( ! [X0] : (r1_tarski(k2_relat_1(sK3(X0)),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v2_funct_1(X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f15])).
% 1.44/0.56  fof(f49,plain,(
% 1.44/0.56    r1_tarski(k2_relat_1(sK2(sK0)),k1_relat_1(sK0))),
% 1.44/0.56    inference(unit_resulting_resolution,[],[f21,f19,f20,f31])).
% 1.44/0.56  fof(f31,plain,(
% 1.44/0.56    ( ! [X0] : (r1_tarski(k2_relat_1(sK2(X0)),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v2_funct_1(X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f15])).
% 1.44/0.56  fof(f47,plain,(
% 1.44/0.56    v1_funct_1(sK2(sK0))),
% 1.44/0.56    inference(unit_resulting_resolution,[],[f21,f19,f20,f38])).
% 1.44/0.56  fof(f38,plain,(
% 1.44/0.56    ( ! [X0] : (v1_funct_1(sK2(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v2_funct_1(X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f15])).
% 1.44/0.56  fof(f45,plain,(
% 1.44/0.56    v1_funct_1(sK3(sK0))),
% 1.44/0.56    inference(unit_resulting_resolution,[],[f21,f19,f20,f30])).
% 1.44/0.56  fof(f30,plain,(
% 1.44/0.56    ( ! [X0] : (v1_funct_1(sK3(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v2_funct_1(X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f15])).
% 1.44/0.56  % SZS output end Proof for theBenchmark
% 1.44/0.56  % (6920)------------------------------
% 1.44/0.56  % (6920)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (6920)Termination reason: Refutation
% 1.44/0.56  
% 1.44/0.56  % (6920)Memory used [KB]: 2302
% 1.44/0.56  % (6920)Time elapsed: 0.128 s
% 1.44/0.56  % (6920)------------------------------
% 1.44/0.56  % (6920)------------------------------
% 1.44/0.56  % (6924)Refutation not found, incomplete strategy% (6924)------------------------------
% 1.44/0.56  % (6924)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (6924)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.56  
% 1.44/0.56  % (6924)Memory used [KB]: 11129
% 1.44/0.56  % (6924)Time elapsed: 0.132 s
% 1.44/0.56  % (6924)------------------------------
% 1.44/0.56  % (6924)------------------------------
% 1.44/0.56  % (6912)Success in time 0.205 s
%------------------------------------------------------------------------------
