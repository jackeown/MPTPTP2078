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
% DateTime   : Thu Dec  3 12:52:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   28 (  36 expanded)
%              Number of leaves         :    6 (  11 expanded)
%              Depth                    :   12
%              Number of atoms          :  105 ( 123 expanded)
%              Number of equality atoms :   46 (  54 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f112,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f15,f43,f103])).

fof(f103,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,X0)
      | sQ3_eqProxy(k1_funct_1(k6_relat_1(X0),X3),X3) ) ),
    inference(subsumption_resolution,[],[f102,f17])).

fof(f17,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f102,plain,(
    ! [X0,X3] :
      ( sQ3_eqProxy(k1_funct_1(k6_relat_1(X0),X3),X3)
      | ~ r2_hidden(X3,X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f31,f18])).

fof(f18,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0,X3] :
      ( sQ3_eqProxy(k1_funct_1(k6_relat_1(X0),X3),X3)
      | ~ r2_hidden(X3,X0)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_proxy_replacement,[],[f25,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( sQ3_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).

fof(f25,plain,(
    ! [X0,X3] :
      ( k1_funct_1(k6_relat_1(X0),X3) = X3
      | ~ r2_hidden(X3,X0)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(X1,X3) = X3
      | ~ r2_hidden(X3,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
            & r2_hidden(sK2(X0,X1),X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f13])).

fof(f13,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

fof(f43,plain,(
    ~ sQ3_eqProxy(k1_funct_1(k6_relat_1(sK1),sK0),sK0) ),
    inference(resolution,[],[f41,f28])).

fof(f28,plain,(
    ~ sQ3_eqProxy(sK0,k1_funct_1(k6_relat_1(sK1),sK0)) ),
    inference(equality_proxy_replacement,[],[f16,f27])).

fof(f16,plain,(
    sK0 != k1_funct_1(k6_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( sK0 != k1_funct_1(k6_relat_1(sK1),sK0)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f8])).

fof(f8,plain,
    ( ? [X0,X1] :
        ( k1_funct_1(k6_relat_1(X1),X0) != X0
        & r2_hidden(X0,X1) )
   => ( sK0 != k1_funct_1(k6_relat_1(sK1),sK0)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1] :
      ( k1_funct_1(k6_relat_1(X1),X0) != X0
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k1_funct_1(k6_relat_1(X1),X0) = X0 ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_funct_1(k6_relat_1(X1),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( sQ3_eqProxy(X1,X0)
      | ~ sQ3_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f27])).

fof(f15,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:35:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (22045)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.47  % (22043)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.47  % (22041)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.47  % (22043)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f112,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f15,f43,f103])).
% 0.20/0.47  fof(f103,plain,(
% 0.20/0.47    ( ! [X0,X3] : (~r2_hidden(X3,X0) | sQ3_eqProxy(k1_funct_1(k6_relat_1(X0),X3),X3)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f102,f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.20/0.47  fof(f102,plain,(
% 0.20/0.47    ( ! [X0,X3] : (sQ3_eqProxy(k1_funct_1(k6_relat_1(X0),X3),X3) | ~r2_hidden(X3,X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f31,f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ( ! [X0,X3] : (sQ3_eqProxy(k1_funct_1(k6_relat_1(X0),X3),X3) | ~r2_hidden(X3,X0) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.47    inference(equality_proxy_replacement,[],[f25,f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ! [X1,X0] : (sQ3_eqProxy(X0,X1) <=> X0 = X1)),
% 0.20/0.47    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ( ! [X0,X3] : (k1_funct_1(k6_relat_1(X0),X3) = X3 | ~r2_hidden(X3,X0) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.47    inference(equality_resolution,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ( ! [X0,X3,X1] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0) | k6_relat_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X1,X0] : (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) => (sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(rectify,[],[f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(flattening,[],[f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0)) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(nnf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,plain,(
% 0.20/0.47    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(flattening,[],[f6])).
% 0.20/0.47  fof(f6,plain,(
% 0.20/0.47    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    ~sQ3_eqProxy(k1_funct_1(k6_relat_1(sK1),sK0),sK0)),
% 0.20/0.47    inference(resolution,[],[f41,f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ~sQ3_eqProxy(sK0,k1_funct_1(k6_relat_1(sK1),sK0))),
% 0.20/0.47    inference(equality_proxy_replacement,[],[f16,f27])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    sK0 != k1_funct_1(k6_relat_1(sK1),sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    sK0 != k1_funct_1(k6_relat_1(sK1),sK0) & r2_hidden(sK0,sK1)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f8])).
% 0.20/0.47  fof(f8,plain,(
% 0.20/0.47    ? [X0,X1] : (k1_funct_1(k6_relat_1(X1),X0) != X0 & r2_hidden(X0,X1)) => (sK0 != k1_funct_1(k6_relat_1(sK1),sK0) & r2_hidden(sK0,sK1))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f5,plain,(
% 0.20/0.47    ? [X0,X1] : (k1_funct_1(k6_relat_1(X1),X0) != X0 & r2_hidden(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1] : (r2_hidden(X0,X1) => k1_funct_1(k6_relat_1(X1),X0) = X0)),
% 0.20/0.47    inference(negated_conjecture,[],[f3])).
% 0.20/0.47  fof(f3,conjecture,(
% 0.20/0.47    ! [X0,X1] : (r2_hidden(X0,X1) => k1_funct_1(k6_relat_1(X1),X0) = X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_1)).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    ( ! [X0,X1] : (sQ3_eqProxy(X1,X0) | ~sQ3_eqProxy(X0,X1)) )),
% 0.20/0.47    inference(equality_proxy_axiom,[],[f27])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    r2_hidden(sK0,sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (22043)------------------------------
% 0.20/0.47  % (22043)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (22043)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (22043)Memory used [KB]: 6140
% 0.20/0.47  % (22043)Time elapsed: 0.067 s
% 0.20/0.47  % (22043)------------------------------
% 0.20/0.47  % (22043)------------------------------
% 0.20/0.48  % (22037)Success in time 0.121 s
%------------------------------------------------------------------------------
