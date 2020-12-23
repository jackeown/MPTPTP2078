%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:56 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 180 expanded)
%              Number of leaves         :    6 (  50 expanded)
%              Depth                    :   22
%              Number of atoms          :  211 (1091 expanded)
%              Number of equality atoms :  136 ( 629 expanded)
%              Maximal formula depth    :   12 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f147,plain,(
    $false ),
    inference(subsumption_resolution,[],[f17,f146])).

fof(f146,plain,(
    ! [X4,X2] : X2 = X4 ),
    inference(subsumption_resolution,[],[f132,f131])).

fof(f131,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_relat_1(sK1(sK0,X1))) ),
    inference(superposition,[],[f27,f124])).

fof(f124,plain,(
    ! [X8,X9] : k1_tarski(X8) = k2_relat_1(sK1(sK0,X9)) ),
    inference(subsumption_resolution,[],[f114,f17])).

fof(f114,plain,(
    ! [X8,X9] :
      ( k1_tarski(X8) = k2_relat_1(sK1(sK0,X9))
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f21,f97])).

fof(f97,plain,(
    ! [X0,X1] : sK1(sK0,X0) = sK1(sK0,X1) ),
    inference(subsumption_resolution,[],[f96,f17])).

fof(f96,plain,(
    ! [X0,X1] :
      ( sK1(sK0,X0) = sK1(sK0,X1)
      | k1_xboole_0 = sK0 ) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( sK0 != X0
      | sK1(X0,X1) = sK1(sK0,X2)
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f94,f17])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( sK0 != X0
      | sK1(X0,X1) = sK1(sK0,X2)
      | k1_xboole_0 = X0
      | k1_xboole_0 = sK0 ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( sK0 != X2
      | sK0 != X0
      | sK1(X0,X1) = sK1(X2,X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2 ) ),
    inference(duplicate_literal_removal,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( sK0 != X0
      | sK0 != X2
      | sK1(X0,X1) = sK1(X2,X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f91,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK1(X0,X1)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tarski(X1) = k2_relat_1(sK1(X0,X1))
          & k1_relat_1(sK1(X0,X1)) = X0
          & v1_funct_1(sK1(X0,X1))
          & v1_relat_1(sK1(X0,X1)) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f7,f10])).

fof(f10,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( k1_tarski(X1) = k2_relat_1(sK1(X0,X1))
        & k1_relat_1(sK1(X0,X1)) = X0
        & v1_funct_1(sK1(X0,X1))
        & v1_relat_1(sK1(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( sK0 != k1_relat_1(sK1(X2,X3))
      | sK0 != X0
      | sK1(X0,X1) = sK1(X2,X3)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( sK0 != X0
      | sK0 != k1_relat_1(sK1(X2,X3))
      | sK1(X0,X1) = sK1(X2,X3)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f89,f20])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( sK0 != k1_relat_1(sK1(X2,X3))
      | sK0 != k1_relat_1(sK1(X0,X1))
      | sK1(X0,X1) = sK1(X2,X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2 ) ),
    inference(subsumption_resolution,[],[f88,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK1(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( sK0 != k1_relat_1(sK1(X0,X1))
      | sK0 != k1_relat_1(sK1(X2,X3))
      | ~ v1_relat_1(sK1(X2,X3))
      | sK1(X0,X1) = sK1(X2,X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2 ) ),
    inference(resolution,[],[f69,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK1(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | sK0 != k1_relat_1(sK1(X1,X2))
      | sK0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | sK1(X1,X2) = X0
      | k1_xboole_0 = X1 ) ),
    inference(subsumption_resolution,[],[f68,f18])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( sK0 != k1_relat_1(X0)
      | sK0 != k1_relat_1(sK1(X1,X2))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sK1(X1,X2) = X0
      | ~ v1_relat_1(sK1(X1,X2))
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f16,f19])).

fof(f16,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(X1)
      | k1_relat_1(X2) != sK0
      | k1_relat_1(X1) != sK0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | X1 = X2
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( k1_xboole_0 != sK0
    & ! [X1] :
        ( ! [X2] :
            ( X1 = X2
            | k1_relat_1(X2) != sK0
            | k1_relat_1(X1) != sK0
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f8])).

fof(f8,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k1_relat_1(X2) != X0
                | k1_relat_1(X1) != X0
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) ) )
   => ( k1_xboole_0 != sK0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != sK0
              | k1_relat_1(X1) != sK0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( k1_relat_1(X2) = X0
                    & k1_relat_1(X1) = X0 )
                 => X1 = X2 ) ) )
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( ( k1_relat_1(X2) = X0
                  & k1_relat_1(X1) = X0 )
               => X1 = X2 ) ) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_1)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK1(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f14])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f132,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X4,k2_relat_1(sK1(sK0,X3)))
      | X2 = X4 ) ),
    inference(superposition,[],[f28,f124])).

fof(f28,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f17,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:59:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (25719)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.44  % (25719)Refutation not found, incomplete strategy% (25719)------------------------------
% 0.20/0.44  % (25719)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (25719)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.44  
% 0.20/0.44  % (25719)Memory used [KB]: 10490
% 0.20/0.44  % (25719)Time elapsed: 0.053 s
% 0.20/0.44  % (25719)------------------------------
% 0.20/0.44  % (25719)------------------------------
% 0.20/0.47  % (25725)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.47  % (25744)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.48  % (25722)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.48  % (25725)Refutation not found, incomplete strategy% (25725)------------------------------
% 0.20/0.48  % (25725)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (25725)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (25725)Memory used [KB]: 10490
% 0.20/0.48  % (25725)Time elapsed: 0.070 s
% 0.20/0.48  % (25725)------------------------------
% 0.20/0.48  % (25725)------------------------------
% 0.20/0.48  % (25722)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f147,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(subsumption_resolution,[],[f17,f146])).
% 0.20/0.48  fof(f146,plain,(
% 0.20/0.48    ( ! [X4,X2] : (X2 = X4) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f132,f131])).
% 0.20/0.48  fof(f131,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(X0,k2_relat_1(sK1(sK0,X1)))) )),
% 0.20/0.48    inference(superposition,[],[f27,f124])).
% 0.20/0.48  fof(f124,plain,(
% 0.20/0.48    ( ! [X8,X9] : (k1_tarski(X8) = k2_relat_1(sK1(sK0,X9))) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f114,f17])).
% 0.20/0.48  fof(f114,plain,(
% 0.20/0.48    ( ! [X8,X9] : (k1_tarski(X8) = k2_relat_1(sK1(sK0,X9)) | k1_xboole_0 = sK0) )),
% 0.20/0.48    inference(superposition,[],[f21,f97])).
% 0.20/0.48  fof(f97,plain,(
% 0.20/0.48    ( ! [X0,X1] : (sK1(sK0,X0) = sK1(sK0,X1)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f96,f17])).
% 0.20/0.48  fof(f96,plain,(
% 0.20/0.48    ( ! [X0,X1] : (sK1(sK0,X0) = sK1(sK0,X1) | k1_xboole_0 = sK0) )),
% 0.20/0.48    inference(equality_resolution,[],[f95])).
% 0.20/0.48  fof(f95,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (sK0 != X0 | sK1(X0,X1) = sK1(sK0,X2) | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f94,f17])).
% 0.20/0.48  fof(f94,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (sK0 != X0 | sK1(X0,X1) = sK1(sK0,X2) | k1_xboole_0 = X0 | k1_xboole_0 = sK0) )),
% 0.20/0.48    inference(equality_resolution,[],[f93])).
% 0.20/0.48  fof(f93,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (sK0 != X2 | sK0 != X0 | sK1(X0,X1) = sK1(X2,X3) | k1_xboole_0 = X0 | k1_xboole_0 = X2) )),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f92])).
% 0.20/0.48  fof(f92,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (sK0 != X0 | sK0 != X2 | sK1(X0,X1) = sK1(X2,X3) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(superposition,[],[f91,f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_relat_1(sK1(X0,X1)) = X0 | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (k1_tarski(X1) = k2_relat_1(sK1(X0,X1)) & k1_relat_1(sK1(X0,X1)) = X0 & v1_funct_1(sK1(X0,X1)) & v1_relat_1(sK1(X0,X1))) | k1_xboole_0 = X0)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f7,f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ! [X1,X0] : (? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_tarski(X1) = k2_relat_1(sK1(X0,X1)) & k1_relat_1(sK1(X0,X1)) = X0 & v1_funct_1(sK1(X0,X1)) & v1_relat_1(sK1(X0,X1))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f7,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).
% 0.20/0.48  fof(f91,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (sK0 != k1_relat_1(sK1(X2,X3)) | sK0 != X0 | sK1(X0,X1) = sK1(X2,X3) | k1_xboole_0 = X2 | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f90])).
% 0.20/0.48  fof(f90,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (sK0 != X0 | sK0 != k1_relat_1(sK1(X2,X3)) | sK1(X0,X1) = sK1(X2,X3) | k1_xboole_0 = X2 | k1_xboole_0 = X0 | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(superposition,[],[f89,f20])).
% 0.20/0.48  fof(f89,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (sK0 != k1_relat_1(sK1(X2,X3)) | sK0 != k1_relat_1(sK1(X0,X1)) | sK1(X0,X1) = sK1(X2,X3) | k1_xboole_0 = X0 | k1_xboole_0 = X2) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f88,f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ( ! [X0,X1] : (v1_relat_1(sK1(X0,X1)) | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f88,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (sK0 != k1_relat_1(sK1(X0,X1)) | sK0 != k1_relat_1(sK1(X2,X3)) | ~v1_relat_1(sK1(X2,X3)) | sK1(X0,X1) = sK1(X2,X3) | k1_xboole_0 = X0 | k1_xboole_0 = X2) )),
% 0.20/0.48    inference(resolution,[],[f69,f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ( ! [X0,X1] : (v1_funct_1(sK1(X0,X1)) | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f69,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | sK0 != k1_relat_1(sK1(X1,X2)) | sK0 != k1_relat_1(X0) | ~v1_relat_1(X0) | sK1(X1,X2) = X0 | k1_xboole_0 = X1) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f68,f18])).
% 0.20/0.48  fof(f68,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (sK0 != k1_relat_1(X0) | sK0 != k1_relat_1(sK1(X1,X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | sK1(X1,X2) = X0 | ~v1_relat_1(sK1(X1,X2)) | k1_xboole_0 = X1) )),
% 0.20/0.48    inference(resolution,[],[f16,f19])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ( ! [X2,X1] : (~v1_funct_1(X1) | k1_relat_1(X2) != sK0 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | X1 = X2 | ~v1_relat_1(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    k1_xboole_0 != sK0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK0 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f8])).
% 0.20/0.48  fof(f8,plain,(
% 0.20/0.48    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) => (k1_xboole_0 != sK0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK0 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f6,plain,(
% 0.20/0.48    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.48    inference(flattening,[],[f5])).
% 0.20/0.48  fof(f5,plain,(
% 0.20/0.48    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : ((X1 = X2 | (k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,negated_conjecture,(
% 0.20/0.48    ~! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 0.20/0.48    inference(negated_conjecture,[],[f3])).
% 0.20/0.48  fof(f3,conjecture,(
% 0.20/0.48    ! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_1)).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK1(X0,X1)) | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 0.20/0.48    inference(equality_resolution,[],[f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 0.20/0.48    inference(equality_resolution,[],[f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.48    inference(rectify,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.48    inference(nnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.20/0.48  fof(f132,plain,(
% 0.20/0.48    ( ! [X4,X2,X3] : (~r2_hidden(X4,k2_relat_1(sK1(sK0,X3))) | X2 = X4) )),
% 0.20/0.48    inference(superposition,[],[f28,f124])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.20/0.48    inference(equality_resolution,[],[f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    k1_xboole_0 != sK0),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (25722)------------------------------
% 0.20/0.48  % (25722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (25722)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (25722)Memory used [KB]: 6140
% 0.20/0.48  % (25722)Time elapsed: 0.081 s
% 0.20/0.48  % (25722)------------------------------
% 0.20/0.48  % (25722)------------------------------
% 0.20/0.48  % (25737)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.48  % (25727)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.49  % (25736)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.49  % (25739)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.49  % (25715)Success in time 0.14 s
%------------------------------------------------------------------------------
