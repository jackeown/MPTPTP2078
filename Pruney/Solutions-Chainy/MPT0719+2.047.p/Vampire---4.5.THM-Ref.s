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
% DateTime   : Thu Dec  3 12:55:02 EST 2020

% Result     : Theorem 1.21s
% Output     : Refutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :   51 (  71 expanded)
%              Number of leaves         :   11 (  19 expanded)
%              Depth                    :   15
%              Number of atoms          :  182 ( 234 expanded)
%              Number of equality atoms :    5 (   9 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f65,plain,(
    $false ),
    inference(subsumption_resolution,[],[f64,f31])).

fof(f31,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f64,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f63,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f63,plain,(
    r2_hidden(k4_tarski(sK1(sK0,k1_xboole_0),sK2(sK1(sK0,k1_xboole_0),k2_relat_1(k1_xboole_0),k1_xboole_0)),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f61,f45])).

fof(f45,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f33,f32])).

fof(f32,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f33,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f61,plain,
    ( r2_hidden(k4_tarski(sK1(sK0,k1_xboole_0),sK2(sK1(sK0,k1_xboole_0),k2_relat_1(k1_xboole_0),k1_xboole_0)),k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f60,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X1,sK2(X1,k2_relat_1(X0),X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X1,sK2(X1,k2_relat_1(X0),X0)),X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f41,f35])).

fof(f35,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2)
            & r2_hidden(sK2(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f26])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2)
        & r2_hidden(sK2(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X0,X4),X2)
              & r2_hidden(X4,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X0,X3),X2)
              & r2_hidden(X3,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(f60,plain,(
    r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f59,f28])).

fof(f28,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ v5_funct_1(k1_xboole_0,sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ~ v5_funct_1(k1_xboole_0,X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ~ v5_funct_1(k1_xboole_0,sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => v5_funct_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => v5_funct_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).

fof(f59,plain,
    ( r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f58,f29])).

fof(f29,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f58,plain,
    ( r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f57,f45])).

fof(f57,plain,
    ( r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f56,f44])).

fof(f44,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f34,f32])).

fof(f34,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f56,plain,
    ( r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f37,f30])).

fof(f30,plain,(
    ~ v5_funct_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v5_funct_1(X1,X0)
      | r2_hidden(sK1(X0,X1),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ( ~ r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1)))
                & r2_hidden(sK1(X0,X1),k1_relat_1(X1)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
          & r2_hidden(X2,k1_relat_1(X1)) )
     => ( ~ r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1)))
        & r2_hidden(sK1(X0,X1),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  & r2_hidden(X2,k1_relat_1(X1)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  & r2_hidden(X2,k1_relat_1(X1)) ) )
            & ( ! [X2] :
                  ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  | ~ r2_hidden(X2,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,k1_relat_1(X1))
               => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:15:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (1881)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.47  % (1882)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.47  % (1887)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (1887)Refutation not found, incomplete strategy% (1887)------------------------------
% 0.21/0.48  % (1887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (1887)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (1887)Memory used [KB]: 6012
% 0.21/0.48  % (1887)Time elapsed: 0.002 s
% 0.21/0.48  % (1887)------------------------------
% 0.21/0.48  % (1887)------------------------------
% 0.21/0.48  % (1896)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.48  % (1891)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.48  % (1890)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.48  % (1890)Refutation not found, incomplete strategy% (1890)------------------------------
% 0.21/0.48  % (1890)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (1890)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (1890)Memory used [KB]: 10490
% 0.21/0.48  % (1890)Time elapsed: 0.002 s
% 0.21/0.48  % (1890)------------------------------
% 0.21/0.48  % (1890)------------------------------
% 0.21/0.49  % (1882)Refutation not found, incomplete strategy% (1882)------------------------------
% 0.21/0.49  % (1882)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (1882)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (1882)Memory used [KB]: 10490
% 0.21/0.49  % (1882)Time elapsed: 0.069 s
% 0.21/0.49  % (1882)------------------------------
% 0.21/0.49  % (1882)------------------------------
% 0.21/0.51  % (1880)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.51  % (1888)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.51  % (1902)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.51  % (1888)Refutation not found, incomplete strategy% (1888)------------------------------
% 0.21/0.51  % (1888)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (1888)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (1888)Memory used [KB]: 10490
% 0.21/0.51  % (1888)Time elapsed: 0.097 s
% 0.21/0.51  % (1888)------------------------------
% 0.21/0.51  % (1888)------------------------------
% 0.21/0.52  % (1897)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 1.21/0.53  % (1883)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 1.21/0.53  % (1897)Refutation not found, incomplete strategy% (1897)------------------------------
% 1.21/0.53  % (1897)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.53  % (1897)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.53  
% 1.21/0.53  % (1897)Memory used [KB]: 1535
% 1.21/0.53  % (1897)Time elapsed: 0.002 s
% 1.21/0.53  % (1897)------------------------------
% 1.21/0.53  % (1897)------------------------------
% 1.21/0.53  % (1898)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 1.21/0.53  % (1894)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 1.21/0.54  % (1900)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 1.21/0.54  % (1900)Refutation found. Thanks to Tanya!
% 1.21/0.54  % SZS status Theorem for theBenchmark
% 1.21/0.54  % SZS output start Proof for theBenchmark
% 1.21/0.54  fof(f65,plain,(
% 1.21/0.54    $false),
% 1.21/0.54    inference(subsumption_resolution,[],[f64,f31])).
% 1.21/0.54  fof(f31,plain,(
% 1.21/0.54    v1_xboole_0(k1_xboole_0)),
% 1.21/0.54    inference(cnf_transformation,[],[f2])).
% 1.21/0.54  fof(f2,axiom,(
% 1.21/0.54    v1_xboole_0(k1_xboole_0)),
% 1.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.21/0.54  fof(f64,plain,(
% 1.21/0.54    ~v1_xboole_0(k1_xboole_0)),
% 1.21/0.54    inference(resolution,[],[f63,f39])).
% 1.21/0.54  fof(f39,plain,(
% 1.21/0.54    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.21/0.54    inference(cnf_transformation,[],[f16])).
% 1.21/0.54  fof(f16,plain,(
% 1.21/0.54    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 1.21/0.54    inference(ennf_transformation,[],[f10])).
% 1.21/0.54  fof(f10,plain,(
% 1.21/0.54    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 1.21/0.54    inference(unused_predicate_definition_removal,[],[f1])).
% 1.21/0.54  fof(f1,axiom,(
% 1.21/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.21/0.54  fof(f63,plain,(
% 1.21/0.54    r2_hidden(k4_tarski(sK1(sK0,k1_xboole_0),sK2(sK1(sK0,k1_xboole_0),k2_relat_1(k1_xboole_0),k1_xboole_0)),k1_xboole_0)),
% 1.21/0.54    inference(subsumption_resolution,[],[f61,f45])).
% 1.21/0.54  fof(f45,plain,(
% 1.21/0.54    v1_relat_1(k1_xboole_0)),
% 1.21/0.54    inference(superposition,[],[f33,f32])).
% 1.21/0.54  fof(f32,plain,(
% 1.21/0.54    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.21/0.54    inference(cnf_transformation,[],[f5])).
% 1.21/0.54  fof(f5,axiom,(
% 1.21/0.54    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 1.21/0.54  fof(f33,plain,(
% 1.21/0.54    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.21/0.54    inference(cnf_transformation,[],[f7])).
% 1.21/0.54  fof(f7,axiom,(
% 1.21/0.54    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.21/0.54  fof(f61,plain,(
% 1.21/0.54    r2_hidden(k4_tarski(sK1(sK0,k1_xboole_0),sK2(sK1(sK0,k1_xboole_0),k2_relat_1(k1_xboole_0),k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 1.21/0.54    inference(resolution,[],[f60,f53])).
% 1.21/0.54  fof(f53,plain,(
% 1.21/0.54    ( ! [X0,X1] : (~r2_hidden(X1,k1_relat_1(X0)) | r2_hidden(k4_tarski(X1,sK2(X1,k2_relat_1(X0),X0)),X0) | ~v1_relat_1(X0)) )),
% 1.21/0.54    inference(duplicate_literal_removal,[],[f52])).
% 1.21/0.54  fof(f52,plain,(
% 1.21/0.54    ( ! [X0,X1] : (~r2_hidden(X1,k1_relat_1(X0)) | r2_hidden(k4_tarski(X1,sK2(X1,k2_relat_1(X0),X0)),X0) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.21/0.54    inference(superposition,[],[f41,f35])).
% 1.21/0.54  fof(f35,plain,(
% 1.21/0.54    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.21/0.54    inference(cnf_transformation,[],[f13])).
% 1.21/0.54  fof(f13,plain,(
% 1.21/0.54    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.21/0.54    inference(ennf_transformation,[],[f4])).
% 1.21/0.54  fof(f4,axiom,(
% 1.21/0.54    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 1.21/0.54  fof(f41,plain,(
% 1.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k10_relat_1(X2,X1)) | r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2) | ~v1_relat_1(X2)) )),
% 1.21/0.54    inference(cnf_transformation,[],[f27])).
% 1.21/0.54  fof(f27,plain,(
% 1.21/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2) & r2_hidden(sK2(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f26])).
% 1.21/0.54  fof(f26,plain,(
% 1.21/0.54    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2) & r2_hidden(sK2(X0,X1,X2),k2_relat_1(X2))))),
% 1.21/0.54    introduced(choice_axiom,[])).
% 1.21/0.54  fof(f25,plain,(
% 1.21/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.21/0.54    inference(rectify,[],[f24])).
% 1.21/0.54  fof(f24,plain,(
% 1.21/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.21/0.54    inference(nnf_transformation,[],[f17])).
% 1.21/0.54  fof(f17,plain,(
% 1.21/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.21/0.54    inference(ennf_transformation,[],[f3])).
% 1.21/0.54  fof(f3,axiom,(
% 1.21/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 1.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).
% 1.21/0.54  fof(f60,plain,(
% 1.21/0.54    r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0))),
% 1.21/0.54    inference(subsumption_resolution,[],[f59,f28])).
% 1.21/0.54  fof(f28,plain,(
% 1.21/0.54    v1_relat_1(sK0)),
% 1.21/0.54    inference(cnf_transformation,[],[f19])).
% 1.21/0.54  fof(f19,plain,(
% 1.21/0.54    ~v5_funct_1(k1_xboole_0,sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 1.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f18])).
% 1.21/0.54  fof(f18,plain,(
% 1.21/0.54    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (~v5_funct_1(k1_xboole_0,sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 1.21/0.54    introduced(choice_axiom,[])).
% 1.21/0.54  fof(f12,plain,(
% 1.21/0.54    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.21/0.54    inference(flattening,[],[f11])).
% 1.21/0.54  fof(f11,plain,(
% 1.21/0.54    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.21/0.54    inference(ennf_transformation,[],[f9])).
% 1.21/0.54  fof(f9,negated_conjecture,(
% 1.21/0.54    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v5_funct_1(k1_xboole_0,X0))),
% 1.21/0.54    inference(negated_conjecture,[],[f8])).
% 1.21/0.54  fof(f8,conjecture,(
% 1.21/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v5_funct_1(k1_xboole_0,X0))),
% 1.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).
% 1.21/0.54  fof(f59,plain,(
% 1.21/0.54    r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0)) | ~v1_relat_1(sK0)),
% 1.21/0.54    inference(subsumption_resolution,[],[f58,f29])).
% 1.21/0.54  fof(f29,plain,(
% 1.21/0.54    v1_funct_1(sK0)),
% 1.21/0.54    inference(cnf_transformation,[],[f19])).
% 1.21/0.54  fof(f58,plain,(
% 1.21/0.54    r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 1.21/0.54    inference(subsumption_resolution,[],[f57,f45])).
% 1.21/0.54  fof(f57,plain,(
% 1.21/0.54    r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 1.21/0.54    inference(subsumption_resolution,[],[f56,f44])).
% 1.21/0.54  fof(f44,plain,(
% 1.21/0.54    v1_funct_1(k1_xboole_0)),
% 1.21/0.54    inference(superposition,[],[f34,f32])).
% 1.21/0.54  fof(f34,plain,(
% 1.21/0.54    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 1.21/0.54    inference(cnf_transformation,[],[f7])).
% 1.21/0.54  fof(f56,plain,(
% 1.21/0.54    r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 1.21/0.54    inference(resolution,[],[f37,f30])).
% 1.21/0.54  fof(f30,plain,(
% 1.21/0.54    ~v5_funct_1(k1_xboole_0,sK0)),
% 1.21/0.54    inference(cnf_transformation,[],[f19])).
% 1.21/0.54  fof(f37,plain,(
% 1.21/0.54    ( ! [X0,X1] : (v5_funct_1(X1,X0) | r2_hidden(sK1(X0,X1),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.21/0.54    inference(cnf_transformation,[],[f23])).
% 1.21/0.54  fof(f23,plain,(
% 1.21/0.54    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | (~r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1))) & r2_hidden(sK1(X0,X1),k1_relat_1(X1)))) & (! [X3] : (r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3)) | ~r2_hidden(X3,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f22])).
% 1.21/0.54  fof(f22,plain,(
% 1.21/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1))) => (~r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1))) & r2_hidden(sK1(X0,X1),k1_relat_1(X1))))),
% 1.21/0.54    introduced(choice_axiom,[])).
% 1.21/0.54  fof(f21,plain,(
% 1.21/0.54    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | ? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1)))) & (! [X3] : (r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3)) | ~r2_hidden(X3,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.21/0.54    inference(rectify,[],[f20])).
% 1.21/0.54  fof(f20,plain,(
% 1.21/0.54    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | ? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1)))) & (! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.21/0.54    inference(nnf_transformation,[],[f15])).
% 1.21/0.54  fof(f15,plain,(
% 1.21/0.54    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.21/0.54    inference(flattening,[],[f14])).
% 1.21/0.54  fof(f14,plain,(
% 1.21/0.54    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.21/0.54    inference(ennf_transformation,[],[f6])).
% 1.21/0.54  fof(f6,axiom,(
% 1.21/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))))))),
% 1.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).
% 1.21/0.54  % SZS output end Proof for theBenchmark
% 1.21/0.54  % (1900)------------------------------
% 1.21/0.54  % (1900)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.54  % (1900)Termination reason: Refutation
% 1.21/0.54  
% 1.21/0.54  % (1900)Memory used [KB]: 6140
% 1.21/0.54  % (1900)Time elapsed: 0.130 s
% 1.21/0.54  % (1900)------------------------------
% 1.21/0.54  % (1900)------------------------------
% 1.21/0.54  % (1879)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 1.21/0.54  % (1877)Success in time 0.175 s
%------------------------------------------------------------------------------
