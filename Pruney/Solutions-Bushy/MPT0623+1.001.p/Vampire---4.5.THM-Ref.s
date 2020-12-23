%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0623+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:19 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 967 expanded)
%              Number of leaves         :   17 ( 323 expanded)
%              Depth                    :   26
%              Number of atoms          :  336 (5247 expanded)
%              Number of equality atoms :   89 (1844 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f837,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f84,f341,f836])).

% (801)Refutation not found, incomplete strategy% (801)------------------------------
% (801)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f836,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_contradiction_clause,[],[f835])).

fof(f835,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f834,f345])).

fof(f345,plain,
    ( ! [X0] : ~ r2_hidden(o_1_0_funct_1(X0),k1_xboole_0)
    | ~ spl7_1 ),
    inference(backward_demodulation,[],[f305,f72])).

fof(f72,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl7_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f305,plain,(
    ! [X0] : ~ r2_hidden(o_1_0_funct_1(X0),sK0) ),
    inference(backward_demodulation,[],[f102,f279])).

fof(f279,plain,(
    ! [X0] : o_1_0_funct_1(X0) = sK5(k2_relat_1(sK6(X0,sK1)),sK0) ),
    inference(backward_demodulation,[],[f118,f178])).

fof(f178,plain,(
    ! [X0,X1] : o_1_0_funct_1(X0) = k1_funct_1(sK6(X0,sK1),sK4(sK6(X1,sK1),sK5(k2_relat_1(sK6(X1,sK1)),sK0))) ),
    inference(unit_resulting_resolution,[],[f128,f65])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( o_1_0_funct_1(X0) = k1_funct_1(sK6(X0,X1),X3)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( o_1_0_funct_1(X0) = k1_funct_1(sK6(X0,X1),X3)
          | ~ r2_hidden(X3,X1) )
      & k1_relat_1(sK6(X0,X1)) = X1
      & v1_funct_1(sK6(X0,X1))
      & v1_relat_1(sK6(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f27,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( o_1_0_funct_1(X0) = k1_funct_1(X2,X3)
              | ~ r2_hidden(X3,X1) )
          & k1_relat_1(X2) = X1
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( o_1_0_funct_1(X0) = k1_funct_1(sK6(X0,X1),X3)
            | ~ r2_hidden(X3,X1) )
        & k1_relat_1(sK6(X0,X1)) = X1
        & v1_funct_1(sK6(X0,X1))
        & v1_relat_1(sK6(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( o_1_0_funct_1(X0) = k1_funct_1(X2,X3)
          | ~ r2_hidden(X3,X1) )
      & k1_relat_1(X2) = X1
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => o_1_0_funct_1(X0) = k1_funct_1(X2,X3) )
      & k1_relat_1(X2) = X1
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e1_27_1__funct_1)).

fof(f128,plain,(
    ! [X0] : r2_hidden(sK4(sK6(X0,sK1),sK5(k2_relat_1(sK6(X0,sK1)),sK0)),sK1) ),
    inference(forward_demodulation,[],[f117,f64])).

fof(f64,plain,(
    ! [X0,X1] : k1_relat_1(sK6(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f41])).

fof(f117,plain,(
    ! [X0] : r2_hidden(sK4(sK6(X0,sK1),sK5(k2_relat_1(sK6(X0,sK1)),sK0)),k1_relat_1(sK6(X0,sK1))) ),
    inference(unit_resulting_resolution,[],[f62,f63,f101,f69])).

fof(f69,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f52])).

% (817)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f52,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK2(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK2(X0,X1),X1) )
              & ( ( sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1))
                  & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK2(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK4(X0,X5)) = X5
                    & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f31,f34,f33,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK2(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK2(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK2(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X5)) = X5
        & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f23])).

% (820)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (801)Termination reason: Refutation not found, incomplete strategy

% (801)Memory used [KB]: 10618
% (801)Time elapsed: 0.116 s
% (801)------------------------------
% (801)------------------------------
fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(f101,plain,(
    ! [X0] : r2_hidden(sK5(k2_relat_1(sK6(X0,sK1)),sK0),k2_relat_1(sK6(X0,sK1))) ),
    inference(unit_resulting_resolution,[],[f92,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f37,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f92,plain,(
    ! [X0] : ~ r1_tarski(k2_relat_1(sK6(X0,sK1)),sK0) ),
    inference(unit_resulting_resolution,[],[f62,f63,f64,f43])).

fof(f43,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_relat_1(X2),sK0)
      | k1_relat_1(X2) != sK1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relat_1(X2),sK0)
        | k1_relat_1(X2) != sK1
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f28])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( ~ r1_tarski(k2_relat_1(X2),X0)
            | k1_relat_1(X2) != X1
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 != X0 ) )
   => ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),sK0)
          | k1_relat_1(X2) != sK1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = sK1
        | k1_xboole_0 != sK0 ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

% (804)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f63,plain,(
    ! [X0,X1] : v1_funct_1(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f62,plain,(
    ! [X0,X1] : v1_relat_1(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f118,plain,(
    ! [X0] : sK5(k2_relat_1(sK6(X0,sK1)),sK0) = k1_funct_1(sK6(X0,sK1),sK4(sK6(X0,sK1),sK5(k2_relat_1(sK6(X0,sK1)),sK0))) ),
    inference(unit_resulting_resolution,[],[f62,f63,f101,f68])).

fof(f68,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f102,plain,(
    ! [X0] : ~ r2_hidden(sK5(k2_relat_1(sK6(X0,sK1)),sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f92,f61])).

% (818)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f834,plain,
    ( ! [X39] : r2_hidden(o_1_0_funct_1(X39),k1_xboole_0)
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f833,f64])).

fof(f833,plain,
    ( ! [X39,X38] : r2_hidden(o_1_0_funct_1(X39),k1_relat_1(sK6(X38,k1_xboole_0)))
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f832,f62])).

fof(f832,plain,
    ( ! [X39,X38] :
        ( r2_hidden(o_1_0_funct_1(X39),k1_relat_1(sK6(X38,k1_xboole_0)))
        | ~ v1_relat_1(sK6(X38,k1_xboole_0)) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f831,f63])).

fof(f831,plain,
    ( ! [X39,X38] :
        ( r2_hidden(o_1_0_funct_1(X39),k1_relat_1(sK6(X38,k1_xboole_0)))
        | ~ v1_funct_1(sK6(X38,k1_xboole_0))
        | ~ v1_relat_1(sK6(X38,k1_xboole_0)) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f822,f351])).

fof(f351,plain,
    ( ! [X3] : r2_hidden(o_1_0_funct_1(X3),k2_relat_1(sK6(X3,k1_xboole_0)))
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f290,f77])).

fof(f77,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f290,plain,(
    ! [X3] : r2_hidden(o_1_0_funct_1(X3),k2_relat_1(sK6(X3,sK1))) ),
    inference(subsumption_resolution,[],[f289,f128])).

fof(f289,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(sK4(sK6(X4,sK1),sK5(k2_relat_1(sK6(X4,sK1)),sK0)),sK1)
      | r2_hidden(o_1_0_funct_1(X3),k2_relat_1(sK6(X3,sK1))) ) ),
    inference(forward_demodulation,[],[f288,f64])).

fof(f288,plain,(
    ! [X4,X3] :
      ( r2_hidden(o_1_0_funct_1(X3),k2_relat_1(sK6(X3,sK1)))
      | ~ r2_hidden(sK4(sK6(X4,sK1),sK5(k2_relat_1(sK6(X4,sK1)),sK0)),k1_relat_1(sK6(X3,sK1))) ) ),
    inference(subsumption_resolution,[],[f287,f62])).

fof(f287,plain,(
    ! [X4,X3] :
      ( r2_hidden(o_1_0_funct_1(X3),k2_relat_1(sK6(X3,sK1)))
      | ~ r2_hidden(sK4(sK6(X4,sK1),sK5(k2_relat_1(sK6(X4,sK1)),sK0)),k1_relat_1(sK6(X3,sK1)))
      | ~ v1_relat_1(sK6(X3,sK1)) ) ),
    inference(subsumption_resolution,[],[f285,f63])).

fof(f285,plain,(
    ! [X4,X3] :
      ( r2_hidden(o_1_0_funct_1(X3),k2_relat_1(sK6(X3,sK1)))
      | ~ r2_hidden(sK4(sK6(X4,sK1),sK5(k2_relat_1(sK6(X4,sK1)),sK0)),k1_relat_1(sK6(X3,sK1)))
      | ~ v1_funct_1(sK6(X3,sK1))
      | ~ v1_relat_1(sK6(X3,sK1)) ) ),
    inference(superposition,[],[f67,f178])).

fof(f67,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f822,plain,
    ( ! [X39,X38] :
        ( r2_hidden(o_1_0_funct_1(X39),k1_relat_1(sK6(X38,k1_xboole_0)))
        | ~ r2_hidden(o_1_0_funct_1(X38),k2_relat_1(sK6(X38,k1_xboole_0)))
        | ~ v1_funct_1(sK6(X38,k1_xboole_0))
        | ~ v1_relat_1(sK6(X38,k1_xboole_0)) )
    | ~ spl7_2 ),
    inference(superposition,[],[f69,f776])).

fof(f776,plain,
    ( ! [X2,X0] : o_1_0_funct_1(X0) = sK4(sK6(X2,k1_xboole_0),o_1_0_funct_1(X2))
    | ~ spl7_2 ),
    inference(superposition,[],[f544,f437])).

fof(f437,plain,
    ( ! [X2,X0,X1] : sK4(sK6(X0,k1_xboole_0),o_1_0_funct_1(X0)) = k1_funct_1(sK6(X1,X2),sK4(sK6(X1,X2),sK4(sK6(X0,k1_xboole_0),o_1_0_funct_1(X0))))
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f62,f63,f404,f68])).

fof(f404,plain,
    ( ! [X0,X1] : r2_hidden(sK4(sK6(X0,k1_xboole_0),o_1_0_funct_1(X0)),X1)
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f45,f402,f59])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f402,plain,
    ( ! [X0] : r2_hidden(sK4(sK6(X0,k1_xboole_0),o_1_0_funct_1(X0)),k1_xboole_0)
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f311,f77])).

fof(f311,plain,(
    ! [X0] : r2_hidden(sK4(sK6(X0,sK1),o_1_0_funct_1(X0)),sK1) ),
    inference(backward_demodulation,[],[f128,f279])).

fof(f45,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f544,plain,
    ( ! [X2,X0,X3,X1] : o_1_0_funct_1(X0) = k1_funct_1(sK6(X0,X1),sK4(sK6(X2,X1),sK4(sK6(X3,k1_xboole_0),o_1_0_funct_1(X3))))
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f447,f65])).

fof(f447,plain,
    ( ! [X2,X0,X1] : r2_hidden(sK4(sK6(X0,X1),sK4(sK6(X2,k1_xboole_0),o_1_0_funct_1(X2))),X1)
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f436,f64])).

fof(f436,plain,
    ( ! [X2,X0,X1] : r2_hidden(sK4(sK6(X0,X1),sK4(sK6(X2,k1_xboole_0),o_1_0_funct_1(X2))),k1_relat_1(sK6(X0,X1)))
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f62,f63,f404,f69])).

fof(f341,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f331,f81])).

fof(f81,plain,
    ( spl7_3
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f331,plain,(
    v1_xboole_0(sK0) ),
    inference(unit_resulting_resolution,[],[f46,f305,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f46,plain,(
    ! [X0] : m1_subset_1(o_1_0_funct_1(X0),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(o_1_0_funct_1(X0),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_1_0_funct_1)).

fof(f84,plain,
    ( ~ spl7_3
    | spl7_1 ),
    inference(avatar_split_clause,[],[f79,f71,f81])).

fof(f79,plain,
    ( ~ v1_xboole_0(sK0)
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f73,f49])).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f73,plain,
    ( k1_xboole_0 != sK0
    | spl7_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f78,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f42,f75,f71])).

fof(f42,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f29])).

%------------------------------------------------------------------------------
