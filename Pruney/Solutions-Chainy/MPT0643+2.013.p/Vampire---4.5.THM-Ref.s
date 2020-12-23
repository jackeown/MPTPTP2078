%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:41 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 384 expanded)
%              Number of leaves         :   10 ( 118 expanded)
%              Depth                    :   18
%              Number of atoms          :  405 (3578 expanded)
%              Number of equality atoms :  150 (1505 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f404,plain,(
    $false ),
    inference(subsumption_resolution,[],[f403,f351])).

% (4951)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
fof(f351,plain,(
    k1_funct_1(sK1,sK5(sK0,sK2)) = k1_funct_1(sK1,k1_funct_1(sK2,sK5(sK0,sK2))) ),
    inference(forward_demodulation,[],[f350,f42])).

fof(f42,plain,(
    sK1 = k5_relat_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( k6_relat_1(sK0) != sK2
    & sK1 = k5_relat_1(sK2,sK1)
    & v2_funct_1(sK1)
    & r1_tarski(k2_relat_1(sK2),sK0)
    & sK0 = k1_relat_1(sK2)
    & sK0 = k1_relat_1(sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f21,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k6_relat_1(X0) != X2
            & k5_relat_1(X2,X1) = X1
            & v2_funct_1(X1)
            & r1_tarski(k2_relat_1(X2),X0)
            & k1_relat_1(X2) = X0
            & k1_relat_1(X1) = X0
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( k6_relat_1(sK0) != X2
          & sK1 = k5_relat_1(X2,sK1)
          & v2_funct_1(sK1)
          & r1_tarski(k2_relat_1(X2),sK0)
          & k1_relat_1(X2) = sK0
          & sK0 = k1_relat_1(sK1)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X2] :
        ( k6_relat_1(sK0) != X2
        & sK1 = k5_relat_1(X2,sK1)
        & v2_funct_1(sK1)
        & r1_tarski(k2_relat_1(X2),sK0)
        & k1_relat_1(X2) = sK0
        & sK0 = k1_relat_1(sK1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k6_relat_1(sK0) != sK2
      & sK1 = k5_relat_1(sK2,sK1)
      & v2_funct_1(sK1)
      & r1_tarski(k2_relat_1(sK2),sK0)
      & sK0 = k1_relat_1(sK2)
      & sK0 = k1_relat_1(sK1)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k6_relat_1(X0) != X2
          & k5_relat_1(X2,X1) = X1
          & v2_funct_1(X1)
          & r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X0
          & k1_relat_1(X1) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k6_relat_1(X0) != X2
          & k5_relat_1(X2,X1) = X1
          & v2_funct_1(X1)
          & r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X0
          & k1_relat_1(X1) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( ( k5_relat_1(X2,X1) = X1
                & v2_funct_1(X1)
                & r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X0
                & k1_relat_1(X1) = X0 )
             => k6_relat_1(X0) = X2 ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( ( k5_relat_1(X2,X1) = X1
              & v2_funct_1(X1)
              & r1_tarski(k2_relat_1(X2),X0)
              & k1_relat_1(X2) = X0
              & k1_relat_1(X1) = X0 )
           => k6_relat_1(X0) = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_funct_1)).

fof(f350,plain,(
    k1_funct_1(k5_relat_1(sK2,sK1),sK5(sK0,sK2)) = k1_funct_1(sK1,k1_funct_1(sK2,sK5(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f348,f34])).

fof(f34,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f348,plain,
    ( k1_funct_1(k5_relat_1(sK2,sK1),sK5(sK0,sK2)) = k1_funct_1(sK1,k1_funct_1(sK2,sK5(sK0,sK2)))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f167,f35])).

fof(f35,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f167,plain,(
    ! [X3] :
      ( ~ v1_funct_1(X3)
      | k1_funct_1(k5_relat_1(sK2,X3),sK5(sK0,sK2)) = k1_funct_1(X3,k1_funct_1(sK2,sK5(sK0,sK2)))
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f137,f121])).

fof(f121,plain,(
    r2_hidden(sK5(sK0,sK2),sK0) ),
    inference(subsumption_resolution,[],[f120,f43])).

fof(f43,plain,(
    k6_relat_1(sK0) != sK2 ),
    inference(cnf_transformation,[],[f22])).

fof(f120,plain,
    ( k6_relat_1(sK0) = sK2
    | r2_hidden(sK5(sK0,sK2),sK0) ),
    inference(forward_demodulation,[],[f119,f39])).

fof(f39,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f119,plain,
    ( r2_hidden(sK5(sK0,sK2),sK0)
    | sK2 = k6_relat_1(k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f118,f39])).

fof(f118,plain,
    ( r2_hidden(sK5(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
    | sK2 = k6_relat_1(k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f105,f36])).

fof(f36,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f105,plain,
    ( r2_hidden(sK5(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
    | sK2 = k6_relat_1(k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f59,f37])).

fof(f37,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f59,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | r2_hidden(sK5(k1_relat_1(X1),X1),k1_relat_1(X1))
      | k6_relat_1(k1_relat_1(X1)) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | r2_hidden(sK5(X0,X1),X0)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( sK5(X0,X1) != k1_funct_1(X1,sK5(X0,X1))
            & r2_hidden(sK5(X0,X1),X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( sK5(X0,X1) != k1_funct_1(X1,sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

fof(f137,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,sK0)
      | k1_funct_1(k5_relat_1(sK2,X3),X2) = k1_funct_1(X3,k1_funct_1(sK2,X2))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(subsumption_resolution,[],[f136,f36])).

fof(f136,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,sK0)
      | k1_funct_1(k5_relat_1(sK2,X3),X2) = k1_funct_1(X3,k1_funct_1(sK2,X2))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f133,f37])).

fof(f133,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,sK0)
      | k1_funct_1(k5_relat_1(sK2,X3),X2) = k1_funct_1(X3,k1_funct_1(sK2,X2))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f54,f39])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

fof(f403,plain,(
    k1_funct_1(sK1,sK5(sK0,sK2)) != k1_funct_1(sK1,k1_funct_1(sK2,sK5(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f384,f131])).

fof(f131,plain,(
    sK5(sK0,sK2) != k1_funct_1(sK2,sK5(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f130,f43])).

fof(f130,plain,
    ( k6_relat_1(sK0) = sK2
    | sK5(sK0,sK2) != k1_funct_1(sK2,sK5(sK0,sK2)) ),
    inference(forward_demodulation,[],[f129,f39])).

fof(f129,plain,
    ( sK5(sK0,sK2) != k1_funct_1(sK2,sK5(sK0,sK2))
    | sK2 = k6_relat_1(k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f128,f39])).

fof(f128,plain,
    ( sK5(k1_relat_1(sK2),sK2) != k1_funct_1(sK2,sK5(k1_relat_1(sK2),sK2))
    | sK2 = k6_relat_1(k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f123,f36])).

fof(f123,plain,
    ( sK5(k1_relat_1(sK2),sK2) != k1_funct_1(sK2,sK5(k1_relat_1(sK2),sK2))
    | sK2 = k6_relat_1(k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f58,f37])).

fof(f58,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | sK5(k1_relat_1(X1),X1) != k1_funct_1(X1,sK5(k1_relat_1(X1),X1))
      | k6_relat_1(k1_relat_1(X1)) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | sK5(X0,X1) != k1_funct_1(X1,sK5(X0,X1))
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f384,plain,
    ( sK5(sK0,sK2) = k1_funct_1(sK2,sK5(sK0,sK2))
    | k1_funct_1(sK1,sK5(sK0,sK2)) != k1_funct_1(sK1,k1_funct_1(sK2,sK5(sK0,sK2))) ),
    inference(resolution,[],[f172,f159])).

fof(f159,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK0)
      | sK5(sK0,sK2) = X3
      | k1_funct_1(sK1,sK5(sK0,sK2)) != k1_funct_1(sK1,X3) ) ),
    inference(resolution,[],[f142,f121])).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1)
      | X0 = X1
      | ~ r2_hidden(X1,sK0) ) ),
    inference(subsumption_resolution,[],[f141,f34])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1)
      | X0 = X1
      | ~ r2_hidden(X1,sK0)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f140,f35])).

fof(f140,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1)
      | X0 = X1
      | ~ r2_hidden(X1,sK0)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f138,f41])).

fof(f41,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f138,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1)
      | X0 = X1
      | ~ r2_hidden(X1,sK0)
      | ~ v2_funct_1(sK1)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f44,f38])).

fof(f38,plain,(
    sK0 = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f44,plain,(
    ! [X4,X0,X3] :
      ( ~ r2_hidden(X4,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | X3 = X4
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK3(X0) != sK4(X0)
            & k1_funct_1(X0,sK3(X0)) = k1_funct_1(X0,sK4(X0))
            & r2_hidden(sK4(X0),k1_relat_1(X0))
            & r2_hidden(sK3(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f24,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK3(X0) != sK4(X0)
        & k1_funct_1(X0,sK3(X0)) = k1_funct_1(X0,sK4(X0))
        & r2_hidden(sK4(X0),k1_relat_1(X0))
        & r2_hidden(sK3(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( X1 = X2
              | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0))
              | ~ r2_hidden(X1,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

fof(f172,plain,(
    r2_hidden(k1_funct_1(sK2,sK5(sK0,sK2)),sK0) ),
    inference(resolution,[],[f150,f121])).

fof(f150,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(k1_funct_1(sK2,X0),sK0) ) ),
    inference(forward_demodulation,[],[f149,f39])).

fof(f149,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK2))
      | r2_hidden(k1_funct_1(sK2,X0),sK0) ) ),
    inference(subsumption_resolution,[],[f148,f36])).

fof(f148,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK2))
      | r2_hidden(k1_funct_1(sK2,X0),sK0)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f146,f37])).

fof(f146,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK2))
      | r2_hidden(k1_funct_1(sK2,X0),sK0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f56,f85])).

fof(f85,plain,(
    sK2 = k5_relat_1(sK2,k6_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f84,f36])).

fof(f84,plain,
    ( sK2 = k5_relat_1(sK2,k6_relat_1(sK0))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f49,f40])).

fof(f40,plain,(
    r1_tarski(k2_relat_1(sK2),sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      | r2_hidden(k1_funct_1(X2,X0),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
          | ~ r2_hidden(k1_funct_1(X2,X0),X1)
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
          | ~ r2_hidden(k1_funct_1(X2,X0),X1)
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.11/0.33  % Computer   : n008.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 18:11:00 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.20/0.44  % (4943)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.45  % (4961)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.45  % (4948)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.46  % (4948)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f404,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(subsumption_resolution,[],[f403,f351])).
% 0.20/0.47  % (4951)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.47  fof(f351,plain,(
% 0.20/0.47    k1_funct_1(sK1,sK5(sK0,sK2)) = k1_funct_1(sK1,k1_funct_1(sK2,sK5(sK0,sK2)))),
% 0.20/0.47    inference(forward_demodulation,[],[f350,f42])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    sK1 = k5_relat_1(sK2,sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    (k6_relat_1(sK0) != sK2 & sK1 = k5_relat_1(sK2,sK1) & v2_funct_1(sK1) & r1_tarski(k2_relat_1(sK2),sK0) & sK0 = k1_relat_1(sK2) & sK0 = k1_relat_1(sK1) & v1_funct_1(sK2) & v1_relat_1(sK2)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f21,f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ? [X0,X1] : (? [X2] : (k6_relat_1(X0) != X2 & k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (k6_relat_1(sK0) != X2 & sK1 = k5_relat_1(X2,sK1) & v2_funct_1(sK1) & r1_tarski(k2_relat_1(X2),sK0) & k1_relat_1(X2) = sK0 & sK0 = k1_relat_1(sK1) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ? [X2] : (k6_relat_1(sK0) != X2 & sK1 = k5_relat_1(X2,sK1) & v2_funct_1(sK1) & r1_tarski(k2_relat_1(X2),sK0) & k1_relat_1(X2) = sK0 & sK0 = k1_relat_1(sK1) & v1_funct_1(X2) & v1_relat_1(X2)) => (k6_relat_1(sK0) != sK2 & sK1 = k5_relat_1(sK2,sK1) & v2_funct_1(sK1) & r1_tarski(k2_relat_1(sK2),sK0) & sK0 = k1_relat_1(sK2) & sK0 = k1_relat_1(sK1) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ? [X0,X1] : (? [X2] : (k6_relat_1(X0) != X2 & k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.47    inference(flattening,[],[f8])).
% 0.20/0.47  fof(f8,plain,(
% 0.20/0.47    ? [X0,X1] : (? [X2] : ((k6_relat_1(X0) != X2 & (k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0)) & (v1_funct_1(X2) & v1_relat_1(X2))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => k6_relat_1(X0) = X2)))),
% 0.20/0.47    inference(negated_conjecture,[],[f6])).
% 0.20/0.47  fof(f6,conjecture,(
% 0.20/0.47    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => k6_relat_1(X0) = X2)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_funct_1)).
% 0.20/0.47  fof(f350,plain,(
% 0.20/0.47    k1_funct_1(k5_relat_1(sK2,sK1),sK5(sK0,sK2)) = k1_funct_1(sK1,k1_funct_1(sK2,sK5(sK0,sK2)))),
% 0.20/0.47    inference(subsumption_resolution,[],[f348,f34])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    v1_relat_1(sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f22])).
% 0.20/0.47  fof(f348,plain,(
% 0.20/0.47    k1_funct_1(k5_relat_1(sK2,sK1),sK5(sK0,sK2)) = k1_funct_1(sK1,k1_funct_1(sK2,sK5(sK0,sK2))) | ~v1_relat_1(sK1)),
% 0.20/0.47    inference(resolution,[],[f167,f35])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    v1_funct_1(sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f22])).
% 0.20/0.47  fof(f167,plain,(
% 0.20/0.47    ( ! [X3] : (~v1_funct_1(X3) | k1_funct_1(k5_relat_1(sK2,X3),sK5(sK0,sK2)) = k1_funct_1(X3,k1_funct_1(sK2,sK5(sK0,sK2))) | ~v1_relat_1(X3)) )),
% 0.20/0.47    inference(resolution,[],[f137,f121])).
% 0.20/0.47  fof(f121,plain,(
% 0.20/0.47    r2_hidden(sK5(sK0,sK2),sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f120,f43])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    k6_relat_1(sK0) != sK2),
% 0.20/0.47    inference(cnf_transformation,[],[f22])).
% 0.20/0.47  fof(f120,plain,(
% 0.20/0.47    k6_relat_1(sK0) = sK2 | r2_hidden(sK5(sK0,sK2),sK0)),
% 0.20/0.47    inference(forward_demodulation,[],[f119,f39])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    sK0 = k1_relat_1(sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f22])).
% 0.20/0.47  fof(f119,plain,(
% 0.20/0.47    r2_hidden(sK5(sK0,sK2),sK0) | sK2 = k6_relat_1(k1_relat_1(sK2))),
% 0.20/0.47    inference(forward_demodulation,[],[f118,f39])).
% 0.20/0.47  fof(f118,plain,(
% 0.20/0.47    r2_hidden(sK5(k1_relat_1(sK2),sK2),k1_relat_1(sK2)) | sK2 = k6_relat_1(k1_relat_1(sK2))),
% 0.20/0.47    inference(subsumption_resolution,[],[f105,f36])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    v1_relat_1(sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f22])).
% 0.20/0.47  fof(f105,plain,(
% 0.20/0.47    r2_hidden(sK5(k1_relat_1(sK2),sK2),k1_relat_1(sK2)) | sK2 = k6_relat_1(k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.20/0.47    inference(resolution,[],[f59,f37])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    v1_funct_1(sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f22])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    ( ! [X1] : (~v1_funct_1(X1) | r2_hidden(sK5(k1_relat_1(X1),X1),k1_relat_1(X1)) | k6_relat_1(k1_relat_1(X1)) = X1 | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(equality_resolution,[],[f52])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | r2_hidden(sK5(X0,X1),X0) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f31])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (sK5(X0,X1) != k1_funct_1(X1,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ! [X1,X0] : (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) => (sK5(X0,X1) != k1_funct_1(X1,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),X0)))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(rectify,[],[f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(flattening,[],[f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0)) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(nnf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(flattening,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).
% 0.20/0.47  fof(f137,plain,(
% 0.20/0.47    ( ! [X2,X3] : (~r2_hidden(X2,sK0) | k1_funct_1(k5_relat_1(sK2,X3),X2) = k1_funct_1(X3,k1_funct_1(sK2,X2)) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f136,f36])).
% 0.20/0.47  fof(f136,plain,(
% 0.20/0.47    ( ! [X2,X3] : (~r2_hidden(X2,sK0) | k1_funct_1(k5_relat_1(sK2,X3),X2) = k1_funct_1(X3,k1_funct_1(sK2,X2)) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_relat_1(sK2)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f133,f37])).
% 0.20/0.47  fof(f133,plain,(
% 0.20/0.47    ( ! [X2,X3] : (~r2_hidden(X2,sK0) | k1_funct_1(k5_relat_1(sK2,X3),X2) = k1_funct_1(X3,k1_funct_1(sK2,X2)) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.20/0.47    inference(superposition,[],[f54,f39])).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(X1)) | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(flattening,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).
% 0.20/0.47  fof(f403,plain,(
% 0.20/0.47    k1_funct_1(sK1,sK5(sK0,sK2)) != k1_funct_1(sK1,k1_funct_1(sK2,sK5(sK0,sK2)))),
% 0.20/0.47    inference(subsumption_resolution,[],[f384,f131])).
% 0.20/0.47  fof(f131,plain,(
% 0.20/0.47    sK5(sK0,sK2) != k1_funct_1(sK2,sK5(sK0,sK2))),
% 0.20/0.47    inference(subsumption_resolution,[],[f130,f43])).
% 0.20/0.47  fof(f130,plain,(
% 0.20/0.47    k6_relat_1(sK0) = sK2 | sK5(sK0,sK2) != k1_funct_1(sK2,sK5(sK0,sK2))),
% 0.20/0.47    inference(forward_demodulation,[],[f129,f39])).
% 0.20/0.47  fof(f129,plain,(
% 0.20/0.47    sK5(sK0,sK2) != k1_funct_1(sK2,sK5(sK0,sK2)) | sK2 = k6_relat_1(k1_relat_1(sK2))),
% 0.20/0.47    inference(forward_demodulation,[],[f128,f39])).
% 0.20/0.47  fof(f128,plain,(
% 0.20/0.47    sK5(k1_relat_1(sK2),sK2) != k1_funct_1(sK2,sK5(k1_relat_1(sK2),sK2)) | sK2 = k6_relat_1(k1_relat_1(sK2))),
% 0.20/0.47    inference(subsumption_resolution,[],[f123,f36])).
% 0.20/0.47  fof(f123,plain,(
% 0.20/0.47    sK5(k1_relat_1(sK2),sK2) != k1_funct_1(sK2,sK5(k1_relat_1(sK2),sK2)) | sK2 = k6_relat_1(k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.20/0.47    inference(resolution,[],[f58,f37])).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    ( ! [X1] : (~v1_funct_1(X1) | sK5(k1_relat_1(X1),X1) != k1_funct_1(X1,sK5(k1_relat_1(X1),X1)) | k6_relat_1(k1_relat_1(X1)) = X1 | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(equality_resolution,[],[f53])).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | sK5(X0,X1) != k1_funct_1(X1,sK5(X0,X1)) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f31])).
% 0.20/0.47  fof(f384,plain,(
% 0.20/0.47    sK5(sK0,sK2) = k1_funct_1(sK2,sK5(sK0,sK2)) | k1_funct_1(sK1,sK5(sK0,sK2)) != k1_funct_1(sK1,k1_funct_1(sK2,sK5(sK0,sK2)))),
% 0.20/0.47    inference(resolution,[],[f172,f159])).
% 0.20/0.47  fof(f159,plain,(
% 0.20/0.47    ( ! [X3] : (~r2_hidden(X3,sK0) | sK5(sK0,sK2) = X3 | k1_funct_1(sK1,sK5(sK0,sK2)) != k1_funct_1(sK1,X3)) )),
% 0.20/0.47    inference(resolution,[],[f142,f121])).
% 0.20/0.47  fof(f142,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1) | X0 = X1 | ~r2_hidden(X1,sK0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f141,f34])).
% 0.20/0.47  fof(f141,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1) | X0 = X1 | ~r2_hidden(X1,sK0) | ~v1_relat_1(sK1)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f140,f35])).
% 0.20/0.47  fof(f140,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1) | X0 = X1 | ~r2_hidden(X1,sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f138,f41])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    v2_funct_1(sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f22])).
% 0.20/0.47  fof(f138,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1) | X0 = X1 | ~r2_hidden(X1,sK0) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 0.20/0.47    inference(superposition,[],[f44,f38])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    sK0 = k1_relat_1(sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f22])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    ( ! [X4,X0,X3] : (~r2_hidden(X4,k1_relat_1(X0)) | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | X3 = X4 | ~r2_hidden(X3,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ! [X0] : (((v2_funct_1(X0) | (sK3(X0) != sK4(X0) & k1_funct_1(X0,sK3(X0)) = k1_funct_1(X0,sK4(X0)) & r2_hidden(sK4(X0),k1_relat_1(X0)) & r2_hidden(sK3(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f24,f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK3(X0) != sK4(X0) & k1_funct_1(X0,sK3(X0)) = k1_funct_1(X0,sK4(X0)) & r2_hidden(sK4(X0),k1_relat_1(X0)) & r2_hidden(sK3(X0),k1_relat_1(X0))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(rectify,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(nnf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(flattening,[],[f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).
% 0.20/0.47  fof(f172,plain,(
% 0.20/0.47    r2_hidden(k1_funct_1(sK2,sK5(sK0,sK2)),sK0)),
% 0.20/0.47    inference(resolution,[],[f150,f121])).
% 0.20/0.47  fof(f150,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK2,X0),sK0)) )),
% 0.20/0.47    inference(forward_demodulation,[],[f149,f39])).
% 0.20/0.47  fof(f149,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | r2_hidden(k1_funct_1(sK2,X0),sK0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f148,f36])).
% 0.20/0.47  fof(f148,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | r2_hidden(k1_funct_1(sK2,X0),sK0) | ~v1_relat_1(sK2)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f146,f37])).
% 0.20/0.47  fof(f146,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | r2_hidden(k1_funct_1(sK2,X0),sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.20/0.47    inference(superposition,[],[f56,f85])).
% 0.20/0.47  fof(f85,plain,(
% 0.20/0.47    sK2 = k5_relat_1(sK2,k6_relat_1(sK0))),
% 0.20/0.47    inference(subsumption_resolution,[],[f84,f36])).
% 0.20/0.47  fof(f84,plain,(
% 0.20/0.47    sK2 = k5_relat_1(sK2,k6_relat_1(sK0)) | ~v1_relat_1(sK2)),
% 0.20/0.47    inference(resolution,[],[f49,f40])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    r1_tarski(k2_relat_1(sK2),sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f22])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(flattening,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) | r2_hidden(k1_funct_1(X2,X0),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) | ~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.47    inference(flattening,[],[f32])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) | (~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2)))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.47    inference(nnf_transformation,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.47    inference(flattening,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_1)).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (4948)------------------------------
% 0.20/0.47  % (4948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (4948)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (4948)Memory used [KB]: 10746
% 0.20/0.47  % (4948)Time elapsed: 0.015 s
% 0.20/0.47  % (4948)------------------------------
% 0.20/0.47  % (4948)------------------------------
% 0.20/0.47  % (4937)Success in time 0.129 s
%------------------------------------------------------------------------------
