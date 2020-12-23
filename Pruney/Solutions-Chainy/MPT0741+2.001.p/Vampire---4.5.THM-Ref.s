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
% DateTime   : Thu Dec  3 12:55:19 EST 2020

% Result     : Theorem 1.55s
% Output     : Refutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 503 expanded)
%              Number of leaves         :   14 ( 134 expanded)
%              Depth                    :   13
%              Number of atoms          :  267 (2208 expanded)
%              Number of equality atoms :   23 ( 122 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f239,plain,(
    $false ),
    inference(subsumption_resolution,[],[f226,f168])).

fof(f168,plain,(
    ~ r2_hidden(sK1(sK0),k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0)))) ),
    inference(unit_resulting_resolution,[],[f90,f91,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | r2_hidden(X0,X1)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f64,f45])).

fof(f45,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f64,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f91,plain,(
    sK2(sK0) != sK1(sK0) ),
    inference(unit_resulting_resolution,[],[f84,f56])).

fof(f56,plain,(
    ! [X0] :
      ( sK1(X0) != sK2(X0)
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        | ( ~ r2_hidden(sK2(X0),sK1(X0))
          & sK1(X0) != sK2(X0)
          & ~ r2_hidden(sK1(X0),sK2(X0))
          & r2_hidden(sK2(X0),X0)
          & r2_hidden(sK1(X0),X0) ) )
      & ( ! [X3,X4] :
            ( r2_hidden(X4,X3)
            | X3 = X4
            | r2_hidden(X3,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) )
        | ~ v2_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f32,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r2_hidden(X2,X1)
          & X1 != X2
          & ~ r2_hidden(X1,X2)
          & r2_hidden(X2,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r2_hidden(sK2(X0),sK1(X0))
        & sK1(X0) != sK2(X0)
        & ~ r2_hidden(sK1(X0),sK2(X0))
        & r2_hidden(sK2(X0),X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        | ? [X1,X2] :
            ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X3,X4] :
            ( r2_hidden(X4,X3)
            | X3 = X4
            | r2_hidden(X3,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) )
        | ~ v2_ordinal1(X0) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        | ? [X1,X2] :
            ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1,X2] :
            ( r2_hidden(X2,X1)
            | X1 = X2
            | r2_hidden(X1,X2)
            | ~ r2_hidden(X2,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v2_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
    <=> ! [X1,X2] :
          ( r2_hidden(X2,X1)
          | X1 = X2
          | r2_hidden(X1,X2)
          | ~ r2_hidden(X2,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v2_ordinal1(X0)
    <=> ! [X1,X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_ordinal1)).

fof(f84,plain,(
    ~ v2_ordinal1(sK0) ),
    inference(unit_resulting_resolution,[],[f44,f83,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v2_ordinal1(X0)
      | v3_ordinal1(X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
      | ~ v2_ordinal1(X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
      | ~ v2_ordinal1(X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        & v1_ordinal1(X0) )
     => v3_ordinal1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_ordinal1)).

fof(f83,plain,(
    v1_ordinal1(sK0) ),
    inference(subsumption_resolution,[],[f82,f59])).

fof(f59,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ( ~ r1_tarski(sK3(X0),X0)
          & r2_hidden(sK3(X0),X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r1_tarski(sK3(X0),X0)
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( r1_tarski(X1,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

fof(f82,plain,
    ( ~ r2_hidden(sK3(sK0),sK0)
    | v1_ordinal1(sK0) ),
    inference(resolution,[],[f43,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK3(X0),X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f43,plain,(
    ! [X1] :
      ( r1_tarski(X1,sK0)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ v3_ordinal1(sK0)
    & ! [X1] :
        ( ( r1_tarski(X1,sK0)
          & v3_ordinal1(X1) )
        | ~ r2_hidden(X1,sK0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ~ v3_ordinal1(X0)
        & ! [X1] :
            ( ( r1_tarski(X1,X0)
              & v3_ordinal1(X1) )
            | ~ r2_hidden(X1,X0) ) )
   => ( ~ v3_ordinal1(sK0)
      & ! [X1] :
          ( ( r1_tarski(X1,sK0)
            & v3_ordinal1(X1) )
          | ~ r2_hidden(X1,sK0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ~ v3_ordinal1(X0)
      & ! [X1] :
          ( ( r1_tarski(X1,X0)
            & v3_ordinal1(X1) )
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ! [X1] :
            ( r2_hidden(X1,X0)
           => ( r1_tarski(X1,X0)
              & v3_ordinal1(X1) ) )
       => v3_ordinal1(X0) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
         => ( r1_tarski(X1,X0)
            & v3_ordinal1(X1) ) )
     => v3_ordinal1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_ordinal1)).

fof(f44,plain,(
    ~ v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f90,plain,(
    ~ r2_hidden(sK1(sK0),sK2(sK0)) ),
    inference(unit_resulting_resolution,[],[f84,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1(X0),sK2(X0))
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f226,plain,(
    r2_hidden(sK1(sK0),k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0)))) ),
    inference(unit_resulting_resolution,[],[f125,f180,f95,f71,f108,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_ordinal1(X0)
      | ~ r2_hidden(X1,X2)
      | ~ r1_tarski(X0,X1)
      | ~ v3_ordinal1(X2)
      | ~ v3_ordinal1(X1)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X0,X2)
              | ~ r2_hidden(X1,X2)
              | ~ r1_tarski(X0,X1)
              | ~ v3_ordinal1(X2) )
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X0,X2)
              | ~ r2_hidden(X1,X2)
              | ~ r1_tarski(X0,X1)
              | ~ v3_ordinal1(X2) )
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ! [X2] :
              ( v3_ordinal1(X2)
             => ( ( r2_hidden(X1,X2)
                  & r1_tarski(X0,X1) )
               => r2_hidden(X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_ordinal1)).

fof(f108,plain,(
    v3_ordinal1(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0)))) ),
    inference(unit_resulting_resolution,[],[f95,f67])).

fof(f67,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f47,f45])).

fof(f47,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f71,plain,(
    ! [X1] : r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | X0 != X1 ) ),
    inference(definition_unfolding,[],[f66,f45])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f95,plain,(
    v3_ordinal1(sK2(sK0)) ),
    inference(unit_resulting_resolution,[],[f84,f74])).

fof(f74,plain,
    ( v3_ordinal1(sK2(sK0))
    | v2_ordinal1(sK0) ),
    inference(resolution,[],[f42,f54])).

fof(f54,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f42,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f180,plain,(
    r1_tarski(sK1(sK0),sK2(sK0)) ),
    inference(unit_resulting_resolution,[],[f116,f95,f174,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f174,plain,(
    r1_ordinal1(sK1(sK0),sK2(sK0)) ),
    inference(unit_resulting_resolution,[],[f116,f95,f92,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f92,plain,(
    ~ r2_hidden(sK2(sK0),sK1(sK0)) ),
    inference(unit_resulting_resolution,[],[f84,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(X0),sK1(X0))
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f116,plain,(
    v3_ordinal1(sK1(sK0)) ),
    inference(unit_resulting_resolution,[],[f84,f75])).

fof(f75,plain,
    ( v3_ordinal1(sK1(sK0))
    | v2_ordinal1(sK0) ),
    inference(resolution,[],[f42,f53])).

fof(f53,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f125,plain,(
    v1_ordinal1(sK1(sK0)) ),
    inference(unit_resulting_resolution,[],[f116,f48])).

fof(f48,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        & v1_ordinal1(X0) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:00:54 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.54  % (20206)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.42/0.55  % (20198)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.42/0.55  % (20190)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.42/0.55  % (20208)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.42/0.55  % (20192)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.42/0.56  % (20198)Refutation not found, incomplete strategy% (20198)------------------------------
% 1.42/0.56  % (20198)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (20198)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.56  
% 1.42/0.56  % (20198)Memory used [KB]: 1663
% 1.42/0.56  % (20198)Time elapsed: 0.133 s
% 1.42/0.56  % (20198)------------------------------
% 1.42/0.56  % (20198)------------------------------
% 1.55/0.56  % (20200)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.55/0.56  % (20193)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.55/0.57  % (20204)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.55/0.57  % (20187)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.55/0.57  % (20186)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.55/0.57  % (20188)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.55/0.57  % (20201)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.55/0.57  % (20184)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.55/0.57  % (20205)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.55/0.58  % (20195)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.55/0.58  % (20189)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.55/0.58  % (20202)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.55/0.58  % (20209)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.55/0.58  % (20197)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.55/0.58  % (20211)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.55/0.58  % (20191)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.55/0.58  % (20194)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.55/0.58  % (20200)Refutation not found, incomplete strategy% (20200)------------------------------
% 1.55/0.58  % (20200)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.58  % (20200)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.58  
% 1.55/0.58  % (20200)Memory used [KB]: 10618
% 1.55/0.58  % (20200)Time elapsed: 0.158 s
% 1.55/0.58  % (20200)------------------------------
% 1.55/0.58  % (20200)------------------------------
% 1.55/0.58  % (20213)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.55/0.58  % (20213)Refutation not found, incomplete strategy% (20213)------------------------------
% 1.55/0.58  % (20213)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.58  % (20213)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.58  
% 1.55/0.58  % (20213)Memory used [KB]: 1663
% 1.55/0.58  % (20213)Time elapsed: 0.168 s
% 1.55/0.58  % (20213)------------------------------
% 1.55/0.58  % (20213)------------------------------
% 1.55/0.58  % (20199)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.55/0.59  % (20203)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.55/0.59  % (20196)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.55/0.59  % (20211)Refutation not found, incomplete strategy% (20211)------------------------------
% 1.55/0.59  % (20211)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.59  % (20210)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.55/0.59  % (20196)Refutation not found, incomplete strategy% (20196)------------------------------
% 1.55/0.59  % (20196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.59  % (20196)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.59  
% 1.55/0.59  % (20196)Memory used [KB]: 10618
% 1.55/0.59  % (20196)Time elapsed: 0.168 s
% 1.55/0.59  % (20196)------------------------------
% 1.55/0.59  % (20196)------------------------------
% 1.55/0.59  % (20211)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.59  
% 1.55/0.59  % (20211)Memory used [KB]: 6140
% 1.55/0.59  % (20211)Time elapsed: 0.169 s
% 1.55/0.59  % (20211)------------------------------
% 1.55/0.59  % (20211)------------------------------
% 1.55/0.59  % (20207)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.55/0.59  % (20210)Refutation not found, incomplete strategy% (20210)------------------------------
% 1.55/0.59  % (20210)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.59  % (20210)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.59  
% 1.55/0.59  % (20210)Memory used [KB]: 6268
% 1.55/0.59  % (20210)Time elapsed: 0.169 s
% 1.55/0.59  % (20210)------------------------------
% 1.55/0.59  % (20210)------------------------------
% 1.55/0.59  % (20209)Refutation not found, incomplete strategy% (20209)------------------------------
% 1.55/0.59  % (20209)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.59  % (20209)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.59  
% 1.55/0.59  % (20209)Memory used [KB]: 6396
% 1.55/0.59  % (20209)Time elapsed: 0.132 s
% 1.55/0.59  % (20209)------------------------------
% 1.55/0.59  % (20209)------------------------------
% 1.55/0.59  % (20212)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.55/0.59  % (20195)Refutation found. Thanks to Tanya!
% 1.55/0.59  % SZS status Theorem for theBenchmark
% 1.55/0.59  % SZS output start Proof for theBenchmark
% 1.55/0.59  fof(f239,plain,(
% 1.55/0.59    $false),
% 1.55/0.59    inference(subsumption_resolution,[],[f226,f168])).
% 1.55/0.59  fof(f168,plain,(
% 1.55/0.59    ~r2_hidden(sK1(sK0),k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))))),
% 1.55/0.59    inference(unit_resulting_resolution,[],[f90,f91,f70])).
% 1.55/0.59  fof(f70,plain,(
% 1.55/0.59    ( ! [X0,X1] : (~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | r2_hidden(X0,X1) | X0 = X1) )),
% 1.55/0.59    inference(definition_unfolding,[],[f64,f45])).
% 1.55/0.59  fof(f45,plain,(
% 1.55/0.59    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 1.55/0.59    inference(cnf_transformation,[],[f3])).
% 1.55/0.59  fof(f3,axiom,(
% 1.55/0.59    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 1.55/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).
% 1.55/0.59  fof(f64,plain,(
% 1.55/0.59    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 1.55/0.59    inference(cnf_transformation,[],[f41])).
% 1.55/0.59  fof(f41,plain,(
% 1.55/0.59    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 1.55/0.59    inference(flattening,[],[f40])).
% 1.55/0.59  fof(f40,plain,(
% 1.55/0.59    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 1.55/0.59    inference(nnf_transformation,[],[f7])).
% 1.55/0.59  fof(f7,axiom,(
% 1.55/0.59    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 1.55/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).
% 1.55/0.59  fof(f91,plain,(
% 1.55/0.59    sK2(sK0) != sK1(sK0)),
% 1.55/0.59    inference(unit_resulting_resolution,[],[f84,f56])).
% 1.55/0.59  fof(f56,plain,(
% 1.55/0.59    ( ! [X0] : (sK1(X0) != sK2(X0) | v2_ordinal1(X0)) )),
% 1.55/0.59    inference(cnf_transformation,[],[f34])).
% 1.55/0.59  fof(f34,plain,(
% 1.55/0.59    ! [X0] : ((v2_ordinal1(X0) | (~r2_hidden(sK2(X0),sK1(X0)) & sK1(X0) != sK2(X0) & ~r2_hidden(sK1(X0),sK2(X0)) & r2_hidden(sK2(X0),X0) & r2_hidden(sK1(X0),X0))) & (! [X3,X4] : (r2_hidden(X4,X3) | X3 = X4 | r2_hidden(X3,X4) | ~r2_hidden(X4,X0) | ~r2_hidden(X3,X0)) | ~v2_ordinal1(X0)))),
% 1.55/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f32,f33])).
% 1.55/0.59  fof(f33,plain,(
% 1.55/0.59    ! [X0] : (? [X1,X2] : (~r2_hidden(X2,X1) & X1 != X2 & ~r2_hidden(X1,X2) & r2_hidden(X2,X0) & r2_hidden(X1,X0)) => (~r2_hidden(sK2(X0),sK1(X0)) & sK1(X0) != sK2(X0) & ~r2_hidden(sK1(X0),sK2(X0)) & r2_hidden(sK2(X0),X0) & r2_hidden(sK1(X0),X0)))),
% 1.55/0.59    introduced(choice_axiom,[])).
% 1.55/0.59  fof(f32,plain,(
% 1.55/0.59    ! [X0] : ((v2_ordinal1(X0) | ? [X1,X2] : (~r2_hidden(X2,X1) & X1 != X2 & ~r2_hidden(X1,X2) & r2_hidden(X2,X0) & r2_hidden(X1,X0))) & (! [X3,X4] : (r2_hidden(X4,X3) | X3 = X4 | r2_hidden(X3,X4) | ~r2_hidden(X4,X0) | ~r2_hidden(X3,X0)) | ~v2_ordinal1(X0)))),
% 1.55/0.59    inference(rectify,[],[f31])).
% 1.55/0.59  fof(f31,plain,(
% 1.55/0.59    ! [X0] : ((v2_ordinal1(X0) | ? [X1,X2] : (~r2_hidden(X2,X1) & X1 != X2 & ~r2_hidden(X1,X2) & r2_hidden(X2,X0) & r2_hidden(X1,X0))) & (! [X1,X2] : (r2_hidden(X2,X1) | X1 = X2 | r2_hidden(X1,X2) | ~r2_hidden(X2,X0) | ~r2_hidden(X1,X0)) | ~v2_ordinal1(X0)))),
% 1.55/0.59    inference(nnf_transformation,[],[f23])).
% 1.55/0.59  fof(f23,plain,(
% 1.55/0.59    ! [X0] : (v2_ordinal1(X0) <=> ! [X1,X2] : (r2_hidden(X2,X1) | X1 = X2 | r2_hidden(X1,X2) | ~r2_hidden(X2,X0) | ~r2_hidden(X1,X0)))),
% 1.55/0.59    inference(ennf_transformation,[],[f5])).
% 1.55/0.59  fof(f5,axiom,(
% 1.55/0.59    ! [X0] : (v2_ordinal1(X0) <=> ! [X1,X2] : ~(~r2_hidden(X2,X1) & X1 != X2 & ~r2_hidden(X1,X2) & r2_hidden(X2,X0) & r2_hidden(X1,X0)))),
% 1.55/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_ordinal1)).
% 1.55/0.59  fof(f84,plain,(
% 1.55/0.59    ~v2_ordinal1(sK0)),
% 1.55/0.59    inference(unit_resulting_resolution,[],[f44,f83,f51])).
% 1.55/0.59  fof(f51,plain,(
% 1.55/0.59    ( ! [X0] : (~v2_ordinal1(X0) | v3_ordinal1(X0) | ~v1_ordinal1(X0)) )),
% 1.55/0.59    inference(cnf_transformation,[],[f22])).
% 1.55/0.59  fof(f22,plain,(
% 1.55/0.59    ! [X0] : (v3_ordinal1(X0) | ~v2_ordinal1(X0) | ~v1_ordinal1(X0))),
% 1.55/0.59    inference(flattening,[],[f21])).
% 1.55/0.59  fof(f21,plain,(
% 1.55/0.59    ! [X0] : (v3_ordinal1(X0) | (~v2_ordinal1(X0) | ~v1_ordinal1(X0)))),
% 1.55/0.59    inference(ennf_transformation,[],[f2])).
% 1.55/0.59  fof(f2,axiom,(
% 1.55/0.59    ! [X0] : ((v2_ordinal1(X0) & v1_ordinal1(X0)) => v3_ordinal1(X0))),
% 1.55/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_ordinal1)).
% 1.55/0.59  fof(f83,plain,(
% 1.55/0.59    v1_ordinal1(sK0)),
% 1.55/0.59    inference(subsumption_resolution,[],[f82,f59])).
% 1.55/0.59  fof(f59,plain,(
% 1.55/0.59    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_ordinal1(X0)) )),
% 1.55/0.59    inference(cnf_transformation,[],[f38])).
% 1.55/0.59  fof(f38,plain,(
% 1.55/0.59    ! [X0] : ((v1_ordinal1(X0) | (~r1_tarski(sK3(X0),X0) & r2_hidden(sK3(X0),X0))) & (! [X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0)) | ~v1_ordinal1(X0)))),
% 1.55/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).
% 1.55/0.59  fof(f37,plain,(
% 1.55/0.59    ! [X0] : (? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0)) => (~r1_tarski(sK3(X0),X0) & r2_hidden(sK3(X0),X0)))),
% 1.55/0.59    introduced(choice_axiom,[])).
% 1.55/0.59  fof(f36,plain,(
% 1.55/0.59    ! [X0] : ((v1_ordinal1(X0) | ? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0))) & (! [X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0)) | ~v1_ordinal1(X0)))),
% 1.55/0.59    inference(rectify,[],[f35])).
% 1.55/0.59  fof(f35,plain,(
% 1.55/0.59    ! [X0] : ((v1_ordinal1(X0) | ? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0))) & (! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)) | ~v1_ordinal1(X0)))),
% 1.55/0.59    inference(nnf_transformation,[],[f24])).
% 1.55/0.59  fof(f24,plain,(
% 1.55/0.59    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)))),
% 1.55/0.59    inference(ennf_transformation,[],[f4])).
% 1.55/0.59  fof(f4,axiom,(
% 1.55/0.59    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 1.55/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).
% 1.55/0.59  fof(f82,plain,(
% 1.55/0.59    ~r2_hidden(sK3(sK0),sK0) | v1_ordinal1(sK0)),
% 1.55/0.59    inference(resolution,[],[f43,f60])).
% 1.55/0.59  fof(f60,plain,(
% 1.55/0.59    ( ! [X0] : (~r1_tarski(sK3(X0),X0) | v1_ordinal1(X0)) )),
% 1.55/0.59    inference(cnf_transformation,[],[f38])).
% 1.55/0.59  fof(f43,plain,(
% 1.55/0.59    ( ! [X1] : (r1_tarski(X1,sK0) | ~r2_hidden(X1,sK0)) )),
% 1.55/0.59    inference(cnf_transformation,[],[f30])).
% 1.55/0.59  fof(f30,plain,(
% 1.55/0.59    ~v3_ordinal1(sK0) & ! [X1] : ((r1_tarski(X1,sK0) & v3_ordinal1(X1)) | ~r2_hidden(X1,sK0))),
% 1.55/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f29])).
% 1.55/0.59  fof(f29,plain,(
% 1.55/0.59    ? [X0] : (~v3_ordinal1(X0) & ! [X1] : ((r1_tarski(X1,X0) & v3_ordinal1(X1)) | ~r2_hidden(X1,X0))) => (~v3_ordinal1(sK0) & ! [X1] : ((r1_tarski(X1,sK0) & v3_ordinal1(X1)) | ~r2_hidden(X1,sK0)))),
% 1.55/0.59    introduced(choice_axiom,[])).
% 1.55/0.59  fof(f14,plain,(
% 1.55/0.59    ? [X0] : (~v3_ordinal1(X0) & ! [X1] : ((r1_tarski(X1,X0) & v3_ordinal1(X1)) | ~r2_hidden(X1,X0)))),
% 1.55/0.59    inference(ennf_transformation,[],[f13])).
% 1.55/0.59  fof(f13,negated_conjecture,(
% 1.55/0.59    ~! [X0] : (! [X1] : (r2_hidden(X1,X0) => (r1_tarski(X1,X0) & v3_ordinal1(X1))) => v3_ordinal1(X0))),
% 1.55/0.59    inference(negated_conjecture,[],[f12])).
% 1.55/0.59  fof(f12,conjecture,(
% 1.55/0.59    ! [X0] : (! [X1] : (r2_hidden(X1,X0) => (r1_tarski(X1,X0) & v3_ordinal1(X1))) => v3_ordinal1(X0))),
% 1.55/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_ordinal1)).
% 1.55/0.59  fof(f44,plain,(
% 1.55/0.59    ~v3_ordinal1(sK0)),
% 1.55/0.59    inference(cnf_transformation,[],[f30])).
% 1.55/0.59  fof(f90,plain,(
% 1.55/0.59    ~r2_hidden(sK1(sK0),sK2(sK0))),
% 1.55/0.59    inference(unit_resulting_resolution,[],[f84,f55])).
% 1.55/0.59  fof(f55,plain,(
% 1.55/0.59    ( ! [X0] : (~r2_hidden(sK1(X0),sK2(X0)) | v2_ordinal1(X0)) )),
% 1.55/0.59    inference(cnf_transformation,[],[f34])).
% 1.55/0.59  fof(f226,plain,(
% 1.55/0.59    r2_hidden(sK1(sK0),k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))))),
% 1.55/0.59    inference(unit_resulting_resolution,[],[f125,f180,f95,f71,f108,f46])).
% 1.55/0.59  fof(f46,plain,(
% 1.55/0.59    ( ! [X2,X0,X1] : (~v1_ordinal1(X0) | ~r2_hidden(X1,X2) | ~r1_tarski(X0,X1) | ~v3_ordinal1(X2) | ~v3_ordinal1(X1) | r2_hidden(X0,X2)) )),
% 1.55/0.59    inference(cnf_transformation,[],[f16])).
% 1.55/0.59  fof(f16,plain,(
% 1.55/0.59    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | ~r1_tarski(X0,X1) | ~v3_ordinal1(X2)) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 1.55/0.59    inference(flattening,[],[f15])).
% 1.55/0.59  fof(f15,plain,(
% 1.55/0.59    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X0,X2) | (~r2_hidden(X1,X2) | ~r1_tarski(X0,X1))) | ~v3_ordinal1(X2)) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 1.55/0.59    inference(ennf_transformation,[],[f8])).
% 1.55/0.59  fof(f8,axiom,(
% 1.55/0.59    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ! [X2] : (v3_ordinal1(X2) => ((r2_hidden(X1,X2) & r1_tarski(X0,X1)) => r2_hidden(X0,X2)))))),
% 1.55/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_ordinal1)).
% 1.55/0.59  fof(f108,plain,(
% 1.55/0.59    v3_ordinal1(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))))),
% 1.55/0.59    inference(unit_resulting_resolution,[],[f95,f67])).
% 1.55/0.59  fof(f67,plain,(
% 1.55/0.59    ( ! [X0] : (v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(X0)) )),
% 1.55/0.59    inference(definition_unfolding,[],[f47,f45])).
% 1.55/0.59  fof(f47,plain,(
% 1.55/0.59    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 1.55/0.59    inference(cnf_transformation,[],[f17])).
% 1.55/0.59  fof(f17,plain,(
% 1.55/0.59    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 1.55/0.59    inference(ennf_transformation,[],[f11])).
% 1.55/0.59  fof(f11,axiom,(
% 1.55/0.59    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 1.55/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).
% 1.55/0.59  fof(f71,plain,(
% 1.55/0.59    ( ! [X1] : (r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1)))) )),
% 1.55/0.59    inference(equality_resolution,[],[f68])).
% 1.55/0.59  fof(f68,plain,(
% 1.55/0.59    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | X0 != X1) )),
% 1.55/0.59    inference(definition_unfolding,[],[f66,f45])).
% 1.55/0.59  fof(f66,plain,(
% 1.55/0.59    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 1.55/0.59    inference(cnf_transformation,[],[f41])).
% 1.55/0.59  fof(f95,plain,(
% 1.55/0.59    v3_ordinal1(sK2(sK0))),
% 1.55/0.59    inference(unit_resulting_resolution,[],[f84,f74])).
% 1.55/0.59  fof(f74,plain,(
% 1.55/0.59    v3_ordinal1(sK2(sK0)) | v2_ordinal1(sK0)),
% 1.55/0.59    inference(resolution,[],[f42,f54])).
% 1.55/0.59  fof(f54,plain,(
% 1.55/0.59    ( ! [X0] : (r2_hidden(sK2(X0),X0) | v2_ordinal1(X0)) )),
% 1.55/0.59    inference(cnf_transformation,[],[f34])).
% 1.55/0.59  fof(f42,plain,(
% 1.55/0.59    ( ! [X1] : (~r2_hidden(X1,sK0) | v3_ordinal1(X1)) )),
% 1.55/0.59    inference(cnf_transformation,[],[f30])).
% 1.55/0.59  fof(f180,plain,(
% 1.55/0.59    r1_tarski(sK1(sK0),sK2(sK0))),
% 1.55/0.59    inference(unit_resulting_resolution,[],[f116,f95,f174,f62])).
% 1.55/0.59  fof(f62,plain,(
% 1.55/0.59    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X0)) )),
% 1.55/0.59    inference(cnf_transformation,[],[f39])).
% 1.55/0.59  fof(f39,plain,(
% 1.55/0.59    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.55/0.59    inference(nnf_transformation,[],[f28])).
% 1.55/0.59  fof(f28,plain,(
% 1.55/0.59    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.55/0.59    inference(flattening,[],[f27])).
% 1.55/0.59  fof(f27,plain,(
% 1.55/0.59    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 1.55/0.59    inference(ennf_transformation,[],[f6])).
% 1.55/0.59  fof(f6,axiom,(
% 1.55/0.59    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 1.55/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 1.55/0.59  fof(f174,plain,(
% 1.55/0.59    r1_ordinal1(sK1(sK0),sK2(sK0))),
% 1.55/0.59    inference(unit_resulting_resolution,[],[f116,f95,f92,f50])).
% 1.55/0.59  fof(f50,plain,(
% 1.55/0.59    ( ! [X0,X1] : (~v3_ordinal1(X1) | r1_ordinal1(X0,X1) | r2_hidden(X1,X0) | ~v3_ordinal1(X0)) )),
% 1.55/0.59    inference(cnf_transformation,[],[f20])).
% 1.55/0.59  fof(f20,plain,(
% 1.55/0.59    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.55/0.59    inference(flattening,[],[f19])).
% 1.55/0.59  fof(f19,plain,(
% 1.55/0.59    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.55/0.59    inference(ennf_transformation,[],[f10])).
% 1.55/0.59  fof(f10,axiom,(
% 1.55/0.59    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 1.55/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).
% 1.55/0.59  fof(f92,plain,(
% 1.55/0.59    ~r2_hidden(sK2(sK0),sK1(sK0))),
% 1.55/0.59    inference(unit_resulting_resolution,[],[f84,f57])).
% 1.55/0.59  fof(f57,plain,(
% 1.55/0.59    ( ! [X0] : (~r2_hidden(sK2(X0),sK1(X0)) | v2_ordinal1(X0)) )),
% 1.55/0.59    inference(cnf_transformation,[],[f34])).
% 1.55/0.59  fof(f116,plain,(
% 1.55/0.59    v3_ordinal1(sK1(sK0))),
% 1.55/0.59    inference(unit_resulting_resolution,[],[f84,f75])).
% 1.55/0.59  fof(f75,plain,(
% 1.55/0.59    v3_ordinal1(sK1(sK0)) | v2_ordinal1(sK0)),
% 1.55/0.59    inference(resolution,[],[f42,f53])).
% 1.55/0.59  fof(f53,plain,(
% 1.55/0.59    ( ! [X0] : (r2_hidden(sK1(X0),X0) | v2_ordinal1(X0)) )),
% 1.55/0.59    inference(cnf_transformation,[],[f34])).
% 1.55/0.59  fof(f125,plain,(
% 1.55/0.59    v1_ordinal1(sK1(sK0))),
% 1.55/0.59    inference(unit_resulting_resolution,[],[f116,f48])).
% 1.55/0.59  fof(f48,plain,(
% 1.55/0.59    ( ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 1.55/0.59    inference(cnf_transformation,[],[f18])).
% 1.55/0.59  fof(f18,plain,(
% 1.55/0.59    ! [X0] : ((v2_ordinal1(X0) & v1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 1.55/0.59    inference(ennf_transformation,[],[f1])).
% 1.55/0.59  fof(f1,axiom,(
% 1.55/0.59    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 1.55/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).
% 1.55/0.59  % SZS output end Proof for theBenchmark
% 1.55/0.59  % (20195)------------------------------
% 1.55/0.59  % (20195)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.59  % (20195)Termination reason: Refutation
% 1.55/0.59  
% 1.55/0.59  % (20195)Memory used [KB]: 6268
% 1.55/0.59  % (20195)Time elapsed: 0.175 s
% 1.55/0.59  % (20195)------------------------------
% 1.55/0.59  % (20195)------------------------------
% 1.55/0.60  % (20182)Success in time 0.226 s
%------------------------------------------------------------------------------
