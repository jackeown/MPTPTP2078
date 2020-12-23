%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 328 expanded)
%              Number of leaves         :    9 (  84 expanded)
%              Depth                    :   22
%              Number of atoms          :  257 (1388 expanded)
%              Number of equality atoms :   63 ( 163 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f109,plain,(
    $false ),
    inference(subsumption_resolution,[],[f108,f30])).

fof(f30,plain,(
    ~ v2_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    & v2_funct_1(sK2)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f8,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ~ v2_funct_1(k2_funct_1(X0))
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ~ v2_funct_1(k2_funct_1(sK2))
      & v2_funct_1(sK2)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

% (31908)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
fof(f8,plain,(
    ? [X0] :
      ( ~ v2_funct_1(k2_funct_1(X0))
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ~ v2_funct_1(k2_funct_1(X0))
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => v2_funct_1(k2_funct_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => v2_funct_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_1)).

fof(f108,plain,(
    v2_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f107,f27])).

fof(f27,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f107,plain,
    ( ~ v1_relat_1(sK2)
    | v2_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f105,f28])).

fof(f28,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f105,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | v2_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f104,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ sP0(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(k2_funct_1(X0)) ) ),
    inference(resolution,[],[f51,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ sP0(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v2_funct_1(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f51,plain,(
    ! [X0] :
      ( sP1(k2_funct_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f50,f31])).

fof(f31,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sP1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0)) ) ),
    inference(resolution,[],[f32,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f14,f18,f17])).

fof(f17,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1,X2] :
          ( X1 = X2
          | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
          | ~ r2_hidden(X2,k1_relat_1(X0))
          | ~ r2_hidden(X1,k1_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f14,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f32,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f104,plain,(
    sP0(k2_funct_1(sK2)) ),
    inference(trivial_inequality_removal,[],[f102])).

fof(f102,plain,
    ( sK3(k2_funct_1(sK2)) != sK3(k2_funct_1(sK2))
    | sP0(k2_funct_1(sK2)) ),
    inference(superposition,[],[f41,f98])).

fof(f98,plain,(
    sK4(k2_funct_1(sK2)) = sK3(k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f97,f75])).

fof(f75,plain,(
    sK3(k2_funct_1(sK2)) = k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK3(k2_funct_1(sK2)))) ),
    inference(subsumption_resolution,[],[f74,f30])).

fof(f74,plain,
    ( sK3(k2_funct_1(sK2)) = k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK3(k2_funct_1(sK2))))
    | v2_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f73,f27])).

fof(f73,plain,
    ( sK3(k2_funct_1(sK2)) = k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK3(k2_funct_1(sK2))))
    | ~ v1_relat_1(sK2)
    | v2_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f72,f28])).

fof(f72,plain,
    ( sK3(k2_funct_1(sK2)) = k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK3(k2_funct_1(sK2))))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | v2_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f67,f52])).

fof(f67,plain,
    ( sP0(k2_funct_1(sK2))
    | sK3(k2_funct_1(sK2)) = k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK3(k2_funct_1(sK2)))) ),
    inference(resolution,[],[f65,f59])).

fof(f59,plain,
    ( r2_hidden(sK3(k2_funct_1(sK2)),k2_relat_1(sK2))
    | sP0(k2_funct_1(sK2)) ),
    inference(superposition,[],[f38,f57])).

fof(f57,plain,(
    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f56,f27])).

fof(f56,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f55,f28])).

fof(f55,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f33,f29])).

fof(f29,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f38,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),k1_relat_1(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( sK3(X0) != sK4(X0)
          & k1_funct_1(X0,sK3(X0)) = k1_funct_1(X0,sK4(X0))
          & r2_hidden(sK4(X0),k1_relat_1(X0))
          & r2_hidden(sK3(X0),k1_relat_1(X0)) ) )
      & ( ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
            | ~ r2_hidden(X4,k1_relat_1(X0))
            | ~ r2_hidden(X3,k1_relat_1(X0)) )
        | ~ sP0(X0) ) ) ),
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
      ( ( sP0(X0)
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
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( sP0(X0)
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
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f65,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK2))
      | k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f64,f27])).

fof(f64,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK2))
      | k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),X0)) = X0
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f63,f28])).

fof(f63,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK2))
      | k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),X0)) = X0
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f43,f29])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
        & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 )
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
        & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 )
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k2_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
          & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_funct_1)).

fof(f97,plain,(
    sK4(k2_funct_1(sK2)) = k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK3(k2_funct_1(sK2)))) ),
    inference(backward_demodulation,[],[f71,f96])).

fof(f96,plain,(
    k1_funct_1(k2_funct_1(sK2),sK4(k2_funct_1(sK2))) = k1_funct_1(k2_funct_1(sK2),sK3(k2_funct_1(sK2))) ),
    inference(subsumption_resolution,[],[f95,f30])).

fof(f95,plain,
    ( k1_funct_1(k2_funct_1(sK2),sK4(k2_funct_1(sK2))) = k1_funct_1(k2_funct_1(sK2),sK3(k2_funct_1(sK2)))
    | v2_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f93,f27])).

fof(f93,plain,
    ( k1_funct_1(k2_funct_1(sK2),sK4(k2_funct_1(sK2))) = k1_funct_1(k2_funct_1(sK2),sK3(k2_funct_1(sK2)))
    | ~ v1_relat_1(sK2)
    | v2_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f54,f28])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k1_funct_1(k2_funct_1(X0),sK3(k2_funct_1(X0))) = k1_funct_1(k2_funct_1(X0),sK4(k2_funct_1(X0)))
      | ~ v1_relat_1(X0)
      | v2_funct_1(k2_funct_1(X0)) ) ),
    inference(resolution,[],[f40,f52])).

fof(f40,plain,(
    ! [X0] :
      ( sP0(X0)
      | k1_funct_1(X0,sK3(X0)) = k1_funct_1(X0,sK4(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f71,plain,(
    sK4(k2_funct_1(sK2)) = k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK4(k2_funct_1(sK2)))) ),
    inference(subsumption_resolution,[],[f70,f30])).

fof(f70,plain,
    ( sK4(k2_funct_1(sK2)) = k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK4(k2_funct_1(sK2))))
    | v2_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f69,f27])).

fof(f69,plain,
    ( sK4(k2_funct_1(sK2)) = k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK4(k2_funct_1(sK2))))
    | ~ v1_relat_1(sK2)
    | v2_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f68,f28])).

fof(f68,plain,
    ( sK4(k2_funct_1(sK2)) = k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK4(k2_funct_1(sK2))))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | v2_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f66,f52])).

fof(f66,plain,
    ( sP0(k2_funct_1(sK2))
    | sK4(k2_funct_1(sK2)) = k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK4(k2_funct_1(sK2)))) ),
    inference(resolution,[],[f65,f58])).

fof(f58,plain,
    ( r2_hidden(sK4(k2_funct_1(sK2)),k2_relat_1(sK2))
    | sP0(k2_funct_1(sK2)) ),
    inference(superposition,[],[f39,f57])).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),k1_relat_1(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f41,plain,(
    ! [X0] :
      ( sK3(X0) != sK4(X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:47:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (31900)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (31891)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (31892)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.50  % (31889)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (31886)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (31890)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (31901)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.50  % (31889)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % (31897)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.50  % (31906)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.50  % (31898)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (31902)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.51  % (31899)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f108,f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ~v2_funct_1(k2_funct_1(sK2))),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ~v2_funct_1(k2_funct_1(sK2)) & v2_funct_1(sK2) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f8,f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ? [X0] : (~v2_funct_1(k2_funct_1(X0)) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (~v2_funct_1(k2_funct_1(sK2)) & v2_funct_1(sK2) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  % (31908)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  fof(f8,plain,(
% 0.21/0.51    ? [X0] : (~v2_funct_1(k2_funct_1(X0)) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f7])).
% 0.21/0.51  fof(f7,plain,(
% 0.21/0.51    ? [X0] : ((~v2_funct_1(k2_funct_1(X0)) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => v2_funct_1(k2_funct_1(X0))))),
% 0.21/0.51    inference(negated_conjecture,[],[f5])).
% 0.21/0.51  fof(f5,conjecture,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => v2_funct_1(k2_funct_1(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_1)).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    v2_funct_1(k2_funct_1(sK2))),
% 0.21/0.51    inference(subsumption_resolution,[],[f107,f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    v1_relat_1(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    ~v1_relat_1(sK2) | v2_funct_1(k2_funct_1(sK2))),
% 0.21/0.51    inference(subsumption_resolution,[],[f105,f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    v1_funct_1(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | v2_funct_1(k2_funct_1(sK2))),
% 0.21/0.51    inference(resolution,[],[f104,f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ( ! [X0] : (~sP0(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v2_funct_1(k2_funct_1(X0))) )),
% 0.21/0.51    inference(resolution,[],[f51,f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X0] : (~sP1(X0) | ~sP0(X0) | v2_funct_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : (((v2_funct_1(X0) | ~sP0(X0)) & (sP0(X0) | ~v2_funct_1(X0))) | ~sP1(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : ((v2_funct_1(X0) <=> sP0(X0)) | ~sP1(X0))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ( ! [X0] : (sP1(k2_funct_1(X0)) | ~v1_relat_1(X0) | ~v1_funct_1(X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f50,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f9])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | sP1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0))) )),
% 0.21/0.51    inference(resolution,[],[f32,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_funct_1(X0) | sP1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(definition_folding,[],[f14,f18,f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : (sP0(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    sP0(k2_funct_1(sK2))),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f102])).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    sK3(k2_funct_1(sK2)) != sK3(k2_funct_1(sK2)) | sP0(k2_funct_1(sK2))),
% 0.21/0.51    inference(superposition,[],[f41,f98])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    sK4(k2_funct_1(sK2)) = sK3(k2_funct_1(sK2))),
% 0.21/0.51    inference(forward_demodulation,[],[f97,f75])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    sK3(k2_funct_1(sK2)) = k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK3(k2_funct_1(sK2))))),
% 0.21/0.51    inference(subsumption_resolution,[],[f74,f30])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    sK3(k2_funct_1(sK2)) = k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK3(k2_funct_1(sK2)))) | v2_funct_1(k2_funct_1(sK2))),
% 0.21/0.51    inference(subsumption_resolution,[],[f73,f27])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    sK3(k2_funct_1(sK2)) = k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK3(k2_funct_1(sK2)))) | ~v1_relat_1(sK2) | v2_funct_1(k2_funct_1(sK2))),
% 0.21/0.51    inference(subsumption_resolution,[],[f72,f28])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    sK3(k2_funct_1(sK2)) = k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK3(k2_funct_1(sK2)))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | v2_funct_1(k2_funct_1(sK2))),
% 0.21/0.51    inference(resolution,[],[f67,f52])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    sP0(k2_funct_1(sK2)) | sK3(k2_funct_1(sK2)) = k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK3(k2_funct_1(sK2))))),
% 0.21/0.51    inference(resolution,[],[f65,f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    r2_hidden(sK3(k2_funct_1(sK2)),k2_relat_1(sK2)) | sP0(k2_funct_1(sK2))),
% 0.21/0.51    inference(superposition,[],[f38,f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.21/0.51    inference(subsumption_resolution,[],[f56,f27])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f55,f28])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.21/0.51    inference(resolution,[],[f33,f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    v2_funct_1(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK3(X0),k1_relat_1(X0)) | sP0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0] : ((sP0(X0) | (sK3(X0) != sK4(X0) & k1_funct_1(X0,sK3(X0)) = k1_funct_1(X0,sK4(X0)) & r2_hidden(sK4(X0),k1_relat_1(X0)) & r2_hidden(sK3(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X0)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f24,f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK3(X0) != sK4(X0) & k1_funct_1(X0,sK3(X0)) = k1_funct_1(X0,sK4(X0)) & r2_hidden(sK4(X0),k1_relat_1(X0)) & r2_hidden(sK3(X0),k1_relat_1(X0))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : ((sP0(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X0)))),
% 0.21/0.51    inference(rectify,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : ((sP0(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~sP0(X0)))),
% 0.21/0.51    inference(nnf_transformation,[],[f17])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK2)) | k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),X0)) = X0) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f64,f27])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK2)) | k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),X0)) = X0 | ~v1_relat_1(sK2)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f63,f28])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK2)) | k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),X0)) = X0 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.21/0.51    inference(resolution,[],[f43,f29])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v2_funct_1(X1) | ~r2_hidden(X0,k2_relat_1(X1)) | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0,X1] : (((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0) | (~r2_hidden(X0,k2_relat_1(X1)) | ~v2_funct_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_funct_1)).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    sK4(k2_funct_1(sK2)) = k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK3(k2_funct_1(sK2))))),
% 0.21/0.51    inference(backward_demodulation,[],[f71,f96])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    k1_funct_1(k2_funct_1(sK2),sK4(k2_funct_1(sK2))) = k1_funct_1(k2_funct_1(sK2),sK3(k2_funct_1(sK2)))),
% 0.21/0.51    inference(subsumption_resolution,[],[f95,f30])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    k1_funct_1(k2_funct_1(sK2),sK4(k2_funct_1(sK2))) = k1_funct_1(k2_funct_1(sK2),sK3(k2_funct_1(sK2))) | v2_funct_1(k2_funct_1(sK2))),
% 0.21/0.51    inference(subsumption_resolution,[],[f93,f27])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    k1_funct_1(k2_funct_1(sK2),sK4(k2_funct_1(sK2))) = k1_funct_1(k2_funct_1(sK2),sK3(k2_funct_1(sK2))) | ~v1_relat_1(sK2) | v2_funct_1(k2_funct_1(sK2))),
% 0.21/0.51    inference(resolution,[],[f54,f28])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_funct_1(X0) | k1_funct_1(k2_funct_1(X0),sK3(k2_funct_1(X0))) = k1_funct_1(k2_funct_1(X0),sK4(k2_funct_1(X0))) | ~v1_relat_1(X0) | v2_funct_1(k2_funct_1(X0))) )),
% 0.21/0.51    inference(resolution,[],[f40,f52])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X0] : (sP0(X0) | k1_funct_1(X0,sK3(X0)) = k1_funct_1(X0,sK4(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    sK4(k2_funct_1(sK2)) = k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK4(k2_funct_1(sK2))))),
% 0.21/0.51    inference(subsumption_resolution,[],[f70,f30])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    sK4(k2_funct_1(sK2)) = k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK4(k2_funct_1(sK2)))) | v2_funct_1(k2_funct_1(sK2))),
% 0.21/0.51    inference(subsumption_resolution,[],[f69,f27])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    sK4(k2_funct_1(sK2)) = k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK4(k2_funct_1(sK2)))) | ~v1_relat_1(sK2) | v2_funct_1(k2_funct_1(sK2))),
% 0.21/0.51    inference(subsumption_resolution,[],[f68,f28])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    sK4(k2_funct_1(sK2)) = k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK4(k2_funct_1(sK2)))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | v2_funct_1(k2_funct_1(sK2))),
% 0.21/0.51    inference(resolution,[],[f66,f52])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    sP0(k2_funct_1(sK2)) | sK4(k2_funct_1(sK2)) = k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK4(k2_funct_1(sK2))))),
% 0.21/0.51    inference(resolution,[],[f65,f58])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    r2_hidden(sK4(k2_funct_1(sK2)),k2_relat_1(sK2)) | sP0(k2_funct_1(sK2))),
% 0.21/0.51    inference(superposition,[],[f39,f57])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK4(X0),k1_relat_1(X0)) | sP0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X0] : (sK3(X0) != sK4(X0) | sP0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (31889)------------------------------
% 0.21/0.51  % (31889)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31889)Termination reason: Refutation
% 0.21/0.51  % (31904)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  
% 0.21/0.51  % (31889)Memory used [KB]: 6140
% 0.21/0.51  % (31889)Time elapsed: 0.088 s
% 0.21/0.51  % (31889)------------------------------
% 0.21/0.51  % (31889)------------------------------
% 0.21/0.51  % (31885)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (31892)Refutation not found, incomplete strategy% (31892)------------------------------
% 0.21/0.51  % (31892)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31892)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (31892)Memory used [KB]: 10490
% 0.21/0.51  % (31892)Time elapsed: 0.092 s
% 0.21/0.51  % (31892)------------------------------
% 0.21/0.51  % (31892)------------------------------
% 0.21/0.51  % (31882)Success in time 0.149 s
%------------------------------------------------------------------------------
