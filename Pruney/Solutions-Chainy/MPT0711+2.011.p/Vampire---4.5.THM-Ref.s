%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:42 EST 2020

% Result     : Theorem 1.52s
% Output     : Refutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 982 expanded)
%              Number of leaves         :   17 ( 355 expanded)
%              Depth                    :   20
%              Number of atoms          :  330 (5873 expanded)
%              Number of equality atoms :  100 (2408 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1178,plain,(
    $false ),
    inference(subsumption_resolution,[],[f872,f1170])).

fof(f1170,plain,(
    k1_funct_1(sK5,sK8(sK5,sK4,k1_relat_1(k7_relat_1(sK4,sK6)))) = k1_funct_1(sK4,sK8(sK5,sK4,k1_relat_1(k7_relat_1(sK4,sK6)))) ),
    inference(unit_resulting_resolution,[],[f1120,f52])).

fof(f52,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK6)
      | k1_funct_1(sK4,X3) = k1_funct_1(sK5,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( k7_relat_1(sK4,sK6) != k7_relat_1(sK5,sK6)
    & ! [X3] :
        ( k1_funct_1(sK4,X3) = k1_funct_1(sK5,X3)
        | ~ r2_hidden(X3,sK6) )
    & k1_relat_1(sK4) = k1_relat_1(sK5)
    & v1_funct_1(sK5)
    & v1_relat_1(sK5)
    & v1_funct_1(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f12,f32,f31,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
                & ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,X2) )
                & k1_relat_1(X1) = k1_relat_1(X0) )
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k7_relat_1(X1,X2) != k7_relat_1(sK4,X2)
              & ! [X3] :
                  ( k1_funct_1(X1,X3) = k1_funct_1(sK4,X3)
                  | ~ r2_hidden(X3,X2) )
              & k1_relat_1(X1) = k1_relat_1(sK4) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK4)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k7_relat_1(X1,X2) != k7_relat_1(sK4,X2)
            & ! [X3] :
                ( k1_funct_1(X1,X3) = k1_funct_1(sK4,X3)
                | ~ r2_hidden(X3,X2) )
            & k1_relat_1(X1) = k1_relat_1(sK4) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( k7_relat_1(sK4,X2) != k7_relat_1(sK5,X2)
          & ! [X3] :
              ( k1_funct_1(sK4,X3) = k1_funct_1(sK5,X3)
              | ~ r2_hidden(X3,X2) )
          & k1_relat_1(sK4) = k1_relat_1(sK5) )
      & v1_funct_1(sK5)
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X2] :
        ( k7_relat_1(sK4,X2) != k7_relat_1(sK5,X2)
        & ! [X3] :
            ( k1_funct_1(sK4,X3) = k1_funct_1(sK5,X3)
            | ~ r2_hidden(X3,X2) )
        & k1_relat_1(sK4) = k1_relat_1(sK5) )
   => ( k7_relat_1(sK4,sK6) != k7_relat_1(sK5,sK6)
      & ! [X3] :
          ( k1_funct_1(sK4,X3) = k1_funct_1(sK5,X3)
          | ~ r2_hidden(X3,sK6) )
      & k1_relat_1(sK4) = k1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
              & ! [X3] :
                  ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,X2) )
              & k1_relat_1(X1) = k1_relat_1(X0) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
              & ! [X3] :
                  ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,X2) )
              & k1_relat_1(X1) = k1_relat_1(X0) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( ! [X3] :
                      ( r2_hidden(X3,X2)
                     => k1_funct_1(X0,X3) = k1_funct_1(X1,X3) )
                  & k1_relat_1(X1) = k1_relat_1(X0) )
               => k7_relat_1(X0,X2) = k7_relat_1(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( ! [X3] :
                    ( r2_hidden(X3,X2)
                   => k1_funct_1(X0,X3) = k1_funct_1(X1,X3) )
                & k1_relat_1(X1) = k1_relat_1(X0) )
             => k7_relat_1(X0,X2) = k7_relat_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_funct_1)).

fof(f1120,plain,(
    r2_hidden(sK8(sK5,sK4,k1_relat_1(k7_relat_1(sK4,sK6))),sK6) ),
    inference(unit_resulting_resolution,[],[f1051,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ~ r2_hidden(X1,k1_relat_1(X0))
        | ~ r2_hidden(X1,X2) )
      & ( ( r2_hidden(X1,k1_relat_1(X0))
          & r2_hidden(X1,X2) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ( sP2(X2,X0,X1)
        | ~ r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(X0,X1) )
      & ( ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) )
        | ~ sP2(X2,X0,X1) ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ( sP2(X2,X0,X1)
        | ~ r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(X0,X1) )
      & ( ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) )
        | ~ sP2(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( sP2(X2,X0,X1)
    <=> ( r2_hidden(X0,k1_relat_1(X2))
        & r2_hidden(X0,X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f1051,plain,(
    sP2(sK5,sK8(sK5,sK4,k1_relat_1(k7_relat_1(sK4,sK6))),sK6) ),
    inference(unit_resulting_resolution,[],[f85,f871,f281])).

fof(f281,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,k1_relat_1(k7_relat_1(sK4,X4)))
      | sP2(sK5,X5,X4)
      | ~ sP3(X4,X5,sK5) ) ),
    inference(superposition,[],[f64,f155])).

fof(f155,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK4,X0)) = k1_relat_1(k7_relat_1(sK5,X0)) ),
    inference(forward_demodulation,[],[f154,f129])).

fof(f129,plain,(
    ! [X0,X1] : k1_relat_1(k7_relat_1(sK7(X0,X1),k1_relat_1(sK4))) = k1_relat_1(k7_relat_1(sK4,X0)) ),
    inference(forward_demodulation,[],[f128,f83])).

fof(f83,plain,(
    ! [X0,X1] : k7_relat_1(sK7(X0,X1),k1_relat_1(sK4)) = k7_relat_1(sK7(X0,X1),k1_relat_1(k7_relat_1(sK4,X0))) ),
    inference(forward_demodulation,[],[f78,f56])).

fof(f56,plain,(
    ! [X0,X1] : k1_relat_1(sK7(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK7(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK7(X0,X1)) = X0
      & v1_funct_1(sK7(X0,X1))
      & v1_relat_1(sK7(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f13,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X2,X3) = X1
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( k1_funct_1(sK7(X0,X1),X3) = X1
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(sK7(X0,X1)) = X0
        & v1_funct_1(sK7(X0,X1))
        & v1_relat_1(sK7(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f78,plain,(
    ! [X0,X1] : k7_relat_1(sK7(X0,X1),k1_relat_1(sK4)) = k7_relat_1(sK7(X0,X1),k1_relat_1(k7_relat_1(sK4,k1_relat_1(sK7(X0,X1))))) ),
    inference(unit_resulting_resolution,[],[f54,f47,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_relat_1)).

fof(f47,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f54,plain,(
    ! [X0,X1] : v1_relat_1(sK7(X0,X1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f128,plain,(
    ! [X0,X1] : k1_relat_1(k7_relat_1(sK4,X0)) = k1_relat_1(k7_relat_1(sK7(X0,X1),k1_relat_1(k7_relat_1(sK4,X0)))) ),
    inference(forward_demodulation,[],[f110,f56])).

fof(f110,plain,(
    ! [X0,X1] : k1_relat_1(k7_relat_1(sK4,k1_relat_1(sK7(X0,X1)))) = k1_relat_1(k7_relat_1(sK7(X0,X1),k1_relat_1(k7_relat_1(sK4,k1_relat_1(sK7(X0,X1)))))) ),
    inference(unit_resulting_resolution,[],[f54,f81,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f81,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK4,X0)),X0) ),
    inference(unit_resulting_resolution,[],[f47,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f154,plain,(
    ! [X0,X1] : k1_relat_1(k7_relat_1(sK7(X0,X1),k1_relat_1(sK4))) = k1_relat_1(k7_relat_1(sK5,X0)) ),
    inference(forward_demodulation,[],[f153,f99])).

fof(f99,plain,(
    ! [X0,X1] : k7_relat_1(sK7(X0,X1),k1_relat_1(sK4)) = k7_relat_1(sK7(X0,X1),k1_relat_1(k7_relat_1(sK5,X0))) ),
    inference(forward_demodulation,[],[f98,f51])).

fof(f51,plain,(
    k1_relat_1(sK4) = k1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f33])).

fof(f98,plain,(
    ! [X0,X1] : k7_relat_1(sK7(X0,X1),k1_relat_1(sK5)) = k7_relat_1(sK7(X0,X1),k1_relat_1(k7_relat_1(sK5,X0))) ),
    inference(forward_demodulation,[],[f89,f56])).

fof(f89,plain,(
    ! [X0,X1] : k7_relat_1(sK7(X0,X1),k1_relat_1(sK5)) = k7_relat_1(sK7(X0,X1),k1_relat_1(k7_relat_1(sK5,k1_relat_1(sK7(X0,X1))))) ),
    inference(unit_resulting_resolution,[],[f54,f49,f70])).

fof(f49,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f33])).

fof(f153,plain,(
    ! [X0,X1] : k1_relat_1(k7_relat_1(sK5,X0)) = k1_relat_1(k7_relat_1(sK7(X0,X1),k1_relat_1(k7_relat_1(sK5,X0)))) ),
    inference(forward_demodulation,[],[f131,f56])).

fof(f131,plain,(
    ! [X0,X1] : k1_relat_1(k7_relat_1(sK5,k1_relat_1(sK7(X0,X1)))) = k1_relat_1(k7_relat_1(sK7(X0,X1),k1_relat_1(k7_relat_1(sK5,k1_relat_1(sK7(X0,X1)))))) ),
    inference(unit_resulting_resolution,[],[f54,f93,f72])).

fof(f93,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK5,X0)),X0) ),
    inference(unit_resulting_resolution,[],[f49,f74])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X0)))
      | sP2(X2,X1,X0)
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X0)))
          | ~ sP2(X2,X1,X0) )
        & ( sP2(X2,X1,X0)
          | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X0))) ) )
      | ~ sP3(X0,X1,X2) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X1,X0,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ sP2(X2,X0,X1) )
        & ( sP2(X2,X0,X1)
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ sP3(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X1,X0,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> sP2(X2,X0,X1) )
      | ~ sP3(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f871,plain,(
    r2_hidden(sK8(sK5,sK4,k1_relat_1(k7_relat_1(sK4,sK6))),k1_relat_1(k7_relat_1(sK4,sK6))) ),
    inference(unit_resulting_resolution,[],[f858,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK8(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( k1_funct_1(X0,sK8(X0,X1,X2)) != k1_funct_1(X1,sK8(X0,X1,X2))
          & r2_hidden(sK8(X0,X1,X2),X2) ) )
      & ( ! [X4] :
            ( k1_funct_1(X1,X4) = k1_funct_1(X0,X4)
            | ~ r2_hidden(X4,X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f39,f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
          & r2_hidden(X3,X2) )
     => ( k1_funct_1(X0,sK8(X0,X1,X2)) != k1_funct_1(X1,sK8(X0,X1,X2))
        & r2_hidden(sK8(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
            & r2_hidden(X3,X2) ) )
      & ( ! [X4] :
            ( k1_funct_1(X1,X4) = k1_funct_1(X0,X4)
            | ~ r2_hidden(X4,X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
            & r2_hidden(X3,X2) ) )
      & ( ! [X3] :
            ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X2) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
          | ~ r2_hidden(X3,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f858,plain,(
    ~ sP0(sK5,sK4,k1_relat_1(k7_relat_1(sK4,sK6))) ),
    inference(unit_resulting_resolution,[],[f53,f522])).

fof(f522,plain,(
    ! [X0] :
      ( ~ sP0(sK5,sK4,k1_relat_1(k7_relat_1(sK4,X0)))
      | k7_relat_1(sK4,X0) = k7_relat_1(sK5,X0) ) ),
    inference(forward_demodulation,[],[f521,f474])).

fof(f474,plain,(
    ! [X2] : k7_relat_1(sK4,X2) = k7_relat_1(sK4,k1_relat_1(k7_relat_1(sK4,X2))) ),
    inference(superposition,[],[f84,f129])).

fof(f84,plain,(
    ! [X0,X1] : k7_relat_1(sK4,k1_relat_1(k7_relat_1(sK7(X0,X1),k1_relat_1(sK4)))) = k7_relat_1(sK4,X0) ),
    inference(forward_demodulation,[],[f76,f56])).

fof(f76,plain,(
    ! [X0,X1] : k7_relat_1(sK4,k1_relat_1(sK7(X0,X1))) = k7_relat_1(sK4,k1_relat_1(k7_relat_1(sK7(X0,X1),k1_relat_1(sK4)))) ),
    inference(unit_resulting_resolution,[],[f54,f47,f70])).

fof(f521,plain,(
    ! [X0] :
      ( k7_relat_1(sK5,X0) = k7_relat_1(sK4,k1_relat_1(k7_relat_1(sK4,X0)))
      | ~ sP0(sK5,sK4,k1_relat_1(k7_relat_1(sK4,X0))) ) ),
    inference(forward_demodulation,[],[f517,f473])).

fof(f473,plain,(
    ! [X0] : k7_relat_1(sK5,X0) = k7_relat_1(sK5,k1_relat_1(k7_relat_1(sK4,X0))) ),
    inference(superposition,[],[f103,f129])).

fof(f103,plain,(
    ! [X0,X1] : k7_relat_1(sK5,X0) = k7_relat_1(sK5,k1_relat_1(k7_relat_1(sK7(X0,X1),k1_relat_1(sK4)))) ),
    inference(forward_demodulation,[],[f102,f56])).

fof(f102,plain,(
    ! [X0,X1] : k7_relat_1(sK5,k1_relat_1(sK7(X0,X1))) = k7_relat_1(sK5,k1_relat_1(k7_relat_1(sK7(X0,X1),k1_relat_1(sK4)))) ),
    inference(forward_demodulation,[],[f86,f51])).

fof(f86,plain,(
    ! [X0,X1] : k7_relat_1(sK5,k1_relat_1(sK7(X0,X1))) = k7_relat_1(sK5,k1_relat_1(k7_relat_1(sK7(X0,X1),k1_relat_1(sK5)))) ),
    inference(unit_resulting_resolution,[],[f54,f49,f70])).

fof(f517,plain,(
    ! [X0] :
      ( ~ sP0(sK5,sK4,k1_relat_1(k7_relat_1(sK4,X0)))
      | k7_relat_1(sK4,k1_relat_1(k7_relat_1(sK4,X0))) = k7_relat_1(sK5,k1_relat_1(k7_relat_1(sK4,X0))) ) ),
    inference(resolution,[],[f510,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | k7_relat_1(X1,X0) = k7_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( k7_relat_1(X1,X0) = k7_relat_1(X2,X0)
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | k7_relat_1(X1,X0) != k7_relat_1(X2,X0) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
          | ~ sP0(X1,X0,X2) )
        & ( sP0(X1,X0,X2)
          | k7_relat_1(X0,X2) != k7_relat_1(X1,X2) ) )
      | ~ sP1(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
      <=> sP0(X1,X0,X2) )
      | ~ sP1(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f510,plain,(
    ! [X0] : sP1(k1_relat_1(k7_relat_1(sK4,X0)),sK4,sK5) ),
    inference(forward_demodulation,[],[f489,f155])).

fof(f489,plain,(
    ! [X0] : sP1(k1_relat_1(k7_relat_1(sK5,X0)),sK4,sK5) ),
    inference(unit_resulting_resolution,[],[f47,f48,f49,f50,f95,f95,f109])).

fof(f109,plain,(
    ! [X6,X5] :
      ( ~ r1_tarski(X5,k1_relat_1(sK4))
      | sP1(X5,X6,sK5)
      | ~ r1_tarski(X5,k1_relat_1(X6))
      | ~ v1_funct_1(sK5)
      | ~ v1_relat_1(sK5)
      | ~ v1_funct_1(X6)
      | ~ v1_relat_1(X6) ) ),
    inference(superposition,[],[f63,f51])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k1_relat_1(X1))
      | sP1(X2,X0,X1)
      | ~ r1_tarski(X2,k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X2,X0,X1)
              | ~ r1_tarski(X2,k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(X0)) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f15,f25,f24])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
              <=> ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,X2) ) )
              | ~ r1_tarski(X2,k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(X0)) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
              <=> ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,X2) ) )
              | ~ r1_tarski(X2,k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(X0)) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( r1_tarski(X2,k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) )
             => ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
              <=> ! [X3] :
                    ( r2_hidden(X3,X2)
                   => k1_funct_1(X0,X3) = k1_funct_1(X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t165_funct_1)).

fof(f95,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK5,X0)),k1_relat_1(sK4)) ),
    inference(forward_demodulation,[],[f92,f51])).

fof(f92,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK5,X0)),k1_relat_1(sK5)) ),
    inference(unit_resulting_resolution,[],[f49,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).

fof(f50,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f33])).

fof(f48,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f53,plain,(
    k7_relat_1(sK4,sK6) != k7_relat_1(sK5,sK6) ),
    inference(cnf_transformation,[],[f33])).

fof(f85,plain,(
    ! [X0,X1] : sP3(X0,X1,sK5) ),
    inference(unit_resulting_resolution,[],[f49,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( sP3(X1,X0,X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( sP3(X1,X0,X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_folding,[],[f16,f28,f27])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

fof(f872,plain,(
    k1_funct_1(sK5,sK8(sK5,sK4,k1_relat_1(k7_relat_1(sK4,sK6)))) != k1_funct_1(sK4,sK8(sK5,sK4,k1_relat_1(k7_relat_1(sK4,sK6)))) ),
    inference(unit_resulting_resolution,[],[f858,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,sK8(X0,X1,X2)) != k1_funct_1(X1,sK8(X0,X1,X2))
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:29:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.49  % (13273)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.50  % (13265)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.51  % (13261)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.51  % (13280)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.52  % (13275)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.52  % (13270)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.52  % (13264)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (13277)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.52  % (13278)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.52  % (13267)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.52  % (13276)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.52  % (13262)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.52  % (13272)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.52  % (13259)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.52  % (13274)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.53  % (13266)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.53  % (13257)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.53  % (13268)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.53  % (13269)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.53  % (13258)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.53  % (13260)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.53  % (13271)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.54  % (13279)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.54  % (13280)Refutation not found, incomplete strategy% (13280)------------------------------
% 0.22/0.54  % (13280)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (13280)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (13280)Memory used [KB]: 10618
% 0.22/0.54  % (13280)Time elapsed: 0.120 s
% 0.22/0.54  % (13280)------------------------------
% 0.22/0.54  % (13280)------------------------------
% 0.22/0.56  % (13263)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 1.52/0.57  % (13273)Refutation found. Thanks to Tanya!
% 1.52/0.57  % SZS status Theorem for theBenchmark
% 1.52/0.57  % SZS output start Proof for theBenchmark
% 1.52/0.57  fof(f1178,plain,(
% 1.52/0.57    $false),
% 1.52/0.57    inference(subsumption_resolution,[],[f872,f1170])).
% 1.52/0.57  fof(f1170,plain,(
% 1.52/0.57    k1_funct_1(sK5,sK8(sK5,sK4,k1_relat_1(k7_relat_1(sK4,sK6)))) = k1_funct_1(sK4,sK8(sK5,sK4,k1_relat_1(k7_relat_1(sK4,sK6))))),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f1120,f52])).
% 1.52/0.57  fof(f52,plain,(
% 1.52/0.57    ( ! [X3] : (~r2_hidden(X3,sK6) | k1_funct_1(sK4,X3) = k1_funct_1(sK5,X3)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f33])).
% 1.52/0.57  fof(f33,plain,(
% 1.52/0.57    ((k7_relat_1(sK4,sK6) != k7_relat_1(sK5,sK6) & ! [X3] : (k1_funct_1(sK4,X3) = k1_funct_1(sK5,X3) | ~r2_hidden(X3,sK6)) & k1_relat_1(sK4) = k1_relat_1(sK5)) & v1_funct_1(sK5) & v1_relat_1(sK5)) & v1_funct_1(sK4) & v1_relat_1(sK4)),
% 1.52/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f12,f32,f31,f30])).
% 1.52/0.57  fof(f30,plain,(
% 1.52/0.57    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (k7_relat_1(X1,X2) != k7_relat_1(sK4,X2) & ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(sK4,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(sK4)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK4) & v1_relat_1(sK4))),
% 1.52/0.57    introduced(choice_axiom,[])).
% 1.52/0.57  fof(f31,plain,(
% 1.52/0.57    ? [X1] : (? [X2] : (k7_relat_1(X1,X2) != k7_relat_1(sK4,X2) & ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(sK4,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(sK4)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (k7_relat_1(sK4,X2) != k7_relat_1(sK5,X2) & ! [X3] : (k1_funct_1(sK4,X3) = k1_funct_1(sK5,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(sK4) = k1_relat_1(sK5)) & v1_funct_1(sK5) & v1_relat_1(sK5))),
% 1.52/0.57    introduced(choice_axiom,[])).
% 1.52/0.57  fof(f32,plain,(
% 1.52/0.57    ? [X2] : (k7_relat_1(sK4,X2) != k7_relat_1(sK5,X2) & ! [X3] : (k1_funct_1(sK4,X3) = k1_funct_1(sK5,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(sK4) = k1_relat_1(sK5)) => (k7_relat_1(sK4,sK6) != k7_relat_1(sK5,sK6) & ! [X3] : (k1_funct_1(sK4,X3) = k1_funct_1(sK5,X3) | ~r2_hidden(X3,sK6)) & k1_relat_1(sK4) = k1_relat_1(sK5))),
% 1.52/0.57    introduced(choice_axiom,[])).
% 1.52/0.57  fof(f12,plain,(
% 1.52/0.57    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.52/0.57    inference(flattening,[],[f11])).
% 1.52/0.57  fof(f11,plain,(
% 1.52/0.57    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.52/0.57    inference(ennf_transformation,[],[f10])).
% 1.52/0.57  fof(f10,negated_conjecture,(
% 1.52/0.57    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3)) & k1_relat_1(X1) = k1_relat_1(X0)) => k7_relat_1(X0,X2) = k7_relat_1(X1,X2))))),
% 1.52/0.57    inference(negated_conjecture,[],[f9])).
% 1.52/0.57  fof(f9,conjecture,(
% 1.52/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3)) & k1_relat_1(X1) = k1_relat_1(X0)) => k7_relat_1(X0,X2) = k7_relat_1(X1,X2))))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_funct_1)).
% 1.52/0.57  fof(f1120,plain,(
% 1.52/0.57    r2_hidden(sK8(sK5,sK4,k1_relat_1(k7_relat_1(sK4,sK6))),sK6)),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f1051,f66])).
% 1.52/0.57  fof(f66,plain,(
% 1.52/0.57    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | r2_hidden(X1,X2)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f46])).
% 1.52/0.57  fof(f46,plain,(
% 1.52/0.57    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ~r2_hidden(X1,k1_relat_1(X0)) | ~r2_hidden(X1,X2)) & ((r2_hidden(X1,k1_relat_1(X0)) & r2_hidden(X1,X2)) | ~sP2(X0,X1,X2)))),
% 1.52/0.57    inference(rectify,[],[f45])).
% 1.52/0.57  fof(f45,plain,(
% 1.52/0.57    ! [X2,X0,X1] : ((sP2(X2,X0,X1) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~sP2(X2,X0,X1)))),
% 1.52/0.57    inference(flattening,[],[f44])).
% 1.52/0.57  fof(f44,plain,(
% 1.52/0.57    ! [X2,X0,X1] : ((sP2(X2,X0,X1) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~sP2(X2,X0,X1)))),
% 1.52/0.57    inference(nnf_transformation,[],[f27])).
% 1.52/0.57  fof(f27,plain,(
% 1.52/0.57    ! [X2,X0,X1] : (sP2(X2,X0,X1) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)))),
% 1.52/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.52/0.57  fof(f1051,plain,(
% 1.52/0.57    sP2(sK5,sK8(sK5,sK4,k1_relat_1(k7_relat_1(sK4,sK6))),sK6)),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f85,f871,f281])).
% 1.52/0.57  fof(f281,plain,(
% 1.52/0.57    ( ! [X4,X5] : (~r2_hidden(X5,k1_relat_1(k7_relat_1(sK4,X4))) | sP2(sK5,X5,X4) | ~sP3(X4,X5,sK5)) )),
% 1.52/0.57    inference(superposition,[],[f64,f155])).
% 1.52/0.57  fof(f155,plain,(
% 1.52/0.57    ( ! [X0] : (k1_relat_1(k7_relat_1(sK4,X0)) = k1_relat_1(k7_relat_1(sK5,X0))) )),
% 1.52/0.57    inference(forward_demodulation,[],[f154,f129])).
% 1.52/0.57  fof(f129,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(sK7(X0,X1),k1_relat_1(sK4))) = k1_relat_1(k7_relat_1(sK4,X0))) )),
% 1.52/0.57    inference(forward_demodulation,[],[f128,f83])).
% 1.52/0.57  fof(f83,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k7_relat_1(sK7(X0,X1),k1_relat_1(sK4)) = k7_relat_1(sK7(X0,X1),k1_relat_1(k7_relat_1(sK4,X0)))) )),
% 1.52/0.57    inference(forward_demodulation,[],[f78,f56])).
% 1.52/0.57  fof(f56,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k1_relat_1(sK7(X0,X1)) = X0) )),
% 1.52/0.57    inference(cnf_transformation,[],[f35])).
% 1.52/0.57  fof(f35,plain,(
% 1.52/0.57    ! [X0,X1] : (! [X3] : (k1_funct_1(sK7(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK7(X0,X1)) = X0 & v1_funct_1(sK7(X0,X1)) & v1_relat_1(sK7(X0,X1)))),
% 1.52/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f13,f34])).
% 1.52/0.57  fof(f34,plain,(
% 1.52/0.57    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK7(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK7(X0,X1)) = X0 & v1_funct_1(sK7(X0,X1)) & v1_relat_1(sK7(X0,X1))))),
% 1.52/0.57    introduced(choice_axiom,[])).
% 1.52/0.57  fof(f13,plain,(
% 1.52/0.57    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.52/0.57    inference(ennf_transformation,[],[f7])).
% 1.52/0.57  fof(f7,axiom,(
% 1.52/0.57    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 1.52/0.57  fof(f78,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k7_relat_1(sK7(X0,X1),k1_relat_1(sK4)) = k7_relat_1(sK7(X0,X1),k1_relat_1(k7_relat_1(sK4,k1_relat_1(sK7(X0,X1)))))) )),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f54,f47,f70])).
% 1.52/0.57  fof(f70,plain,(
% 1.52/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) | ~v1_relat_1(X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f17])).
% 1.52/0.57  fof(f17,plain,(
% 1.52/0.57    ! [X0] : (! [X1] : (k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.52/0.57    inference(ennf_transformation,[],[f1])).
% 1.52/0.57  fof(f1,axiom,(
% 1.52/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_relat_1)).
% 1.52/0.57  fof(f47,plain,(
% 1.52/0.57    v1_relat_1(sK4)),
% 1.52/0.57    inference(cnf_transformation,[],[f33])).
% 1.52/0.57  fof(f54,plain,(
% 1.52/0.57    ( ! [X0,X1] : (v1_relat_1(sK7(X0,X1))) )),
% 1.52/0.57    inference(cnf_transformation,[],[f35])).
% 1.52/0.57  fof(f128,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(sK4,X0)) = k1_relat_1(k7_relat_1(sK7(X0,X1),k1_relat_1(k7_relat_1(sK4,X0))))) )),
% 1.52/0.57    inference(forward_demodulation,[],[f110,f56])).
% 1.52/0.57  fof(f110,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(sK4,k1_relat_1(sK7(X0,X1)))) = k1_relat_1(k7_relat_1(sK7(X0,X1),k1_relat_1(k7_relat_1(sK4,k1_relat_1(sK7(X0,X1))))))) )),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f54,f81,f72])).
% 1.52/0.57  fof(f72,plain,(
% 1.52/0.57    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f21])).
% 1.52/0.57  fof(f21,plain,(
% 1.52/0.57    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.52/0.57    inference(flattening,[],[f20])).
% 1.52/0.57  fof(f20,plain,(
% 1.52/0.57    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.52/0.57    inference(ennf_transformation,[],[f5])).
% 1.52/0.57  fof(f5,axiom,(
% 1.52/0.57    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 1.52/0.57  fof(f81,plain,(
% 1.52/0.57    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK4,X0)),X0)) )),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f47,f74])).
% 1.52/0.57  fof(f74,plain,(
% 1.52/0.57    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f23])).
% 1.52/0.57  fof(f23,plain,(
% 1.52/0.57    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 1.52/0.57    inference(ennf_transformation,[],[f3])).
% 1.52/0.57  fof(f3,axiom,(
% 1.52/0.57    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 1.52/0.57  fof(f154,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(sK7(X0,X1),k1_relat_1(sK4))) = k1_relat_1(k7_relat_1(sK5,X0))) )),
% 1.52/0.57    inference(forward_demodulation,[],[f153,f99])).
% 1.52/0.57  fof(f99,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k7_relat_1(sK7(X0,X1),k1_relat_1(sK4)) = k7_relat_1(sK7(X0,X1),k1_relat_1(k7_relat_1(sK5,X0)))) )),
% 1.52/0.57    inference(forward_demodulation,[],[f98,f51])).
% 1.52/0.57  fof(f51,plain,(
% 1.52/0.57    k1_relat_1(sK4) = k1_relat_1(sK5)),
% 1.52/0.57    inference(cnf_transformation,[],[f33])).
% 1.52/0.57  fof(f98,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k7_relat_1(sK7(X0,X1),k1_relat_1(sK5)) = k7_relat_1(sK7(X0,X1),k1_relat_1(k7_relat_1(sK5,X0)))) )),
% 1.52/0.57    inference(forward_demodulation,[],[f89,f56])).
% 1.52/0.57  fof(f89,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k7_relat_1(sK7(X0,X1),k1_relat_1(sK5)) = k7_relat_1(sK7(X0,X1),k1_relat_1(k7_relat_1(sK5,k1_relat_1(sK7(X0,X1)))))) )),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f54,f49,f70])).
% 1.52/0.57  fof(f49,plain,(
% 1.52/0.57    v1_relat_1(sK5)),
% 1.52/0.57    inference(cnf_transformation,[],[f33])).
% 1.52/0.57  fof(f153,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(sK5,X0)) = k1_relat_1(k7_relat_1(sK7(X0,X1),k1_relat_1(k7_relat_1(sK5,X0))))) )),
% 1.52/0.57    inference(forward_demodulation,[],[f131,f56])).
% 1.52/0.57  fof(f131,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(sK5,k1_relat_1(sK7(X0,X1)))) = k1_relat_1(k7_relat_1(sK7(X0,X1),k1_relat_1(k7_relat_1(sK5,k1_relat_1(sK7(X0,X1))))))) )),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f54,f93,f72])).
% 1.52/0.57  fof(f93,plain,(
% 1.52/0.57    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK5,X0)),X0)) )),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f49,f74])).
% 1.52/0.57  fof(f64,plain,(
% 1.52/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X0))) | sP2(X2,X1,X0) | ~sP3(X0,X1,X2)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f43])).
% 1.52/0.57  fof(f43,plain,(
% 1.52/0.57    ! [X0,X1,X2] : (((r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X0))) | ~sP2(X2,X1,X0)) & (sP2(X2,X1,X0) | ~r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X0))))) | ~sP3(X0,X1,X2))),
% 1.52/0.57    inference(rectify,[],[f42])).
% 1.52/0.57  fof(f42,plain,(
% 1.52/0.57    ! [X1,X0,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~sP2(X2,X0,X1)) & (sP2(X2,X0,X1) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~sP3(X1,X0,X2))),
% 1.52/0.57    inference(nnf_transformation,[],[f28])).
% 1.52/0.57  fof(f28,plain,(
% 1.52/0.57    ! [X1,X0,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> sP2(X2,X0,X1)) | ~sP3(X1,X0,X2))),
% 1.52/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 1.52/0.57  fof(f871,plain,(
% 1.52/0.57    r2_hidden(sK8(sK5,sK4,k1_relat_1(k7_relat_1(sK4,sK6))),k1_relat_1(k7_relat_1(sK4,sK6)))),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f858,f61])).
% 1.52/0.57  fof(f61,plain,(
% 1.52/0.57    ( ! [X2,X0,X1] : (r2_hidden(sK8(X0,X1,X2),X2) | sP0(X0,X1,X2)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f41])).
% 1.52/0.57  fof(f41,plain,(
% 1.52/0.57    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (k1_funct_1(X0,sK8(X0,X1,X2)) != k1_funct_1(X1,sK8(X0,X1,X2)) & r2_hidden(sK8(X0,X1,X2),X2))) & (! [X4] : (k1_funct_1(X1,X4) = k1_funct_1(X0,X4) | ~r2_hidden(X4,X2)) | ~sP0(X0,X1,X2)))),
% 1.52/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f39,f40])).
% 1.52/0.57  fof(f40,plain,(
% 1.52/0.57    ! [X2,X1,X0] : (? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2)) => (k1_funct_1(X0,sK8(X0,X1,X2)) != k1_funct_1(X1,sK8(X0,X1,X2)) & r2_hidden(sK8(X0,X1,X2),X2)))),
% 1.52/0.57    introduced(choice_axiom,[])).
% 1.52/0.57  fof(f39,plain,(
% 1.52/0.57    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2))) & (! [X4] : (k1_funct_1(X1,X4) = k1_funct_1(X0,X4) | ~r2_hidden(X4,X2)) | ~sP0(X0,X1,X2)))),
% 1.52/0.57    inference(rectify,[],[f38])).
% 1.52/0.57  fof(f38,plain,(
% 1.52/0.57    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2))) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) | ~sP0(X1,X0,X2)))),
% 1.52/0.57    inference(nnf_transformation,[],[f24])).
% 1.52/0.57  fof(f24,plain,(
% 1.52/0.57    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)))),
% 1.52/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.52/0.57  fof(f858,plain,(
% 1.52/0.57    ~sP0(sK5,sK4,k1_relat_1(k7_relat_1(sK4,sK6)))),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f53,f522])).
% 1.52/0.57  fof(f522,plain,(
% 1.52/0.57    ( ! [X0] : (~sP0(sK5,sK4,k1_relat_1(k7_relat_1(sK4,X0))) | k7_relat_1(sK4,X0) = k7_relat_1(sK5,X0)) )),
% 1.52/0.57    inference(forward_demodulation,[],[f521,f474])).
% 1.52/0.57  fof(f474,plain,(
% 1.52/0.57    ( ! [X2] : (k7_relat_1(sK4,X2) = k7_relat_1(sK4,k1_relat_1(k7_relat_1(sK4,X2)))) )),
% 1.52/0.57    inference(superposition,[],[f84,f129])).
% 1.52/0.57  fof(f84,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k7_relat_1(sK4,k1_relat_1(k7_relat_1(sK7(X0,X1),k1_relat_1(sK4)))) = k7_relat_1(sK4,X0)) )),
% 1.52/0.57    inference(forward_demodulation,[],[f76,f56])).
% 1.52/0.57  fof(f76,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k7_relat_1(sK4,k1_relat_1(sK7(X0,X1))) = k7_relat_1(sK4,k1_relat_1(k7_relat_1(sK7(X0,X1),k1_relat_1(sK4))))) )),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f54,f47,f70])).
% 1.52/0.57  fof(f521,plain,(
% 1.52/0.57    ( ! [X0] : (k7_relat_1(sK5,X0) = k7_relat_1(sK4,k1_relat_1(k7_relat_1(sK4,X0))) | ~sP0(sK5,sK4,k1_relat_1(k7_relat_1(sK4,X0)))) )),
% 1.52/0.57    inference(forward_demodulation,[],[f517,f473])).
% 1.52/0.57  fof(f473,plain,(
% 1.52/0.57    ( ! [X0] : (k7_relat_1(sK5,X0) = k7_relat_1(sK5,k1_relat_1(k7_relat_1(sK4,X0)))) )),
% 1.52/0.57    inference(superposition,[],[f103,f129])).
% 1.52/0.57  fof(f103,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k7_relat_1(sK5,X0) = k7_relat_1(sK5,k1_relat_1(k7_relat_1(sK7(X0,X1),k1_relat_1(sK4))))) )),
% 1.52/0.57    inference(forward_demodulation,[],[f102,f56])).
% 1.52/0.57  fof(f102,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k7_relat_1(sK5,k1_relat_1(sK7(X0,X1))) = k7_relat_1(sK5,k1_relat_1(k7_relat_1(sK7(X0,X1),k1_relat_1(sK4))))) )),
% 1.52/0.57    inference(forward_demodulation,[],[f86,f51])).
% 1.52/0.57  fof(f86,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k7_relat_1(sK5,k1_relat_1(sK7(X0,X1))) = k7_relat_1(sK5,k1_relat_1(k7_relat_1(sK7(X0,X1),k1_relat_1(sK5))))) )),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f54,f49,f70])).
% 1.52/0.57  fof(f517,plain,(
% 1.52/0.57    ( ! [X0] : (~sP0(sK5,sK4,k1_relat_1(k7_relat_1(sK4,X0))) | k7_relat_1(sK4,k1_relat_1(k7_relat_1(sK4,X0))) = k7_relat_1(sK5,k1_relat_1(k7_relat_1(sK4,X0)))) )),
% 1.52/0.57    inference(resolution,[],[f510,f59])).
% 1.52/0.57  fof(f59,plain,(
% 1.52/0.57    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | k7_relat_1(X1,X0) = k7_relat_1(X2,X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f37])).
% 1.52/0.57  fof(f37,plain,(
% 1.52/0.57    ! [X0,X1,X2] : (((k7_relat_1(X1,X0) = k7_relat_1(X2,X0) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | k7_relat_1(X1,X0) != k7_relat_1(X2,X0))) | ~sP1(X0,X1,X2))),
% 1.52/0.57    inference(rectify,[],[f36])).
% 1.52/0.57  fof(f36,plain,(
% 1.52/0.57    ! [X2,X0,X1] : (((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2))) | ~sP1(X2,X0,X1))),
% 1.52/0.57    inference(nnf_transformation,[],[f25])).
% 1.52/0.57  fof(f25,plain,(
% 1.52/0.57    ! [X2,X0,X1] : ((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> sP0(X1,X0,X2)) | ~sP1(X2,X0,X1))),
% 1.52/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.52/0.57  fof(f510,plain,(
% 1.52/0.57    ( ! [X0] : (sP1(k1_relat_1(k7_relat_1(sK4,X0)),sK4,sK5)) )),
% 1.52/0.57    inference(forward_demodulation,[],[f489,f155])).
% 1.52/0.57  fof(f489,plain,(
% 1.52/0.57    ( ! [X0] : (sP1(k1_relat_1(k7_relat_1(sK5,X0)),sK4,sK5)) )),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f47,f48,f49,f50,f95,f95,f109])).
% 1.52/0.57  fof(f109,plain,(
% 1.52/0.57    ( ! [X6,X5] : (~r1_tarski(X5,k1_relat_1(sK4)) | sP1(X5,X6,sK5) | ~r1_tarski(X5,k1_relat_1(X6)) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | ~v1_funct_1(X6) | ~v1_relat_1(X6)) )),
% 1.52/0.57    inference(superposition,[],[f63,f51])).
% 1.52/0.57  fof(f63,plain,(
% 1.52/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X2,k1_relat_1(X1)) | sP1(X2,X0,X1) | ~r1_tarski(X2,k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f26])).
% 1.52/0.57  fof(f26,plain,(
% 1.52/0.57    ! [X0] : (! [X1] : (! [X2] : (sP1(X2,X0,X1) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.52/0.57    inference(definition_folding,[],[f15,f25,f24])).
% 1.52/0.57  fof(f15,plain,(
% 1.52/0.57    ! [X0] : (! [X1] : (! [X2] : ((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.52/0.57    inference(flattening,[],[f14])).
% 1.52/0.57  fof(f14,plain,(
% 1.52/0.57    ! [X0] : (! [X1] : (! [X2] : ((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2))) | (~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.52/0.57    inference(ennf_transformation,[],[f8])).
% 1.52/0.57  fof(f8,axiom,(
% 1.52/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) => (k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3))))))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t165_funct_1)).
% 1.52/0.57  fof(f95,plain,(
% 1.52/0.57    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK5,X0)),k1_relat_1(sK4))) )),
% 1.52/0.57    inference(forward_demodulation,[],[f92,f51])).
% 1.52/0.57  fof(f92,plain,(
% 1.52/0.57    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK5,X0)),k1_relat_1(sK5))) )),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f49,f73])).
% 1.52/0.57  fof(f73,plain,(
% 1.52/0.57    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f22])).
% 1.52/0.57  fof(f22,plain,(
% 1.52/0.57    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.52/0.57    inference(ennf_transformation,[],[f4])).
% 1.52/0.57  fof(f4,axiom,(
% 1.52/0.57    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).
% 1.52/0.57  fof(f50,plain,(
% 1.52/0.57    v1_funct_1(sK5)),
% 1.52/0.57    inference(cnf_transformation,[],[f33])).
% 1.52/0.57  fof(f48,plain,(
% 1.52/0.57    v1_funct_1(sK4)),
% 1.52/0.57    inference(cnf_transformation,[],[f33])).
% 1.52/0.57  fof(f53,plain,(
% 1.52/0.57    k7_relat_1(sK4,sK6) != k7_relat_1(sK5,sK6)),
% 1.52/0.57    inference(cnf_transformation,[],[f33])).
% 1.52/0.57  fof(f85,plain,(
% 1.52/0.57    ( ! [X0,X1] : (sP3(X0,X1,sK5)) )),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f49,f69])).
% 1.52/0.57  fof(f69,plain,(
% 1.52/0.57    ( ! [X2,X0,X1] : (sP3(X1,X0,X2) | ~v1_relat_1(X2)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f29])).
% 1.52/0.57  fof(f29,plain,(
% 1.52/0.57    ! [X0,X1,X2] : (sP3(X1,X0,X2) | ~v1_relat_1(X2))),
% 1.52/0.57    inference(definition_folding,[],[f16,f28,f27])).
% 1.52/0.57  fof(f16,plain,(
% 1.52/0.57    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 1.52/0.57    inference(ennf_transformation,[],[f2])).
% 1.52/0.57  fof(f2,axiom,(
% 1.52/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).
% 1.52/0.57  fof(f872,plain,(
% 1.52/0.57    k1_funct_1(sK5,sK8(sK5,sK4,k1_relat_1(k7_relat_1(sK4,sK6)))) != k1_funct_1(sK4,sK8(sK5,sK4,k1_relat_1(k7_relat_1(sK4,sK6))))),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f858,f62])).
% 1.52/0.57  fof(f62,plain,(
% 1.52/0.57    ( ! [X2,X0,X1] : (k1_funct_1(X0,sK8(X0,X1,X2)) != k1_funct_1(X1,sK8(X0,X1,X2)) | sP0(X0,X1,X2)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f41])).
% 1.52/0.57  % SZS output end Proof for theBenchmark
% 1.52/0.57  % (13273)------------------------------
% 1.52/0.57  % (13273)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.57  % (13273)Termination reason: Refutation
% 1.52/0.57  
% 1.52/0.57  % (13273)Memory used [KB]: 2174
% 1.52/0.57  % (13273)Time elapsed: 0.131 s
% 1.52/0.57  % (13273)------------------------------
% 1.52/0.57  % (13273)------------------------------
% 1.58/0.58  % (13256)Success in time 0.204 s
%------------------------------------------------------------------------------
