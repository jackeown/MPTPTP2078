%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0802+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 430 expanded)
%              Number of leaves         :    6 ( 159 expanded)
%              Depth                    :   19
%              Number of atoms          :  362 (3328 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f81,plain,(
    $false ),
    inference(subsumption_resolution,[],[f80,f17])).

fof(f17,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ v2_wellord1(sK1)
    & r3_wellord1(sK0,sK1,sK2)
    & v2_wellord1(sK0)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f12,f11,f10])).

fof(f10,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_wellord1(X1)
                & r3_wellord1(X0,X1,X2)
                & v2_wellord1(X0)
                & v1_funct_1(X2)
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_wellord1(X1)
              & r3_wellord1(sK0,X1,X2)
              & v2_wellord1(sK0)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v2_wellord1(X1)
            & r3_wellord1(sK0,X1,X2)
            & v2_wellord1(sK0)
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ v2_wellord1(sK1)
          & r3_wellord1(sK0,sK1,X2)
          & v2_wellord1(sK0)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X2] :
        ( ~ v2_wellord1(sK1)
        & r3_wellord1(sK0,sK1,X2)
        & v2_wellord1(sK0)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ v2_wellord1(sK1)
      & r3_wellord1(sK0,sK1,sK2)
      & v2_wellord1(sK0)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_wellord1(X1)
              & r3_wellord1(X0,X1,X2)
              & v2_wellord1(X0)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_wellord1(X1)
              & r3_wellord1(X0,X1,X2)
              & v2_wellord1(X0)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( r3_wellord1(X0,X1,X2)
                    & v2_wellord1(X0) )
                 => v2_wellord1(X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( ( r3_wellord1(X0,X1,X2)
                  & v2_wellord1(X0) )
               => v2_wellord1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_wellord1)).

fof(f80,plain,(
    ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f79,f49])).

fof(f49,plain,(
    v1_relat_2(sK1) ),
    inference(subsumption_resolution,[],[f48,f16])).

fof(f16,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f48,plain,
    ( v1_relat_2(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f47,f17])).

fof(f47,plain,
    ( v1_relat_2(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f46,f18])).

fof(f18,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f46,plain,
    ( v1_relat_2(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f45,f19])).

fof(f19,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f45,plain,
    ( v1_relat_2(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f44,f35])).

fof(f35,plain,(
    v1_relat_2(sK0) ),
    inference(subsumption_resolution,[],[f34,f16])).

fof(f34,plain,
    ( v1_relat_2(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f23,f20])).

fof(f20,plain,(
    v2_wellord1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v2_wellord1(X0)
      | v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_wellord1)).

fof(f44,plain,
    ( ~ v1_relat_2(sK0)
    | v1_relat_2(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f29,f21])).

fof(f21,plain,(
    r3_wellord1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_wellord1(X0,X1,X2)
      | ~ v1_relat_2(X0)
      | v1_relat_2(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v1_wellord1(X1)
                  | ~ v1_wellord1(X0) )
                & ( v4_relat_2(X1)
                  | ~ v4_relat_2(X0) )
                & ( v6_relat_2(X1)
                  | ~ v6_relat_2(X0) )
                & ( v8_relat_2(X1)
                  | ~ v8_relat_2(X0) )
                & ( v1_relat_2(X1)
                  | ~ v1_relat_2(X0) ) )
              | ~ r3_wellord1(X0,X1,X2)
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v1_wellord1(X1)
                  | ~ v1_wellord1(X0) )
                & ( v4_relat_2(X1)
                  | ~ v4_relat_2(X0) )
                & ( v6_relat_2(X1)
                  | ~ v6_relat_2(X0) )
                & ( v8_relat_2(X1)
                  | ~ v8_relat_2(X0) )
                & ( v1_relat_2(X1)
                  | ~ v1_relat_2(X0) ) )
              | ~ r3_wellord1(X0,X1,X2)
              | ~ v1_funct_1(X2)
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
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( r3_wellord1(X0,X1,X2)
               => ( ( v1_wellord1(X0)
                   => v1_wellord1(X1) )
                  & ( v4_relat_2(X0)
                   => v4_relat_2(X1) )
                  & ( v6_relat_2(X0)
                   => v6_relat_2(X1) )
                  & ( v8_relat_2(X0)
                   => v8_relat_2(X1) )
                  & ( v1_relat_2(X0)
                   => v1_relat_2(X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_wellord1)).

fof(f79,plain,
    ( ~ v1_relat_2(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f78,f55])).

fof(f55,plain,(
    v8_relat_2(sK1) ),
    inference(subsumption_resolution,[],[f54,f16])).

fof(f54,plain,
    ( v8_relat_2(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f53,f17])).

fof(f53,plain,
    ( v8_relat_2(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f52,f18])).

fof(f52,plain,
    ( v8_relat_2(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f51,f19])).

fof(f51,plain,
    ( v8_relat_2(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f50,f37])).

fof(f37,plain,(
    v8_relat_2(sK0) ),
    inference(subsumption_resolution,[],[f36,f16])).

fof(f36,plain,
    ( v8_relat_2(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f24,f20])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v2_wellord1(X0)
      | v8_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f50,plain,
    ( ~ v8_relat_2(sK0)
    | v8_relat_2(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f30,f21])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_wellord1(X0,X1,X2)
      | ~ v8_relat_2(X0)
      | v8_relat_2(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f78,plain,
    ( ~ v8_relat_2(sK1)
    | ~ v1_relat_2(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f77,f67])).

fof(f67,plain,(
    v4_relat_2(sK1) ),
    inference(subsumption_resolution,[],[f66,f16])).

fof(f66,plain,
    ( v4_relat_2(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f65,f17])).

fof(f65,plain,
    ( v4_relat_2(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f64,f18])).

fof(f64,plain,
    ( v4_relat_2(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f63,f19])).

fof(f63,plain,
    ( v4_relat_2(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f62,f39])).

fof(f39,plain,(
    v4_relat_2(sK0) ),
    inference(subsumption_resolution,[],[f38,f16])).

fof(f38,plain,
    ( v4_relat_2(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f25,f20])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v2_wellord1(X0)
      | v4_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f62,plain,
    ( ~ v4_relat_2(sK0)
    | v4_relat_2(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f32,f21])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_wellord1(X0,X1,X2)
      | ~ v4_relat_2(X0)
      | v4_relat_2(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f77,plain,
    ( ~ v4_relat_2(sK1)
    | ~ v8_relat_2(sK1)
    | ~ v1_relat_2(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f76,f61])).

fof(f61,plain,(
    v6_relat_2(sK1) ),
    inference(subsumption_resolution,[],[f60,f16])).

fof(f60,plain,
    ( v6_relat_2(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f59,f17])).

fof(f59,plain,
    ( v6_relat_2(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f58,f18])).

fof(f58,plain,
    ( v6_relat_2(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f57,f19])).

fof(f57,plain,
    ( v6_relat_2(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f56,f41])).

fof(f41,plain,(
    v6_relat_2(sK0) ),
    inference(subsumption_resolution,[],[f40,f16])).

fof(f40,plain,
    ( v6_relat_2(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f26,f20])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v2_wellord1(X0)
      | v6_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f56,plain,
    ( ~ v6_relat_2(sK0)
    | v6_relat_2(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f31,f21])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_wellord1(X0,X1,X2)
      | ~ v6_relat_2(X0)
      | v6_relat_2(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f76,plain,
    ( ~ v6_relat_2(sK1)
    | ~ v4_relat_2(sK1)
    | ~ v8_relat_2(sK1)
    | ~ v1_relat_2(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f75,f22])).

fof(f22,plain,(
    ~ v2_wellord1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f75,plain,
    ( v2_wellord1(sK1)
    | ~ v6_relat_2(sK1)
    | ~ v4_relat_2(sK1)
    | ~ v8_relat_2(sK1)
    | ~ v1_relat_2(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f73,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_wellord1(X0)
      | v2_wellord1(X0)
      | ~ v6_relat_2(X0)
      | ~ v4_relat_2(X0)
      | ~ v8_relat_2(X0)
      | ~ v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f73,plain,(
    v1_wellord1(sK1) ),
    inference(subsumption_resolution,[],[f72,f16])).

fof(f72,plain,
    ( v1_wellord1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f71,f17])).

fof(f71,plain,
    ( v1_wellord1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f70,f18])).

fof(f70,plain,
    ( v1_wellord1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f69,f19])).

fof(f69,plain,
    ( v1_wellord1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f68,f43])).

fof(f43,plain,(
    v1_wellord1(sK0) ),
    inference(subsumption_resolution,[],[f42,f16])).

fof(f42,plain,
    ( v1_wellord1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f27,f20])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v2_wellord1(X0)
      | v1_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f68,plain,
    ( ~ v1_wellord1(sK0)
    | v1_wellord1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f33,f21])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_wellord1(X0,X1,X2)
      | ~ v1_wellord1(X0)
      | v1_wellord1(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

%------------------------------------------------------------------------------
