%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : wellord1__t50_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:14 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 182 expanded)
%              Number of leaves         :    9 (  57 expanded)
%              Depth                    :   19
%              Number of atoms          :  232 ( 844 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f68,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f62,f67])).

fof(f67,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f66])).

fof(f66,plain,
    ( $false
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f65,f20])).

fof(f20,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ r4_wellord1(sK1,sK0)
    & r4_wellord1(sK0,sK1)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f14,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r4_wellord1(X1,X0)
            & r4_wellord1(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r4_wellord1(X1,sK0)
          & r4_wellord1(sK0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r4_wellord1(X1,X0)
          & r4_wellord1(X0,X1)
          & v1_relat_1(X1) )
     => ( ~ r4_wellord1(sK1,X0)
        & r4_wellord1(X0,sK1)
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r4_wellord1(X1,X0)
          & r4_wellord1(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r4_wellord1(X1,X0)
          & r4_wellord1(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r4_wellord1(X0,X1)
             => r4_wellord1(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t50_wellord1.p',t50_wellord1)).

fof(f65,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f64,f21])).

fof(f21,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f64,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f63,f22])).

fof(f22,plain,(
    r4_wellord1(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f63,plain,
    ( ~ r4_wellord1(sK0,sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f56,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK2(X0,X1))
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r4_wellord1(X0,X1)
              | ! [X2] :
                  ( ~ r3_wellord1(X0,X1,X2)
                  | ~ v1_funct_1(X2)
                  | ~ v1_relat_1(X2) ) )
            & ( ( r3_wellord1(X0,X1,sK2(X0,X1))
                & v1_funct_1(sK2(X0,X1))
                & v1_relat_1(sK2(X0,X1)) )
              | ~ r4_wellord1(X0,X1) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r3_wellord1(X0,X1,X3)
          & v1_funct_1(X3)
          & v1_relat_1(X3) )
     => ( r3_wellord1(X0,X1,sK2(X0,X1))
        & v1_funct_1(sK2(X0,X1))
        & v1_relat_1(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r4_wellord1(X0,X1)
              | ! [X2] :
                  ( ~ r3_wellord1(X0,X1,X2)
                  | ~ v1_funct_1(X2)
                  | ~ v1_relat_1(X2) ) )
            & ( ? [X3] :
                  ( r3_wellord1(X0,X1,X3)
                  & v1_funct_1(X3)
                  & v1_relat_1(X3) )
              | ~ r4_wellord1(X0,X1) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r4_wellord1(X0,X1)
              | ! [X2] :
                  ( ~ r3_wellord1(X0,X1,X2)
                  | ~ v1_funct_1(X2)
                  | ~ v1_relat_1(X2) ) )
            & ( ? [X2] :
                  ( r3_wellord1(X0,X1,X2)
                  & v1_funct_1(X2)
                  & v1_relat_1(X2) )
              | ~ r4_wellord1(X0,X1) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r4_wellord1(X0,X1)
          <=> ? [X2] :
                ( r3_wellord1(X0,X1,X2)
                & v1_funct_1(X2)
                & v1_relat_1(X2) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
          <=> ? [X2] :
                ( r3_wellord1(X0,X1,X2)
                & v1_funct_1(X2)
                & v1_relat_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t50_wellord1.p',d8_wellord1)).

fof(f56,plain,
    ( ~ v1_funct_1(sK2(sK0,sK1))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl3_3
  <=> ~ v1_funct_1(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f62,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f61])).

fof(f61,plain,
    ( $false
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f60,f20])).

fof(f60,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f59,f21])).

fof(f59,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f58,f22])).

fof(f58,plain,
    ( ~ r4_wellord1(sK0,sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl3_1 ),
    inference(resolution,[],[f50,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK2(X0,X1))
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f50,plain,
    ( ~ v1_relat_1(sK2(sK0,sK1))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl3_1
  <=> ~ v1_relat_1(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f57,plain,
    ( ~ spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f44,f55,f49])).

fof(f44,plain,
    ( ~ v1_funct_1(sK2(sK0,sK1))
    | ~ v1_relat_1(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f43,f20])).

fof(f43,plain,
    ( ~ v1_funct_1(sK2(sK0,sK1))
    | ~ v1_relat_1(sK2(sK0,sK1))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f42,f21])).

fof(f42,plain,
    ( ~ v1_funct_1(sK2(sK0,sK1))
    | ~ v1_relat_1(sK2(sK0,sK1))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f40,f22])).

fof(f40,plain,
    ( ~ v1_funct_1(sK2(sK0,sK1))
    | ~ v1_relat_1(sK2(sK0,sK1))
    | ~ r4_wellord1(sK0,sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f39,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r3_wellord1(X0,X1,sK2(X0,X1))
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f39,plain,(
    ! [X0] :
      ( ~ r3_wellord1(sK0,sK1,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f38,f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t50_wellord1.p',dt_k2_funct_1)).

fof(f38,plain,(
    ! [X0] :
      ( ~ r3_wellord1(sK0,sK1,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k2_funct_1(X0)) ) ),
    inference(subsumption_resolution,[],[f37,f30])).

fof(f30,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0] :
      ( ~ r3_wellord1(sK0,sK1,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0)) ) ),
    inference(subsumption_resolution,[],[f36,f20])).

fof(f36,plain,(
    ! [X0] :
      ( ~ r3_wellord1(sK0,sK1,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK0)
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0)) ) ),
    inference(subsumption_resolution,[],[f35,f21])).

fof(f35,plain,(
    ! [X0] :
      ( ~ r3_wellord1(sK0,sK1,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(sK0)
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0)) ) ),
    inference(resolution,[],[f28,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ r3_wellord1(sK1,sK0,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f32,f21])).

fof(f32,plain,(
    ! [X0] :
      ( ~ r3_wellord1(sK1,sK0,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f31,f20])).

fof(f31,plain,(
    ! [X0] :
      ( ~ r3_wellord1(sK1,sK0,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK0)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f27,f23])).

fof(f23,plain,(
    ~ r4_wellord1(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r4_wellord1(X0,X1)
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r3_wellord1(X1,X0,k2_funct_1(X2))
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_wellord1(X1,X0,k2_funct_1(X2))
              | ~ r3_wellord1(X0,X1,X2)
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_wellord1(X1,X0,k2_funct_1(X2))
              | ~ r3_wellord1(X0,X1,X2)
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( r3_wellord1(X0,X1,X2)
               => r3_wellord1(X1,X0,k2_funct_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t50_wellord1.p',t49_wellord1)).
%------------------------------------------------------------------------------
