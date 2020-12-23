%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : wellord1__t65_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:15 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   35 (  83 expanded)
%              Number of leaves         :    6 (  25 expanded)
%              Depth                    :   15
%              Number of atoms          :  185 ( 497 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f38,plain,(
    $false ),
    inference(subsumption_resolution,[],[f37,f19])).

fof(f19,plain,(
    r4_wellord1(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ~ v2_wellord1(sK1)
    & v2_wellord1(sK0)
    & r4_wellord1(sK0,sK1)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f11,f10])).

fof(f10,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_wellord1(X1)
            & v2_wellord1(X0)
            & r4_wellord1(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ v2_wellord1(X1)
          & v2_wellord1(sK0)
          & r4_wellord1(sK0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_wellord1(X1)
          & v2_wellord1(X0)
          & r4_wellord1(X0,X1)
          & v1_relat_1(X1) )
     => ( ~ v2_wellord1(sK1)
        & v2_wellord1(X0)
        & r4_wellord1(X0,sK1)
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_wellord1(X1)
          & v2_wellord1(X0)
          & r4_wellord1(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_wellord1(X1)
          & v2_wellord1(X0)
          & r4_wellord1(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( ( v2_wellord1(X0)
                & r4_wellord1(X0,X1) )
             => v2_wellord1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( ( v2_wellord1(X0)
              & r4_wellord1(X0,X1) )
           => v2_wellord1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t65_wellord1.p',t65_wellord1)).

fof(f37,plain,(
    ~ r4_wellord1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f34,f17])).

fof(f17,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f34,plain,
    ( ~ v1_relat_1(sK0)
    | ~ r4_wellord1(sK0,sK1) ),
    inference(resolution,[],[f33,f20])).

fof(f20,plain,(
    v2_wellord1(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0)
      | ~ r4_wellord1(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f32,f18])).

fof(f18,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0)
      | ~ r4_wellord1(X0,sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(duplicate_literal_removal,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0)
      | ~ r4_wellord1(X0,sK1)
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(X0)
      | ~ r4_wellord1(X0,sK1)
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f30,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r3_wellord1(X0,X1,sK2(X0,X1))
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f15])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r3_wellord1(X0,X1,X3)
          & v1_funct_1(X3)
          & v1_relat_1(X3) )
     => ( r3_wellord1(X0,X1,sK2(X0,X1))
        & v1_funct_1(sK2(X0,X1))
        & v1_relat_1(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
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
    inference(rectify,[],[f13])).

fof(f13,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
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
    file('/export/starexec/sandbox/benchmark/wellord1__t65_wellord1.p',d8_wellord1)).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_wellord1(X0,sK1,sK2(X1,X2))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0)
      | ~ r4_wellord1(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f29,f18])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_wellord1(X0)
      | ~ r3_wellord1(X0,sK1,sK2(X1,X2))
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(X0)
      | ~ r4_wellord1(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f28,f21])).

fof(f21,plain,(
    ~ v2_wellord1(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_wellord1(X1)
      | ~ v2_wellord1(X0)
      | ~ r3_wellord1(X0,X1,sK2(X2,X3))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ r4_wellord1(X2,X3)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f27,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK2(X0,X1))
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r3_wellord1(X0,X1,sK2(X2,X3))
      | ~ v2_wellord1(X0)
      | v2_wellord1(X1)
      | ~ v1_relat_1(sK2(X2,X3))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ r4_wellord1(X2,X3)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f26,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK2(X0,X1))
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v2_wellord1(X0)
      | v2_wellord1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_wellord1(X1)
              | ~ r3_wellord1(X0,X1,X2)
              | ~ v2_wellord1(X0)
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_wellord1(X1)
              | ~ r3_wellord1(X0,X1,X2)
              | ~ v2_wellord1(X0)
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/wellord1__t65_wellord1.p',t54_wellord1)).
%------------------------------------------------------------------------------
