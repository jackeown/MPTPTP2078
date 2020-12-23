%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : wellord1__t52_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:14 EDT 2019

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 172 expanded)
%              Number of leaves         :    9 (  57 expanded)
%              Depth                    :   26
%              Number of atoms          :  334 (1178 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   8 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f65,plain,(
    $false ),
    inference(subsumption_resolution,[],[f64,f25])).

fof(f25,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ r4_wellord1(sK0,sK2)
    & r4_wellord1(sK1,sK2)
    & r4_wellord1(sK0,sK1)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f18,f17,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r4_wellord1(X0,X2)
                & r4_wellord1(X1,X2)
                & r4_wellord1(X0,X1)
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r4_wellord1(sK0,X2)
              & r4_wellord1(X1,X2)
              & r4_wellord1(sK0,X1)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r4_wellord1(X0,X2)
              & r4_wellord1(X1,X2)
              & r4_wellord1(X0,X1)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
     => ( ? [X2] :
            ( ~ r4_wellord1(X0,X2)
            & r4_wellord1(sK1,X2)
            & r4_wellord1(X0,sK1)
            & v1_relat_1(X2) )
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r4_wellord1(X0,X2)
          & r4_wellord1(X1,X2)
          & r4_wellord1(X0,X1)
          & v1_relat_1(X2) )
     => ( ~ r4_wellord1(X0,sK2)
        & r4_wellord1(X1,sK2)
        & r4_wellord1(X0,X1)
        & v1_relat_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r4_wellord1(X0,X2)
              & r4_wellord1(X1,X2)
              & r4_wellord1(X0,X1)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r4_wellord1(X0,X2)
              & r4_wellord1(X1,X2)
              & r4_wellord1(X0,X1)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => ( ( r4_wellord1(X1,X2)
                    & r4_wellord1(X0,X1) )
                 => r4_wellord1(X0,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( ( r4_wellord1(X1,X2)
                  & r4_wellord1(X0,X1) )
               => r4_wellord1(X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t52_wellord1.p',t52_wellord1)).

fof(f64,plain,(
    ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f61,f28])).

fof(f28,plain,(
    r4_wellord1(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f61,plain,
    ( ~ r4_wellord1(sK1,sK2)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f60,f27])).

fof(f27,plain,(
    r4_wellord1(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f60,plain,(
    ! [X0] :
      ( ~ r4_wellord1(sK0,X0)
      | ~ r4_wellord1(X0,sK2)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f59,f24])).

fof(f24,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ r4_wellord1(X0,sK2)
      | ~ r4_wellord1(sK0,X0)
      | ~ v1_relat_1(sK0) ) ),
    inference(duplicate_literal_removal,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ r4_wellord1(X0,sK2)
      | ~ r4_wellord1(sK0,X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK0)
      | ~ r4_wellord1(sK0,X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f56,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r3_wellord1(X0,X1,sK3(X0,X1))
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r4_wellord1(X0,X1)
              | ! [X2] :
                  ( ~ r3_wellord1(X0,X1,X2)
                  | ~ v1_funct_1(X2)
                  | ~ v1_relat_1(X2) ) )
            & ( ( r3_wellord1(X0,X1,sK3(X0,X1))
                & v1_funct_1(sK3(X0,X1))
                & v1_relat_1(sK3(X0,X1)) )
              | ~ r4_wellord1(X0,X1) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r3_wellord1(X0,X1,X3)
          & v1_funct_1(X3)
          & v1_relat_1(X3) )
     => ( r3_wellord1(X0,X1,sK3(X0,X1))
        & v1_funct_1(sK3(X0,X1))
        & v1_relat_1(sK3(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
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
    file('/export/starexec/sandbox2/benchmark/wellord1__t52_wellord1.p',d8_wellord1)).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_wellord1(sK0,X0,sK3(X1,X2))
      | ~ v1_relat_1(X0)
      | ~ r4_wellord1(X0,sK2)
      | ~ r4_wellord1(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f54,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK3(X0,X1))
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_wellord1(sK0,X0,sK3(X1,X2))
      | ~ v1_relat_1(sK3(X1,X2))
      | ~ v1_relat_1(X0)
      | ~ r4_wellord1(X0,sK2)
      | ~ r4_wellord1(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f53,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK3(X0,X1))
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r3_wellord1(sK0,X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ r4_wellord1(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f52,f26])).

fof(f26,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r3_wellord1(sK0,X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ r4_wellord1(X0,sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(duplicate_literal_removal,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r3_wellord1(sK0,X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ r4_wellord1(X0,sK2)
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(X0)
      | ~ r4_wellord1(X0,sK2)
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f49,f32])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r3_wellord1(X0,sK2,sK3(X2,X3))
      | ~ r3_wellord1(sK0,X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ r4_wellord1(X2,X3)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f47,f30])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r3_wellord1(sK0,X0,X1)
      | ~ r3_wellord1(X0,sK2,sK3(X2,X3))
      | ~ v1_relat_1(sK3(X2,X3))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ r4_wellord1(X2,X3)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f46,f31])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r3_wellord1(sK0,X0,X2)
      | ~ r3_wellord1(X0,sK2,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f45,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t52_wellord1.p',dt_k5_relat_1)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_wellord1(X0,sK2,X1)
      | ~ r3_wellord1(sK0,X0,X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k5_relat_1(X2,X1)) ) ),
    inference(subsumption_resolution,[],[f44,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t52_wellord1.p',fc2_funct_1)).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_wellord1(X0,sK2,X1)
      | ~ r3_wellord1(sK0,X0,X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(k5_relat_1(X2,X1))
      | ~ v1_relat_1(k5_relat_1(X2,X1)) ) ),
    inference(subsumption_resolution,[],[f43,f24])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_wellord1(X0,sK2,X1)
      | ~ r3_wellord1(sK0,X0,X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK0)
      | ~ v1_funct_1(k5_relat_1(X2,X1))
      | ~ v1_relat_1(k5_relat_1(X2,X1)) ) ),
    inference(subsumption_resolution,[],[f42,f26])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_wellord1(X0,sK2,X1)
      | ~ r3_wellord1(sK0,X0,X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK0)
      | ~ v1_funct_1(k5_relat_1(X2,X1))
      | ~ v1_relat_1(k5_relat_1(X2,X1)) ) ),
    inference(resolution,[],[f34,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ r3_wellord1(sK0,sK2,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f39,f24])).

fof(f39,plain,(
    ! [X0] :
      ( ~ r3_wellord1(sK0,sK2,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f38,f26])).

fof(f38,plain,(
    ! [X0] :
      ( ~ r3_wellord1(sK0,sK2,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f33,f29])).

fof(f29,plain,(
    ~ r4_wellord1(sK0,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r4_wellord1(X0,X1)
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r3_wellord1(X0,X2,k5_relat_1(X3,X4))
      | ~ r3_wellord1(X1,X2,X4)
      | ~ r3_wellord1(X0,X1,X3)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r3_wellord1(X0,X2,k5_relat_1(X3,X4))
                      | ~ r3_wellord1(X1,X2,X4)
                      | ~ r3_wellord1(X0,X1,X3)
                      | ~ v1_funct_1(X4)
                      | ~ v1_relat_1(X4) )
                  | ~ v1_funct_1(X3)
                  | ~ v1_relat_1(X3) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r3_wellord1(X0,X2,k5_relat_1(X3,X4))
                      | ~ r3_wellord1(X1,X2,X4)
                      | ~ r3_wellord1(X0,X1,X3)
                      | ~ v1_funct_1(X4)
                      | ~ v1_relat_1(X4) )
                  | ~ v1_funct_1(X3)
                  | ~ v1_relat_1(X3) )
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
              ( v1_relat_1(X2)
             => ! [X3] :
                  ( ( v1_funct_1(X3)
                    & v1_relat_1(X3) )
                 => ! [X4] :
                      ( ( v1_funct_1(X4)
                        & v1_relat_1(X4) )
                     => ( ( r3_wellord1(X1,X2,X4)
                          & r3_wellord1(X0,X1,X3) )
                       => r3_wellord1(X0,X2,k5_relat_1(X3,X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t52_wellord1.p',t51_wellord1)).
%------------------------------------------------------------------------------
