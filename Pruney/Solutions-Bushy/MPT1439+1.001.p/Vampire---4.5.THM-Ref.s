%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1439+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 308 expanded)
%              Number of leaves         :    7 ( 127 expanded)
%              Depth                    :    7
%              Number of atoms          :  223 (3655 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f52,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f35,f36,f37,f38,f39,f40,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r4_wellord1(X0,X2)
      | ~ r4_wellord1(X1,X2)
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_wellord1(X0,X2)
              | ~ r4_wellord1(X1,X2)
              | ~ r4_wellord1(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_wellord1(X0,X2)
              | ~ r4_wellord1(X1,X2)
              | ~ r4_wellord1(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( ( r4_wellord1(X1,X2)
                  & r4_wellord1(X0,X1) )
               => r4_wellord1(X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_wellord1)).

fof(f40,plain,(
    ~ r4_wellord1(k8_filter_1(sK0),k8_filter_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f19,f20,f21,f25,f26,f27,f30,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(k8_filter_1(X0),k8_filter_1(X1))
      | r1_filter_1(X0,X1)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_filter_1(X0,X1)
              | ~ r4_wellord1(k8_filter_1(X0),k8_filter_1(X1)) )
            & ( r4_wellord1(k8_filter_1(X0),k8_filter_1(X1))
              | ~ r1_filter_1(X0,X1) ) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_filter_1(X0,X1)
          <=> r4_wellord1(k8_filter_1(X0),k8_filter_1(X1)) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_filter_1(X0,X1)
          <=> r4_wellord1(k8_filter_1(X0),k8_filter_1(X1)) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l3_lattices(X1)
            & v10_lattices(X1)
            & ~ v2_struct_0(X1) )
         => ( r1_filter_1(X0,X1)
          <=> r4_wellord1(k8_filter_1(X0),k8_filter_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_filter_1)).

fof(f30,plain,(
    ~ r1_filter_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r1_filter_1(sK0,sK2)
    & r1_filter_1(sK1,sK2)
    & r1_filter_1(sK0,sK1)
    & l3_lattices(sK2)
    & v10_lattices(sK2)
    & ~ v2_struct_0(sK2)
    & l3_lattices(sK1)
    & v10_lattices(sK1)
    & ~ v2_struct_0(sK1)
    & l3_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f16,f15,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_filter_1(X0,X2)
                & r1_filter_1(X1,X2)
                & r1_filter_1(X0,X1)
                & l3_lattices(X2)
                & v10_lattices(X2)
                & ~ v2_struct_0(X2) )
            & l3_lattices(X1)
            & v10_lattices(X1)
            & ~ v2_struct_0(X1) )
        & l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_filter_1(sK0,X2)
              & r1_filter_1(X1,X2)
              & r1_filter_1(sK0,X1)
              & l3_lattices(X2)
              & v10_lattices(X2)
              & ~ v2_struct_0(X2) )
          & l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
      & l3_lattices(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_filter_1(sK0,X2)
            & r1_filter_1(X1,X2)
            & r1_filter_1(sK0,X1)
            & l3_lattices(X2)
            & v10_lattices(X2)
            & ~ v2_struct_0(X2) )
        & l3_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ~ r1_filter_1(sK0,X2)
          & r1_filter_1(sK1,X2)
          & r1_filter_1(sK0,sK1)
          & l3_lattices(X2)
          & v10_lattices(X2)
          & ~ v2_struct_0(X2) )
      & l3_lattices(sK1)
      & v10_lattices(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X2] :
        ( ~ r1_filter_1(sK0,X2)
        & r1_filter_1(sK1,X2)
        & r1_filter_1(sK0,sK1)
        & l3_lattices(X2)
        & v10_lattices(X2)
        & ~ v2_struct_0(X2) )
   => ( ~ r1_filter_1(sK0,sK2)
      & r1_filter_1(sK1,sK2)
      & r1_filter_1(sK0,sK1)
      & l3_lattices(sK2)
      & v10_lattices(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_filter_1(X0,X2)
              & r1_filter_1(X1,X2)
              & r1_filter_1(X0,X1)
              & l3_lattices(X2)
              & v10_lattices(X2)
              & ~ v2_struct_0(X2) )
          & l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_filter_1(X0,X2)
              & r1_filter_1(X1,X2)
              & r1_filter_1(X0,X1)
              & l3_lattices(X2)
              & v10_lattices(X2)
              & ~ v2_struct_0(X2) )
          & l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l3_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( l3_lattices(X2)
                  & v10_lattices(X2)
                  & ~ v2_struct_0(X2) )
               => ( ( r1_filter_1(X1,X2)
                    & r1_filter_1(X0,X1) )
                 => r1_filter_1(X0,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l3_lattices(X1)
            & v10_lattices(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( l3_lattices(X2)
                & v10_lattices(X2)
                & ~ v2_struct_0(X2) )
             => ( ( r1_filter_1(X1,X2)
                  & r1_filter_1(X0,X1) )
               => r1_filter_1(X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_filter_1)).

fof(f27,plain,(
    l3_lattices(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f26,plain,(
    v10_lattices(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f25,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f21,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f20,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f19,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f39,plain,(
    r4_wellord1(k8_filter_1(sK1),k8_filter_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f22,f23,f24,f25,f26,f27,f29,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r4_wellord1(k8_filter_1(X0),k8_filter_1(X1))
      | ~ r1_filter_1(X0,X1)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f29,plain,(
    r1_filter_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f24,plain,(
    l3_lattices(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f23,plain,(
    v10_lattices(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f22,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f38,plain,(
    r4_wellord1(k8_filter_1(sK0),k8_filter_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f19,f20,f21,f22,f23,f24,f28,f33])).

fof(f28,plain,(
    r1_filter_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f37,plain,(
    v1_relat_1(k8_filter_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f25,f26,f27,f32])).

fof(f32,plain,(
    ! [X0] :
      ( v1_relat_1(k8_filter_1(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( v1_relat_1(k8_filter_1(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( v1_relat_1(k8_filter_1(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => v1_relat_1(k8_filter_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_filter_1)).

fof(f36,plain,(
    v1_relat_1(k8_filter_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f22,f23,f24,f32])).

fof(f35,plain,(
    v1_relat_1(k8_filter_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f19,f20,f21,f32])).

%------------------------------------------------------------------------------
