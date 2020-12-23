%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 189 expanded)
%              Number of leaves         :    7 (  67 expanded)
%              Depth                    :   27
%              Number of atoms          :  394 (2101 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   20 (   8 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f113,plain,(
    $false ),
    inference(subsumption_resolution,[],[f112,f30])).

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

fof(f112,plain,(
    r1_filter_1(sK0,sK2) ),
    inference(subsumption_resolution,[],[f111,f27])).

fof(f27,plain,(
    l3_lattices(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f111,plain,
    ( ~ l3_lattices(sK2)
    | r1_filter_1(sK0,sK2) ),
    inference(subsumption_resolution,[],[f110,f25])).

fof(f25,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f110,plain,
    ( v2_struct_0(sK2)
    | ~ l3_lattices(sK2)
    | r1_filter_1(sK0,sK2) ),
    inference(subsumption_resolution,[],[f109,f26])).

fof(f26,plain,(
    v10_lattices(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f109,plain,
    ( ~ v10_lattices(sK2)
    | v2_struct_0(sK2)
    | ~ l3_lattices(sK2)
    | r1_filter_1(sK0,sK2) ),
    inference(resolution,[],[f64,f29])).

fof(f29,plain,(
    r1_filter_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f64,plain,(
    ! [X0] :
      ( ~ r1_filter_1(sK1,X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | r1_filter_1(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f63,f19])).

fof(f19,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f63,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ r1_filter_1(sK1,X0)
      | ~ l3_lattices(X0)
      | r1_filter_1(sK0,X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f62,f20])).

fof(f20,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f62,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ r1_filter_1(sK1,X0)
      | ~ l3_lattices(X0)
      | r1_filter_1(sK0,X0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f61,f21])).

fof(f21,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f61,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ r1_filter_1(sK1,X0)
      | ~ l3_lattices(X0)
      | r1_filter_1(sK0,X0)
      | ~ l3_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ r1_filter_1(sK1,X0)
      | ~ l3_lattices(X0)
      | r1_filter_1(sK0,X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f50,f34])).

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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f50,plain,(
    ! [X0] :
      ( r4_wellord1(k8_filter_1(sK0),k8_filter_1(X0))
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ r1_filter_1(sK1,X0)
      | ~ l3_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f49,f19])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | r4_wellord1(k8_filter_1(sK0),k8_filter_1(X0))
      | ~ r1_filter_1(sK1,X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f48,f20])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | r4_wellord1(k8_filter_1(sK0),k8_filter_1(X0))
      | ~ r1_filter_1(sK1,X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f47,f21])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | r4_wellord1(k8_filter_1(sK0),k8_filter_1(X0))
      | ~ r1_filter_1(sK1,X0)
      | ~ l3_lattices(X0)
      | ~ l3_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f46,f22])).

fof(f22,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | v2_struct_0(sK1)
      | r4_wellord1(k8_filter_1(sK0),k8_filter_1(X0))
      | ~ r1_filter_1(sK1,X0)
      | ~ l3_lattices(X0)
      | ~ l3_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f45,f23])).

fof(f23,plain,(
    v10_lattices(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(sK1)
      | v2_struct_0(sK1)
      | r4_wellord1(k8_filter_1(sK0),k8_filter_1(X0))
      | ~ r1_filter_1(sK1,X0)
      | ~ l3_lattices(X0)
      | ~ l3_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f43,f24])).

fof(f24,plain,(
    l3_lattices(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(sK1)
      | ~ v10_lattices(sK1)
      | v2_struct_0(sK1)
      | r4_wellord1(k8_filter_1(sK0),k8_filter_1(X0))
      | ~ r1_filter_1(sK1,X0)
      | ~ l3_lattices(X0)
      | ~ l3_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f42,f28])).

fof(f28,plain,(
    r1_filter_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_filter_1(X2,X1)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | r4_wellord1(k8_filter_1(X2),k8_filter_1(X0))
      | ~ r1_filter_1(X1,X0)
      | ~ l3_lattices(X0)
      | ~ l3_lattices(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f41,f32])).

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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => v1_relat_1(k8_filter_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_filter_1)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | r4_wellord1(k8_filter_1(X2),k8_filter_1(X0))
      | ~ r1_filter_1(X1,X0)
      | ~ v1_relat_1(k8_filter_1(X2))
      | ~ r1_filter_1(X2,X1)
      | ~ l3_lattices(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(duplicate_literal_removal,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | r4_wellord1(k8_filter_1(X2),k8_filter_1(X0))
      | ~ r1_filter_1(X1,X0)
      | ~ v1_relat_1(k8_filter_1(X2))
      | ~ r1_filter_1(X2,X1)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(resolution,[],[f37,f33])).

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

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r4_wellord1(X2,k8_filter_1(X0))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | r4_wellord1(X2,k8_filter_1(X1))
      | ~ r1_filter_1(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f36,f32])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_filter_1(X0,X1)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | r4_wellord1(X2,k8_filter_1(X1))
      | ~ r4_wellord1(X2,k8_filter_1(X0))
      | ~ v1_relat_1(k8_filter_1(X0))
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f35,f32])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_filter_1(X0,X1)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | r4_wellord1(X2,k8_filter_1(X1))
      | ~ r4_wellord1(X2,k8_filter_1(X0))
      | ~ v1_relat_1(k8_filter_1(X1))
      | ~ v1_relat_1(k8_filter_1(X0))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f33,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r4_wellord1(X1,X2)
      | r4_wellord1(X0,X2)
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:43:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (18523)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.21/0.42  % (18541)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
% 0.21/0.43  % (18541)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f113,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(subsumption_resolution,[],[f112,f30])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    ~r1_filter_1(sK0,sK2)),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ((~r1_filter_1(sK0,sK2) & r1_filter_1(sK1,sK2) & r1_filter_1(sK0,sK1) & l3_lattices(sK2) & v10_lattices(sK2) & ~v2_struct_0(sK2)) & l3_lattices(sK1) & v10_lattices(sK1) & ~v2_struct_0(sK1)) & l3_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f16,f15,f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (? [X2] : (~r1_filter_1(X0,X2) & r1_filter_1(X1,X2) & r1_filter_1(X0,X1) & l3_lattices(X2) & v10_lattices(X2) & ~v2_struct_0(X2)) & l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) & l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r1_filter_1(sK0,X2) & r1_filter_1(X1,X2) & r1_filter_1(sK0,X1) & l3_lattices(X2) & v10_lattices(X2) & ~v2_struct_0(X2)) & l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) & l3_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ? [X1] : (? [X2] : (~r1_filter_1(sK0,X2) & r1_filter_1(X1,X2) & r1_filter_1(sK0,X1) & l3_lattices(X2) & v10_lattices(X2) & ~v2_struct_0(X2)) & l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r1_filter_1(sK0,X2) & r1_filter_1(sK1,X2) & r1_filter_1(sK0,sK1) & l3_lattices(X2) & v10_lattices(X2) & ~v2_struct_0(X2)) & l3_lattices(sK1) & v10_lattices(sK1) & ~v2_struct_0(sK1))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ? [X2] : (~r1_filter_1(sK0,X2) & r1_filter_1(sK1,X2) & r1_filter_1(sK0,sK1) & l3_lattices(X2) & v10_lattices(X2) & ~v2_struct_0(X2)) => (~r1_filter_1(sK0,sK2) & r1_filter_1(sK1,sK2) & r1_filter_1(sK0,sK1) & l3_lattices(sK2) & v10_lattices(sK2) & ~v2_struct_0(sK2))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f7,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (? [X2] : (~r1_filter_1(X0,X2) & r1_filter_1(X1,X2) & r1_filter_1(X0,X1) & l3_lattices(X2) & v10_lattices(X2) & ~v2_struct_0(X2)) & l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) & l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.21/0.43    inference(flattening,[],[f6])).
% 0.21/0.43  fof(f6,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (? [X2] : ((~r1_filter_1(X0,X2) & (r1_filter_1(X1,X2) & r1_filter_1(X0,X1))) & (l3_lattices(X2) & v10_lattices(X2) & ~v2_struct_0(X2))) & (l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1))) & (l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,negated_conjecture,(
% 0.21/0.43    ~! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l3_lattices(X2) & v10_lattices(X2) & ~v2_struct_0(X2)) => ((r1_filter_1(X1,X2) & r1_filter_1(X0,X1)) => r1_filter_1(X0,X2)))))),
% 0.21/0.43    inference(negated_conjecture,[],[f4])).
% 0.21/0.43  fof(f4,conjecture,(
% 0.21/0.43    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l3_lattices(X2) & v10_lattices(X2) & ~v2_struct_0(X2)) => ((r1_filter_1(X1,X2) & r1_filter_1(X0,X1)) => r1_filter_1(X0,X2)))))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_filter_1)).
% 0.21/0.43  fof(f112,plain,(
% 0.21/0.43    r1_filter_1(sK0,sK2)),
% 0.21/0.43    inference(subsumption_resolution,[],[f111,f27])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    l3_lattices(sK2)),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  fof(f111,plain,(
% 0.21/0.43    ~l3_lattices(sK2) | r1_filter_1(sK0,sK2)),
% 0.21/0.43    inference(subsumption_resolution,[],[f110,f25])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ~v2_struct_0(sK2)),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  fof(f110,plain,(
% 0.21/0.43    v2_struct_0(sK2) | ~l3_lattices(sK2) | r1_filter_1(sK0,sK2)),
% 0.21/0.43    inference(subsumption_resolution,[],[f109,f26])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    v10_lattices(sK2)),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.44  fof(f109,plain,(
% 0.21/0.44    ~v10_lattices(sK2) | v2_struct_0(sK2) | ~l3_lattices(sK2) | r1_filter_1(sK0,sK2)),
% 0.21/0.44    inference(resolution,[],[f64,f29])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    r1_filter_1(sK1,sK2)),
% 0.21/0.44    inference(cnf_transformation,[],[f17])).
% 0.21/0.44  fof(f64,plain,(
% 0.21/0.44    ( ! [X0] : (~r1_filter_1(sK1,X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | r1_filter_1(sK0,X0)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f63,f19])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ~v2_struct_0(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f17])).
% 0.21/0.44  fof(f63,plain,(
% 0.21/0.44    ( ! [X0] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~r1_filter_1(sK1,X0) | ~l3_lattices(X0) | r1_filter_1(sK0,X0) | v2_struct_0(sK0)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f62,f20])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    v10_lattices(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f17])).
% 0.21/0.44  fof(f62,plain,(
% 0.21/0.44    ( ! [X0] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~r1_filter_1(sK1,X0) | ~l3_lattices(X0) | r1_filter_1(sK0,X0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f61,f21])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    l3_lattices(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f17])).
% 0.21/0.44  fof(f61,plain,(
% 0.21/0.44    ( ! [X0] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~r1_filter_1(sK1,X0) | ~l3_lattices(X0) | r1_filter_1(sK0,X0) | ~l3_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.44    inference(duplicate_literal_removal,[],[f57])).
% 0.21/0.44  fof(f57,plain,(
% 0.21/0.44    ( ! [X0] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~r1_filter_1(sK1,X0) | ~l3_lattices(X0) | r1_filter_1(sK0,X0) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.44    inference(resolution,[],[f50,f34])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r4_wellord1(k8_filter_1(X0),k8_filter_1(X1)) | r1_filter_1(X0,X1) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f18])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (((r1_filter_1(X0,X1) | ~r4_wellord1(k8_filter_1(X0),k8_filter_1(X1))) & (r4_wellord1(k8_filter_1(X0),k8_filter_1(X1)) | ~r1_filter_1(X0,X1))) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.44    inference(nnf_transformation,[],[f13])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : ((r1_filter_1(X0,X1) <=> r4_wellord1(k8_filter_1(X0),k8_filter_1(X1))) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.44    inference(flattening,[],[f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : ((r1_filter_1(X0,X1) <=> r4_wellord1(k8_filter_1(X0),k8_filter_1(X1))) | (~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r1_filter_1(X0,X1) <=> r4_wellord1(k8_filter_1(X0),k8_filter_1(X1)))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_filter_1)).
% 0.21/0.44  fof(f50,plain,(
% 0.21/0.44    ( ! [X0] : (r4_wellord1(k8_filter_1(sK0),k8_filter_1(X0)) | v2_struct_0(X0) | ~v10_lattices(X0) | ~r1_filter_1(sK1,X0) | ~l3_lattices(X0)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f49,f19])).
% 0.21/0.44  fof(f49,plain,(
% 0.21/0.44    ( ! [X0] : (~v10_lattices(X0) | v2_struct_0(X0) | r4_wellord1(k8_filter_1(sK0),k8_filter_1(X0)) | ~r1_filter_1(sK1,X0) | ~l3_lattices(X0) | v2_struct_0(sK0)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f48,f20])).
% 0.21/0.44  fof(f48,plain,(
% 0.21/0.44    ( ! [X0] : (~v10_lattices(X0) | v2_struct_0(X0) | r4_wellord1(k8_filter_1(sK0),k8_filter_1(X0)) | ~r1_filter_1(sK1,X0) | ~l3_lattices(X0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f47,f21])).
% 0.21/0.44  fof(f47,plain,(
% 0.21/0.44    ( ! [X0] : (~v10_lattices(X0) | v2_struct_0(X0) | r4_wellord1(k8_filter_1(sK0),k8_filter_1(X0)) | ~r1_filter_1(sK1,X0) | ~l3_lattices(X0) | ~l3_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f46,f22])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ~v2_struct_0(sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f17])).
% 0.21/0.44  fof(f46,plain,(
% 0.21/0.44    ( ! [X0] : (~v10_lattices(X0) | v2_struct_0(X0) | v2_struct_0(sK1) | r4_wellord1(k8_filter_1(sK0),k8_filter_1(X0)) | ~r1_filter_1(sK1,X0) | ~l3_lattices(X0) | ~l3_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f45,f23])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    v10_lattices(sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f17])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    ( ! [X0] : (~v10_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(sK1) | v2_struct_0(sK1) | r4_wellord1(k8_filter_1(sK0),k8_filter_1(X0)) | ~r1_filter_1(sK1,X0) | ~l3_lattices(X0) | ~l3_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f43,f24])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    l3_lattices(sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f17])).
% 0.21/0.44  fof(f43,plain,(
% 0.21/0.44    ( ! [X0] : (~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(sK1) | ~v10_lattices(sK1) | v2_struct_0(sK1) | r4_wellord1(k8_filter_1(sK0),k8_filter_1(X0)) | ~r1_filter_1(sK1,X0) | ~l3_lattices(X0) | ~l3_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.44    inference(resolution,[],[f42,f28])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    r1_filter_1(sK0,sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f17])).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~r1_filter_1(X2,X1) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | r4_wellord1(k8_filter_1(X2),k8_filter_1(X0)) | ~r1_filter_1(X1,X0) | ~l3_lattices(X0) | ~l3_lattices(X2) | ~v10_lattices(X2) | v2_struct_0(X2)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f41,f32])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    ( ! [X0] : (v1_relat_1(k8_filter_1(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ! [X0] : (v1_relat_1(k8_filter_1(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.44    inference(flattening,[],[f10])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    ! [X0] : (v1_relat_1(k8_filter_1(X0)) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => v1_relat_1(k8_filter_1(X0)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_filter_1)).
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | r4_wellord1(k8_filter_1(X2),k8_filter_1(X0)) | ~r1_filter_1(X1,X0) | ~v1_relat_1(k8_filter_1(X2)) | ~r1_filter_1(X2,X1) | ~l3_lattices(X2) | ~v10_lattices(X2) | v2_struct_0(X2)) )),
% 0.21/0.44    inference(duplicate_literal_removal,[],[f40])).
% 0.21/0.44  fof(f40,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | r4_wellord1(k8_filter_1(X2),k8_filter_1(X0)) | ~r1_filter_1(X1,X0) | ~v1_relat_1(k8_filter_1(X2)) | ~r1_filter_1(X2,X1) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X2) | ~v10_lattices(X2) | v2_struct_0(X2)) )),
% 0.21/0.44    inference(resolution,[],[f37,f33])).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r4_wellord1(k8_filter_1(X0),k8_filter_1(X1)) | ~r1_filter_1(X0,X1) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f18])).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~r4_wellord1(X2,k8_filter_1(X0)) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | r4_wellord1(X2,k8_filter_1(X1)) | ~r1_filter_1(X0,X1) | ~v1_relat_1(X2)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f36,f32])).
% 0.21/0.44  fof(f36,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~r1_filter_1(X0,X1) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | r4_wellord1(X2,k8_filter_1(X1)) | ~r4_wellord1(X2,k8_filter_1(X0)) | ~v1_relat_1(k8_filter_1(X0)) | ~v1_relat_1(X2)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f35,f32])).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~r1_filter_1(X0,X1) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | r4_wellord1(X2,k8_filter_1(X1)) | ~r4_wellord1(X2,k8_filter_1(X0)) | ~v1_relat_1(k8_filter_1(X1)) | ~v1_relat_1(k8_filter_1(X0)) | ~v1_relat_1(X2)) )),
% 0.21/0.44    inference(resolution,[],[f33,f31])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~r4_wellord1(X1,X2) | r4_wellord1(X0,X2) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : (r4_wellord1(X0,X2) | ~r4_wellord1(X1,X2) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(flattening,[],[f8])).
% 0.21/0.44  fof(f8,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : ((r4_wellord1(X0,X2) | (~r4_wellord1(X1,X2) | ~r4_wellord1(X0,X1))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ((r4_wellord1(X1,X2) & r4_wellord1(X0,X1)) => r4_wellord1(X0,X2)))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_wellord1)).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (18541)------------------------------
% 0.21/0.44  % (18541)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (18541)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (18541)Memory used [KB]: 5373
% 0.21/0.44  % (18541)Time elapsed: 0.053 s
% 0.21/0.44  % (18541)------------------------------
% 0.21/0.44  % (18541)------------------------------
% 0.21/0.44  % (18518)Success in time 0.082 s
%------------------------------------------------------------------------------
