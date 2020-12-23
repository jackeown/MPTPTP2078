%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:58 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :  217 ( 693 expanded)
%              Number of clauses        :  127 ( 166 expanded)
%              Number of leaves         :   12 ( 138 expanded)
%              Depth                    :   11
%              Number of atoms          : 1326 (9930 expanded)
%              Number of equality atoms :  164 ( 164 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   60 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v17_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v16_lattices(X0)
          & v15_lattices(X0)
          & v11_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ( v16_lattices(X0)
        & v15_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f10,plain,(
    ! [X0] :
      ( ( v16_lattices(X0)
        & v15_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f9])).

fof(f47,plain,(
    ! [X0] :
      ( v16_lattices(X0)
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v16_lattices(X0)
          & v15_lattices(X0)
          & v11_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v17_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ( v17_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v16_lattices(X0)
      | ~ v15_lattices(X0)
      | ~ v11_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0] :
      ( ( v17_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v16_lattices(X0)
      | ~ v15_lattices(X0)
      | ~ v11_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f11])).

fof(f49,plain,(
    ! [X0] :
      ( v17_lattices(X0)
      | ~ v16_lattices(X0)
      | ~ v15_lattices(X0)
      | ~ v11_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f46,plain,(
    ! [X0] :
      ( v15_lattices(X0)
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f45,plain,(
    ! [X0] :
      ( v11_lattices(X0)
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X1,X0] :
      ( sP2(X1,X0)
    <=> ( l3_lattices(X1)
        & v16_lattices(X1)
        & v15_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1)
        & l3_lattices(X0)
        & v16_lattices(X0)
        & v15_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ( sP2(X1,X0)
        | ~ l3_lattices(X1)
        | ~ v16_lattices(X1)
        | ~ v15_lattices(X1)
        | ~ v10_lattices(X1)
        | v2_struct_0(X1)
        | ~ l3_lattices(X0)
        | ~ v16_lattices(X0)
        | ~ v15_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
      & ( ( l3_lattices(X1)
          & v16_lattices(X1)
          & v15_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1)
          & l3_lattices(X0)
          & v16_lattices(X0)
          & v15_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
        | ~ sP2(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ( sP2(X1,X0)
        | ~ l3_lattices(X1)
        | ~ v16_lattices(X1)
        | ~ v15_lattices(X1)
        | ~ v10_lattices(X1)
        | v2_struct_0(X1)
        | ~ l3_lattices(X0)
        | ~ v16_lattices(X0)
        | ~ v15_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
      & ( ( l3_lattices(X1)
          & v16_lattices(X1)
          & v15_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1)
          & l3_lattices(X0)
          & v16_lattices(X0)
          & v15_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
        | ~ sP2(X1,X0) ) ) ),
    inference(flattening,[],[f36])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ~ l3_lattices(X0)
        | ~ v16_lattices(X0)
        | ~ v15_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0)
        | ~ l3_lattices(X1)
        | ~ v16_lattices(X1)
        | ~ v15_lattices(X1)
        | ~ v10_lattices(X1)
        | v2_struct_0(X1) )
      & ( ( l3_lattices(X0)
          & v16_lattices(X0)
          & v15_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0)
          & l3_lattices(X1)
          & v16_lattices(X1)
          & v15_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
        | ~ sP2(X0,X1) ) ) ),
    inference(rectify,[],[f37])).

fof(f82,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
      | ~ l3_lattices(X0)
      | ~ v16_lattices(X0)
      | ~ v15_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X1)
      | ~ v16_lattices(X1)
      | ~ v15_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f21,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ( l3_lattices(X1)
        & v11_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1)
        & l3_lattices(X0)
        & v11_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ~ l3_lattices(X1)
        | ~ v11_lattices(X1)
        | ~ v10_lattices(X1)
        | v2_struct_0(X1)
        | ~ l3_lattices(X0)
        | ~ v11_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
      & ( ( l3_lattices(X1)
          & v11_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1)
          & l3_lattices(X0)
          & v11_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ~ l3_lattices(X1)
        | ~ v11_lattices(X1)
        | ~ v10_lattices(X1)
        | v2_struct_0(X1)
        | ~ l3_lattices(X0)
        | ~ v11_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
      & ( ( l3_lattices(X1)
          & v11_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1)
          & l3_lattices(X0)
          & v11_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
        | ~ sP0(X1,X0) ) ) ),
    inference(flattening,[],[f30])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ~ l3_lattices(X0)
        | ~ v11_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0)
        | ~ l3_lattices(X1)
        | ~ v11_lattices(X1)
        | ~ v10_lattices(X1)
        | v2_struct_0(X1) )
      & ( ( l3_lattices(X0)
          & v11_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0)
          & l3_lattices(X1)
          & v11_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f31])).

fof(f64,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ l3_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X1)
      | ~ v11_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1)
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( l3_lattices(k7_filter_1(X0,X1))
        & v3_lattices(k7_filter_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1)
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => l3_lattices(k7_filter_1(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f13,plain,(
    ! [X0,X1] :
      ( l3_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f14,plain,(
    ! [X0,X1] :
      ( l3_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f50,plain,(
    ! [X0,X1] :
      ( l3_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v15_lattices(X1)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v16_lattices(X1)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v15_lattices(X0)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v16_lattices(X0)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ( sP2(X1,X0)
      <=> ( l3_lattices(k7_filter_1(X0,X1))
          & v16_lattices(k7_filter_1(X0,X1))
          & v15_lattices(k7_filter_1(X0,X1))
          & v10_lattices(k7_filter_1(X0,X1))
          & ~ v2_struct_0(k7_filter_1(X0,X1)) ) )
      | ~ sP3(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ( ( sP2(X1,X0)
          | ~ l3_lattices(k7_filter_1(X0,X1))
          | ~ v16_lattices(k7_filter_1(X0,X1))
          | ~ v15_lattices(k7_filter_1(X0,X1))
          | ~ v10_lattices(k7_filter_1(X0,X1))
          | v2_struct_0(k7_filter_1(X0,X1)) )
        & ( ( l3_lattices(k7_filter_1(X0,X1))
            & v16_lattices(k7_filter_1(X0,X1))
            & v15_lattices(k7_filter_1(X0,X1))
            & v10_lattices(k7_filter_1(X0,X1))
            & ~ v2_struct_0(k7_filter_1(X0,X1)) )
          | ~ sP2(X1,X0) ) )
      | ~ sP3(X1,X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ( ( sP2(X1,X0)
          | ~ l3_lattices(k7_filter_1(X0,X1))
          | ~ v16_lattices(k7_filter_1(X0,X1))
          | ~ v15_lattices(k7_filter_1(X0,X1))
          | ~ v10_lattices(k7_filter_1(X0,X1))
          | v2_struct_0(k7_filter_1(X0,X1)) )
        & ( ( l3_lattices(k7_filter_1(X0,X1))
            & v16_lattices(k7_filter_1(X0,X1))
            & v15_lattices(k7_filter_1(X0,X1))
            & v10_lattices(k7_filter_1(X0,X1))
            & ~ v2_struct_0(k7_filter_1(X0,X1)) )
          | ~ sP2(X1,X0) ) )
      | ~ sP3(X1,X0) ) ),
    inference(flattening,[],[f33])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( sP2(X0,X1)
          | ~ l3_lattices(k7_filter_1(X1,X0))
          | ~ v16_lattices(k7_filter_1(X1,X0))
          | ~ v15_lattices(k7_filter_1(X1,X0))
          | ~ v10_lattices(k7_filter_1(X1,X0))
          | v2_struct_0(k7_filter_1(X1,X0)) )
        & ( ( l3_lattices(k7_filter_1(X1,X0))
            & v16_lattices(k7_filter_1(X1,X0))
            & v15_lattices(k7_filter_1(X1,X0))
            & v10_lattices(k7_filter_1(X1,X0))
            & ~ v2_struct_0(k7_filter_1(X1,X0)) )
          | ~ sP2(X0,X1) ) )
      | ~ sP3(X0,X1) ) ),
    inference(rectify,[],[f34])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v16_lattices(k7_filter_1(X1,X0))
      | ~ sP2(X0,X1)
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l3_lattices(X1)
            & v10_lattices(X1)
            & ~ v2_struct_0(X1) )
         => ( ( l3_lattices(X1)
              & v16_lattices(X1)
              & v15_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v16_lattices(X0)
              & v15_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
          <=> ( l3_lattices(k7_filter_1(X0,X1))
              & v16_lattices(k7_filter_1(X0,X1))
              & v15_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( l3_lattices(X1)
              & v16_lattices(X1)
              & v15_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v16_lattices(X0)
              & v15_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
          <=> ( l3_lattices(k7_filter_1(X0,X1))
              & v16_lattices(k7_filter_1(X0,X1))
              & v15_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) ) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( l3_lattices(X1)
              & v16_lattices(X1)
              & v15_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v16_lattices(X0)
              & v15_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
          <=> ( l3_lattices(k7_filter_1(X0,X1))
              & v16_lattices(k7_filter_1(X0,X1))
              & v15_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) ) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP3(X1,X0)
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f18,f25,f24])).

fof(f83,plain,(
    ! [X0,X1] :
      ( sP3(X1,X0)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(X1)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v10_lattices(X1)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f76,plain,(
    ! [X0,X1] :
      ( l3_lattices(X1)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(X0)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v10_lattices(X0)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f81,plain,(
    ! [X0,X1] :
      ( l3_lattices(X0)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v15_lattices(k7_filter_1(X1,X0))
      | ~ sP2(X0,X1)
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
      <=> ( l3_lattices(k7_filter_1(X0,X1))
          & v11_lattices(k7_filter_1(X0,X1))
          & v10_lattices(k7_filter_1(X0,X1))
          & ~ v2_struct_0(k7_filter_1(X0,X1)) ) )
      | ~ sP1(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ( ( sP0(X1,X0)
          | ~ l3_lattices(k7_filter_1(X0,X1))
          | ~ v11_lattices(k7_filter_1(X0,X1))
          | ~ v10_lattices(k7_filter_1(X0,X1))
          | v2_struct_0(k7_filter_1(X0,X1)) )
        & ( ( l3_lattices(k7_filter_1(X0,X1))
            & v11_lattices(k7_filter_1(X0,X1))
            & v10_lattices(k7_filter_1(X0,X1))
            & ~ v2_struct_0(k7_filter_1(X0,X1)) )
          | ~ sP0(X1,X0) ) )
      | ~ sP1(X1,X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ( ( sP0(X1,X0)
          | ~ l3_lattices(k7_filter_1(X0,X1))
          | ~ v11_lattices(k7_filter_1(X0,X1))
          | ~ v10_lattices(k7_filter_1(X0,X1))
          | v2_struct_0(k7_filter_1(X0,X1)) )
        & ( ( l3_lattices(k7_filter_1(X0,X1))
            & v11_lattices(k7_filter_1(X0,X1))
            & v10_lattices(k7_filter_1(X0,X1))
            & ~ v2_struct_0(k7_filter_1(X0,X1)) )
          | ~ sP0(X1,X0) ) )
      | ~ sP1(X1,X0) ) ),
    inference(flattening,[],[f27])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( sP0(X0,X1)
          | ~ l3_lattices(k7_filter_1(X1,X0))
          | ~ v11_lattices(k7_filter_1(X1,X0))
          | ~ v10_lattices(k7_filter_1(X1,X0))
          | v2_struct_0(k7_filter_1(X1,X0)) )
        & ( ( l3_lattices(k7_filter_1(X1,X0))
            & v11_lattices(k7_filter_1(X1,X0))
            & v10_lattices(k7_filter_1(X1,X0))
            & ~ v2_struct_0(k7_filter_1(X1,X0)) )
          | ~ sP0(X0,X1) ) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f28])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v11_lattices(k7_filter_1(X1,X0))
      | ~ sP0(X0,X1)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l3_lattices(X1)
            & v10_lattices(X1)
            & ~ v2_struct_0(X1) )
         => ( ( l3_lattices(X1)
              & v11_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v11_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
          <=> ( l3_lattices(k7_filter_1(X0,X1))
              & v11_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( l3_lattices(X1)
              & v11_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v11_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
          <=> ( l3_lattices(k7_filter_1(X0,X1))
              & v11_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) ) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( l3_lattices(X1)
              & v11_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v11_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
          <=> ( l3_lattices(k7_filter_1(X0,X1))
              & v11_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) ) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X1,X0)
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f16,f22,f21])).

fof(f65,plain,(
    ! [X0,X1] :
      ( sP1(X1,X0)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v10_lattices(X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f59,plain,(
    ! [X0,X1] :
      ( l3_lattices(X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v10_lattices(X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f63,plain,(
    ! [X0,X1] :
      ( l3_lattices(X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v10_lattices(k7_filter_1(X1,X0))
      | ~ sP0(X0,X1)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k7_filter_1(X1,X0))
      | ~ sP0(X0,X1)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v11_lattices(X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v11_lattices(X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f71,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
      | ~ l3_lattices(k7_filter_1(X1,X0))
      | ~ v16_lattices(k7_filter_1(X1,X0))
      | ~ v15_lattices(k7_filter_1(X1,X0))
      | ~ v10_lattices(k7_filter_1(X1,X0))
      | v2_struct_0(k7_filter_1(X1,X0))
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f55,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ l3_lattices(k7_filter_1(X1,X0))
      | ~ v11_lattices(k7_filter_1(X1,X0))
      | ~ v10_lattices(k7_filter_1(X1,X0))
      | v2_struct_0(k7_filter_1(X1,X0))
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l3_lattices(X1)
            & v10_lattices(X1)
            & ~ v2_struct_0(X1) )
         => ( ( l3_lattices(X1)
              & v17_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v17_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
          <=> ( l3_lattices(k7_filter_1(X0,X1))
              & v17_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l3_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1) )
           => ( ( l3_lattices(X1)
                & v17_lattices(X1)
                & v10_lattices(X1)
                & ~ v2_struct_0(X1)
                & l3_lattices(X0)
                & v17_lattices(X0)
                & v10_lattices(X0)
                & ~ v2_struct_0(X0) )
            <=> ( l3_lattices(k7_filter_1(X0,X1))
                & v17_lattices(k7_filter_1(X0,X1))
                & v10_lattices(k7_filter_1(X0,X1))
                & ~ v2_struct_0(k7_filter_1(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( l3_lattices(X1)
              & v17_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v17_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
          <~> ( l3_lattices(k7_filter_1(X0,X1))
              & v17_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) ) )
          & l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( l3_lattices(X1)
              & v17_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v17_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
          <~> ( l3_lattices(k7_filter_1(X0,X1))
              & v17_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) ) )
          & l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ l3_lattices(k7_filter_1(X0,X1))
            | ~ v17_lattices(k7_filter_1(X0,X1))
            | ~ v10_lattices(k7_filter_1(X0,X1))
            | v2_struct_0(k7_filter_1(X0,X1))
            | ~ l3_lattices(X1)
            | ~ v17_lattices(X1)
            | ~ v10_lattices(X1)
            | v2_struct_0(X1)
            | ~ l3_lattices(X0)
            | ~ v17_lattices(X0)
            | ~ v10_lattices(X0)
            | v2_struct_0(X0) )
          & ( ( l3_lattices(k7_filter_1(X0,X1))
              & v17_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) )
            | ( l3_lattices(X1)
              & v17_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v17_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) ) )
          & l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ l3_lattices(k7_filter_1(X0,X1))
            | ~ v17_lattices(k7_filter_1(X0,X1))
            | ~ v10_lattices(k7_filter_1(X0,X1))
            | v2_struct_0(k7_filter_1(X0,X1))
            | ~ l3_lattices(X1)
            | ~ v17_lattices(X1)
            | ~ v10_lattices(X1)
            | v2_struct_0(X1)
            | ~ l3_lattices(X0)
            | ~ v17_lattices(X0)
            | ~ v10_lattices(X0)
            | v2_struct_0(X0) )
          & ( ( l3_lattices(k7_filter_1(X0,X1))
              & v17_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) )
            | ( l3_lattices(X1)
              & v17_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v17_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) ) )
          & l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ l3_lattices(k7_filter_1(X0,X1))
            | ~ v17_lattices(k7_filter_1(X0,X1))
            | ~ v10_lattices(k7_filter_1(X0,X1))
            | v2_struct_0(k7_filter_1(X0,X1))
            | ~ l3_lattices(X1)
            | ~ v17_lattices(X1)
            | ~ v10_lattices(X1)
            | v2_struct_0(X1)
            | ~ l3_lattices(X0)
            | ~ v17_lattices(X0)
            | ~ v10_lattices(X0)
            | v2_struct_0(X0) )
          & ( ( l3_lattices(k7_filter_1(X0,X1))
              & v17_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) )
            | ( l3_lattices(X1)
              & v17_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v17_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) ) )
          & l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
     => ( ( ~ l3_lattices(k7_filter_1(X0,sK5))
          | ~ v17_lattices(k7_filter_1(X0,sK5))
          | ~ v10_lattices(k7_filter_1(X0,sK5))
          | v2_struct_0(k7_filter_1(X0,sK5))
          | ~ l3_lattices(sK5)
          | ~ v17_lattices(sK5)
          | ~ v10_lattices(sK5)
          | v2_struct_0(sK5)
          | ~ l3_lattices(X0)
          | ~ v17_lattices(X0)
          | ~ v10_lattices(X0)
          | v2_struct_0(X0) )
        & ( ( l3_lattices(k7_filter_1(X0,sK5))
            & v17_lattices(k7_filter_1(X0,sK5))
            & v10_lattices(k7_filter_1(X0,sK5))
            & ~ v2_struct_0(k7_filter_1(X0,sK5)) )
          | ( l3_lattices(sK5)
            & v17_lattices(sK5)
            & v10_lattices(sK5)
            & ~ v2_struct_0(sK5)
            & l3_lattices(X0)
            & v17_lattices(X0)
            & v10_lattices(X0)
            & ~ v2_struct_0(X0) ) )
        & l3_lattices(sK5)
        & v10_lattices(sK5)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ l3_lattices(k7_filter_1(X0,X1))
              | ~ v17_lattices(k7_filter_1(X0,X1))
              | ~ v10_lattices(k7_filter_1(X0,X1))
              | v2_struct_0(k7_filter_1(X0,X1))
              | ~ l3_lattices(X1)
              | ~ v17_lattices(X1)
              | ~ v10_lattices(X1)
              | v2_struct_0(X1)
              | ~ l3_lattices(X0)
              | ~ v17_lattices(X0)
              | ~ v10_lattices(X0)
              | v2_struct_0(X0) )
            & ( ( l3_lattices(k7_filter_1(X0,X1))
                & v17_lattices(k7_filter_1(X0,X1))
                & v10_lattices(k7_filter_1(X0,X1))
                & ~ v2_struct_0(k7_filter_1(X0,X1)) )
              | ( l3_lattices(X1)
                & v17_lattices(X1)
                & v10_lattices(X1)
                & ~ v2_struct_0(X1)
                & l3_lattices(X0)
                & v17_lattices(X0)
                & v10_lattices(X0)
                & ~ v2_struct_0(X0) ) )
            & l3_lattices(X1)
            & v10_lattices(X1)
            & ~ v2_struct_0(X1) )
        & l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ l3_lattices(k7_filter_1(sK4,X1))
            | ~ v17_lattices(k7_filter_1(sK4,X1))
            | ~ v10_lattices(k7_filter_1(sK4,X1))
            | v2_struct_0(k7_filter_1(sK4,X1))
            | ~ l3_lattices(X1)
            | ~ v17_lattices(X1)
            | ~ v10_lattices(X1)
            | v2_struct_0(X1)
            | ~ l3_lattices(sK4)
            | ~ v17_lattices(sK4)
            | ~ v10_lattices(sK4)
            | v2_struct_0(sK4) )
          & ( ( l3_lattices(k7_filter_1(sK4,X1))
              & v17_lattices(k7_filter_1(sK4,X1))
              & v10_lattices(k7_filter_1(sK4,X1))
              & ~ v2_struct_0(k7_filter_1(sK4,X1)) )
            | ( l3_lattices(X1)
              & v17_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(sK4)
              & v17_lattices(sK4)
              & v10_lattices(sK4)
              & ~ v2_struct_0(sK4) ) )
          & l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
      & l3_lattices(sK4)
      & v10_lattices(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ( ~ l3_lattices(k7_filter_1(sK4,sK5))
      | ~ v17_lattices(k7_filter_1(sK4,sK5))
      | ~ v10_lattices(k7_filter_1(sK4,sK5))
      | v2_struct_0(k7_filter_1(sK4,sK5))
      | ~ l3_lattices(sK5)
      | ~ v17_lattices(sK5)
      | ~ v10_lattices(sK5)
      | v2_struct_0(sK5)
      | ~ l3_lattices(sK4)
      | ~ v17_lattices(sK4)
      | ~ v10_lattices(sK4)
      | v2_struct_0(sK4) )
    & ( ( l3_lattices(k7_filter_1(sK4,sK5))
        & v17_lattices(k7_filter_1(sK4,sK5))
        & v10_lattices(k7_filter_1(sK4,sK5))
        & ~ v2_struct_0(k7_filter_1(sK4,sK5)) )
      | ( l3_lattices(sK5)
        & v17_lattices(sK5)
        & v10_lattices(sK5)
        & ~ v2_struct_0(sK5)
        & l3_lattices(sK4)
        & v17_lattices(sK4)
        & v10_lattices(sK4)
        & ~ v2_struct_0(sK4) ) )
    & l3_lattices(sK5)
    & v10_lattices(sK5)
    & ~ v2_struct_0(sK5)
    & l3_lattices(sK4)
    & v10_lattices(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f40,f42,f41])).

fof(f122,plain,
    ( ~ l3_lattices(k7_filter_1(sK4,sK5))
    | ~ v17_lattices(k7_filter_1(sK4,sK5))
    | ~ v10_lattices(k7_filter_1(sK4,sK5))
    | v2_struct_0(k7_filter_1(sK4,sK5))
    | ~ l3_lattices(sK5)
    | ~ v17_lattices(sK5)
    | ~ v10_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ l3_lattices(sK4)
    | ~ v17_lattices(sK4)
    | ~ v10_lattices(sK4)
    | v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f84,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f85,plain,(
    v10_lattices(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f86,plain,(
    l3_lattices(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f87,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f43])).

fof(f88,plain,(
    v10_lattices(sK5) ),
    inference(cnf_transformation,[],[f43])).

fof(f89,plain,(
    l3_lattices(sK5) ),
    inference(cnf_transformation,[],[f43])).

fof(f112,plain,
    ( v17_lattices(k7_filter_1(sK4,sK5))
    | v17_lattices(sK5) ),
    inference(cnf_transformation,[],[f43])).

fof(f108,plain,
    ( v17_lattices(k7_filter_1(sK4,sK5))
    | v17_lattices(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f104,plain,
    ( v10_lattices(k7_filter_1(sK4,sK5))
    | v17_lattices(sK5) ),
    inference(cnf_transformation,[],[f43])).

fof(f100,plain,
    ( v10_lattices(k7_filter_1(sK4,sK5))
    | v17_lattices(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f96,plain,
    ( ~ v2_struct_0(k7_filter_1(sK4,sK5))
    | v17_lattices(sK5) ),
    inference(cnf_transformation,[],[f43])).

fof(f92,plain,
    ( ~ v2_struct_0(k7_filter_1(sK4,sK5))
    | v17_lattices(sK4) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_0,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v17_lattices(X0)
    | v16_lattices(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2918,plain,
    ( ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ v17_lattices(sK5)
    | v16_lattices(sK5) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2919,plain,
    ( l3_lattices(sK5) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v17_lattices(sK5) != iProver_top
    | v16_lattices(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2918])).

cnf(c_4,plain,
    ( ~ v11_lattices(X0)
    | ~ v15_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | v17_lattices(X0)
    | ~ v16_lattices(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2894,plain,
    ( ~ v11_lattices(sK5)
    | ~ v15_lattices(sK5)
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | v17_lattices(sK5)
    | ~ v16_lattices(sK5) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2895,plain,
    ( v11_lattices(sK5) != iProver_top
    | v15_lattices(sK5) != iProver_top
    | l3_lattices(sK5) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v17_lattices(sK5) = iProver_top
    | v16_lattices(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2894])).

cnf(c_1,plain,
    ( v15_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v17_lattices(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2828,plain,
    ( v15_lattices(sK5)
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ v17_lattices(sK5) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2829,plain,
    ( v15_lattices(sK5) = iProver_top
    | l3_lattices(sK5) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v17_lattices(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2828])).

cnf(c_2,plain,
    ( v11_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v17_lattices(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2817,plain,
    ( v11_lattices(sK5)
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ v17_lattices(sK5) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2818,plain,
    ( v11_lattices(sK5) = iProver_top
    | l3_lattices(sK5) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v17_lattices(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2817])).

cnf(c_28,plain,
    ( sP2(X0,X1)
    | ~ v10_lattices(X0)
    | ~ v10_lattices(X1)
    | ~ v15_lattices(X0)
    | ~ v15_lattices(X1)
    | ~ l3_lattices(X0)
    | ~ l3_lattices(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v16_lattices(X0)
    | ~ v16_lattices(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2745,plain,
    ( sP2(sK5,sK4)
    | ~ v10_lattices(sK5)
    | ~ v10_lattices(sK4)
    | ~ v15_lattices(sK5)
    | ~ v15_lattices(sK4)
    | ~ l3_lattices(sK5)
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | ~ v16_lattices(sK5)
    | ~ v16_lattices(sK4) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_2746,plain,
    ( sP2(sK5,sK4) = iProver_top
    | v10_lattices(sK5) != iProver_top
    | v10_lattices(sK4) != iProver_top
    | v15_lattices(sK5) != iProver_top
    | v15_lattices(sK4) != iProver_top
    | l3_lattices(sK5) != iProver_top
    | l3_lattices(sK4) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v16_lattices(sK5) != iProver_top
    | v16_lattices(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2745])).

cnf(c_12,plain,
    ( sP0(X0,X1)
    | ~ v10_lattices(X0)
    | ~ v10_lattices(X1)
    | ~ v11_lattices(X0)
    | ~ v11_lattices(X1)
    | ~ l3_lattices(X0)
    | ~ l3_lattices(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2726,plain,
    ( sP0(sK5,sK4)
    | ~ v10_lattices(sK5)
    | ~ v10_lattices(sK4)
    | ~ v11_lattices(sK5)
    | ~ v11_lattices(sK4)
    | ~ l3_lattices(sK5)
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2728,plain,
    ( sP0(sK5,sK4) = iProver_top
    | v10_lattices(sK5) != iProver_top
    | v10_lattices(sK4) != iProver_top
    | v11_lattices(sK5) != iProver_top
    | v11_lattices(sK4) != iProver_top
    | l3_lattices(sK5) != iProver_top
    | l3_lattices(sK4) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2726])).

cnf(c_6,plain,
    ( ~ l3_lattices(X0)
    | ~ l3_lattices(X1)
    | l3_lattices(k7_filter_1(X0,X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2691,plain,
    ( l3_lattices(k7_filter_1(sK4,sK5))
    | ~ l3_lattices(sK5)
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2692,plain,
    ( l3_lattices(k7_filter_1(sK4,sK5)) = iProver_top
    | l3_lattices(sK5) != iProver_top
    | l3_lattices(sK4) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2691])).

cnf(c_36,plain,
    ( ~ sP2(X0,X1)
    | v15_lattices(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2647,plain,
    ( ~ sP2(sK5,sK4)
    | v15_lattices(sK4) ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_2669,plain,
    ( sP2(sK5,sK4) != iProver_top
    | v15_lattices(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2647])).

cnf(c_35,plain,
    ( ~ sP2(X0,X1)
    | v16_lattices(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2648,plain,
    ( ~ sP2(sK5,sK4)
    | v16_lattices(sK4) ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_2667,plain,
    ( sP2(sK5,sK4) != iProver_top
    | v16_lattices(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2648])).

cnf(c_31,plain,
    ( ~ sP2(X0,X1)
    | v15_lattices(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2649,plain,
    ( ~ sP2(sK5,sK4)
    | v15_lattices(sK5) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_2665,plain,
    ( sP2(sK5,sK4) != iProver_top
    | v15_lattices(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2649])).

cnf(c_30,plain,
    ( ~ sP2(X0,X1)
    | v16_lattices(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2650,plain,
    ( ~ sP2(sK5,sK4)
    | v16_lattices(sK5) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_2663,plain,
    ( sP2(sK5,sK4) != iProver_top
    | v16_lattices(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2650])).

cnf(c_24,plain,
    ( ~ sP3(X0,X1)
    | ~ sP2(X0,X1)
    | v16_lattices(k7_filter_1(X1,X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_39,plain,
    ( sP3(X0,X1)
    | ~ v10_lattices(X1)
    | ~ v10_lattices(X0)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_38,plain,
    ( ~ sP2(X0,X1)
    | ~ v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_37,plain,
    ( ~ sP2(X0,X1)
    | v10_lattices(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_34,plain,
    ( ~ sP2(X0,X1)
    | l3_lattices(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_33,plain,
    ( ~ sP2(X0,X1)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_32,plain,
    ( ~ sP2(X0,X1)
    | v10_lattices(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_29,plain,
    ( ~ sP2(X0,X1)
    | l3_lattices(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_535,plain,
    ( ~ sP2(X0,X1)
    | v16_lattices(k7_filter_1(X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_24,c_39,c_38,c_37,c_34,c_33,c_32,c_29])).

cnf(c_2651,plain,
    ( ~ sP2(sK5,sK4)
    | v16_lattices(k7_filter_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_535])).

cnf(c_2661,plain,
    ( sP2(sK5,sK4) != iProver_top
    | v16_lattices(k7_filter_1(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2651])).

cnf(c_25,plain,
    ( ~ sP3(X0,X1)
    | ~ sP2(X0,X1)
    | v15_lattices(k7_filter_1(X1,X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_528,plain,
    ( ~ sP2(X0,X1)
    | v15_lattices(k7_filter_1(X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_25,c_39,c_38,c_37,c_34,c_33,c_32,c_29])).

cnf(c_2652,plain,
    ( ~ sP2(sK5,sK4)
    | v15_lattices(k7_filter_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_528])).

cnf(c_2659,plain,
    ( sP2(sK5,sK4) != iProver_top
    | v15_lattices(k7_filter_1(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2652])).

cnf(c_9,plain,
    ( ~ sP1(X0,X1)
    | ~ sP0(X0,X1)
    | v11_lattices(k7_filter_1(X1,X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_21,plain,
    ( sP1(X0,X1)
    | ~ v10_lattices(X1)
    | ~ v10_lattices(X0)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_20,plain,
    ( ~ sP0(X0,X1)
    | ~ v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_19,plain,
    ( ~ sP0(X0,X1)
    | v10_lattices(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_17,plain,
    ( ~ sP0(X0,X1)
    | l3_lattices(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_16,plain,
    ( ~ sP0(X0,X1)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_15,plain,
    ( ~ sP0(X0,X1)
    | v10_lattices(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_13,plain,
    ( ~ sP0(X0,X1)
    | l3_lattices(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_574,plain,
    ( ~ sP0(X0,X1)
    | v11_lattices(k7_filter_1(X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_21,c_20,c_19,c_17,c_16,c_15,c_13])).

cnf(c_2632,plain,
    ( ~ sP0(sK5,sK4)
    | v11_lattices(k7_filter_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_574])).

cnf(c_2645,plain,
    ( sP0(sK5,sK4) != iProver_top
    | v11_lattices(k7_filter_1(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2632])).

cnf(c_10,plain,
    ( ~ sP1(X0,X1)
    | ~ sP0(X0,X1)
    | v10_lattices(k7_filter_1(X1,X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_567,plain,
    ( ~ sP0(X0,X1)
    | v10_lattices(k7_filter_1(X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_21,c_20,c_19,c_17,c_16,c_15,c_13])).

cnf(c_2633,plain,
    ( ~ sP0(sK5,sK4)
    | v10_lattices(k7_filter_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_567])).

cnf(c_2643,plain,
    ( sP0(sK5,sK4) != iProver_top
    | v10_lattices(k7_filter_1(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2633])).

cnf(c_11,plain,
    ( ~ sP1(X0,X1)
    | ~ sP0(X0,X1)
    | ~ v2_struct_0(k7_filter_1(X1,X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_560,plain,
    ( ~ sP0(X0,X1)
    | ~ v2_struct_0(k7_filter_1(X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_21,c_20,c_19,c_17,c_16,c_15,c_13])).

cnf(c_2634,plain,
    ( ~ sP0(sK5,sK4)
    | ~ v2_struct_0(k7_filter_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_560])).

cnf(c_2641,plain,
    ( sP0(sK5,sK4) != iProver_top
    | v2_struct_0(k7_filter_1(sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2634])).

cnf(c_18,plain,
    ( ~ sP0(X0,X1)
    | v11_lattices(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2635,plain,
    ( ~ sP0(sK5,sK4)
    | v11_lattices(sK4) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2639,plain,
    ( sP0(sK5,sK4) != iProver_top
    | v11_lattices(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2635])).

cnf(c_14,plain,
    ( ~ sP0(X0,X1)
    | v11_lattices(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2636,plain,
    ( ~ sP0(sK5,sK4)
    | v11_lattices(sK5) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2637,plain,
    ( sP0(sK5,sK4) != iProver_top
    | v11_lattices(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2636])).

cnf(c_2625,plain,
    ( ~ v11_lattices(k7_filter_1(sK4,sK5))
    | ~ v15_lattices(k7_filter_1(sK4,sK5))
    | ~ l3_lattices(k7_filter_1(sK4,sK5))
    | v2_struct_0(k7_filter_1(sK4,sK5))
    | v17_lattices(k7_filter_1(sK4,sK5))
    | ~ v16_lattices(k7_filter_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2626,plain,
    ( v11_lattices(k7_filter_1(sK4,sK5)) != iProver_top
    | v15_lattices(k7_filter_1(sK4,sK5)) != iProver_top
    | l3_lattices(k7_filter_1(sK4,sK5)) != iProver_top
    | v2_struct_0(k7_filter_1(sK4,sK5)) = iProver_top
    | v17_lattices(k7_filter_1(sK4,sK5)) = iProver_top
    | v16_lattices(k7_filter_1(sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2625])).

cnf(c_22,plain,
    ( ~ sP3(X0,X1)
    | sP2(X0,X1)
    | ~ v10_lattices(k7_filter_1(X1,X0))
    | ~ v15_lattices(k7_filter_1(X1,X0))
    | ~ l3_lattices(k7_filter_1(X1,X0))
    | v2_struct_0(k7_filter_1(X1,X0))
    | ~ v16_lattices(k7_filter_1(X1,X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_891,plain,
    ( sP2(X0,X1)
    | ~ v10_lattices(X0)
    | ~ v10_lattices(X1)
    | ~ v10_lattices(k7_filter_1(X1,X0))
    | ~ v15_lattices(k7_filter_1(X1,X0))
    | ~ l3_lattices(X0)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(k7_filter_1(X1,X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(k7_filter_1(X1,X0))
    | ~ v16_lattices(k7_filter_1(X1,X0)) ),
    inference(resolution,[status(thm)],[c_39,c_22])).

cnf(c_919,plain,
    ( sP2(X0,X1)
    | ~ v10_lattices(X0)
    | ~ v10_lattices(X1)
    | ~ v10_lattices(k7_filter_1(X1,X0))
    | ~ v15_lattices(k7_filter_1(X1,X0))
    | ~ l3_lattices(X0)
    | ~ l3_lattices(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(k7_filter_1(X1,X0))
    | ~ v16_lattices(k7_filter_1(X1,X0)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_891,c_6])).

cnf(c_2616,plain,
    ( sP2(sK5,sK4)
    | ~ v10_lattices(k7_filter_1(sK4,sK5))
    | ~ v10_lattices(sK5)
    | ~ v10_lattices(sK4)
    | ~ v15_lattices(k7_filter_1(sK4,sK5))
    | ~ l3_lattices(sK5)
    | ~ l3_lattices(sK4)
    | v2_struct_0(k7_filter_1(sK4,sK5))
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | ~ v16_lattices(k7_filter_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_919])).

cnf(c_2617,plain,
    ( sP2(sK5,sK4) = iProver_top
    | v10_lattices(k7_filter_1(sK4,sK5)) != iProver_top
    | v10_lattices(sK5) != iProver_top
    | v10_lattices(sK4) != iProver_top
    | v15_lattices(k7_filter_1(sK4,sK5)) != iProver_top
    | l3_lattices(sK5) != iProver_top
    | l3_lattices(sK4) != iProver_top
    | v2_struct_0(k7_filter_1(sK4,sK5)) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v16_lattices(k7_filter_1(sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2616])).

cnf(c_7,plain,
    ( ~ sP1(X0,X1)
    | sP0(X0,X1)
    | ~ v10_lattices(k7_filter_1(X1,X0))
    | ~ v11_lattices(k7_filter_1(X1,X0))
    | ~ l3_lattices(k7_filter_1(X1,X0))
    | v2_struct_0(k7_filter_1(X1,X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_840,plain,
    ( sP0(X0,X1)
    | ~ v10_lattices(X0)
    | ~ v10_lattices(X1)
    | ~ v10_lattices(k7_filter_1(X1,X0))
    | ~ v11_lattices(k7_filter_1(X1,X0))
    | ~ l3_lattices(X0)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(k7_filter_1(X1,X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(k7_filter_1(X1,X0)) ),
    inference(resolution,[status(thm)],[c_21,c_7])).

cnf(c_866,plain,
    ( sP0(X0,X1)
    | ~ v10_lattices(X0)
    | ~ v10_lattices(X1)
    | ~ v10_lattices(k7_filter_1(X1,X0))
    | ~ v11_lattices(k7_filter_1(X1,X0))
    | ~ l3_lattices(X0)
    | ~ l3_lattices(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(k7_filter_1(X1,X0)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_840,c_6])).

cnf(c_2609,plain,
    ( sP0(sK5,sK4)
    | ~ v10_lattices(k7_filter_1(sK4,sK5))
    | ~ v10_lattices(sK5)
    | ~ v10_lattices(sK4)
    | ~ v11_lattices(k7_filter_1(sK4,sK5))
    | ~ l3_lattices(sK5)
    | ~ l3_lattices(sK4)
    | v2_struct_0(k7_filter_1(sK4,sK5))
    | v2_struct_0(sK5)
    | v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_866])).

cnf(c_2610,plain,
    ( sP0(sK5,sK4) = iProver_top
    | v10_lattices(k7_filter_1(sK4,sK5)) != iProver_top
    | v10_lattices(sK5) != iProver_top
    | v10_lattices(sK4) != iProver_top
    | v11_lattices(k7_filter_1(sK4,sK5)) != iProver_top
    | l3_lattices(sK5) != iProver_top
    | l3_lattices(sK4) != iProver_top
    | v2_struct_0(k7_filter_1(sK4,sK5)) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2609])).

cnf(c_2586,plain,
    ( v11_lattices(k7_filter_1(sK4,sK5))
    | ~ l3_lattices(k7_filter_1(sK4,sK5))
    | v2_struct_0(k7_filter_1(sK4,sK5))
    | ~ v17_lattices(k7_filter_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2587,plain,
    ( v11_lattices(k7_filter_1(sK4,sK5)) = iProver_top
    | l3_lattices(k7_filter_1(sK4,sK5)) != iProver_top
    | v2_struct_0(k7_filter_1(sK4,sK5)) = iProver_top
    | v17_lattices(k7_filter_1(sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2586])).

cnf(c_2583,plain,
    ( v15_lattices(k7_filter_1(sK4,sK5))
    | ~ l3_lattices(k7_filter_1(sK4,sK5))
    | v2_struct_0(k7_filter_1(sK4,sK5))
    | ~ v17_lattices(k7_filter_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2584,plain,
    ( v15_lattices(k7_filter_1(sK4,sK5)) = iProver_top
    | l3_lattices(k7_filter_1(sK4,sK5)) != iProver_top
    | v2_struct_0(k7_filter_1(sK4,sK5)) = iProver_top
    | v17_lattices(k7_filter_1(sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2583])).

cnf(c_2580,plain,
    ( ~ l3_lattices(k7_filter_1(sK4,sK5))
    | v2_struct_0(k7_filter_1(sK4,sK5))
    | ~ v17_lattices(k7_filter_1(sK4,sK5))
    | v16_lattices(k7_filter_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2581,plain,
    ( l3_lattices(k7_filter_1(sK4,sK5)) != iProver_top
    | v2_struct_0(k7_filter_1(sK4,sK5)) = iProver_top
    | v17_lattices(k7_filter_1(sK4,sK5)) != iProver_top
    | v16_lattices(k7_filter_1(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2580])).

cnf(c_40,negated_conjecture,
    ( ~ v10_lattices(k7_filter_1(sK4,sK5))
    | ~ v10_lattices(sK5)
    | ~ v10_lattices(sK4)
    | ~ l3_lattices(k7_filter_1(sK4,sK5))
    | ~ l3_lattices(sK5)
    | ~ l3_lattices(sK4)
    | v2_struct_0(k7_filter_1(sK4,sK5))
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | ~ v17_lattices(k7_filter_1(sK4,sK5))
    | ~ v17_lattices(sK5)
    | ~ v17_lattices(sK4) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_78,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_77,negated_conjecture,
    ( v10_lattices(sK4) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_76,negated_conjecture,
    ( l3_lattices(sK4) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_75,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_74,negated_conjecture,
    ( v10_lattices(sK5) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_73,negated_conjecture,
    ( l3_lattices(sK5) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_497,negated_conjecture,
    ( ~ v10_lattices(k7_filter_1(sK4,sK5))
    | ~ l3_lattices(k7_filter_1(sK4,sK5))
    | v2_struct_0(k7_filter_1(sK4,sK5))
    | ~ v17_lattices(k7_filter_1(sK4,sK5))
    | ~ v17_lattices(sK5)
    | ~ v17_lattices(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_40,c_78,c_77,c_76,c_75,c_74,c_73])).

cnf(c_499,plain,
    ( v10_lattices(k7_filter_1(sK4,sK5)) != iProver_top
    | l3_lattices(k7_filter_1(sK4,sK5)) != iProver_top
    | v2_struct_0(k7_filter_1(sK4,sK5)) = iProver_top
    | v17_lattices(k7_filter_1(sK4,sK5)) != iProver_top
    | v17_lattices(sK5) != iProver_top
    | v17_lattices(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_497])).

cnf(c_201,plain,
    ( l3_lattices(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v17_lattices(X0) != iProver_top
    | v16_lattices(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_203,plain,
    ( l3_lattices(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v17_lattices(sK4) != iProver_top
    | v16_lattices(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_201])).

cnf(c_198,plain,
    ( v15_lattices(X0) = iProver_top
    | l3_lattices(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v17_lattices(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_200,plain,
    ( v15_lattices(sK4) = iProver_top
    | l3_lattices(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v17_lattices(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_198])).

cnf(c_195,plain,
    ( v11_lattices(X0) = iProver_top
    | l3_lattices(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v17_lattices(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_197,plain,
    ( v11_lattices(sK4) = iProver_top
    | l3_lattices(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v17_lattices(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_195])).

cnf(c_191,plain,
    ( v11_lattices(X0) != iProver_top
    | v15_lattices(X0) != iProver_top
    | l3_lattices(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v17_lattices(X0) = iProver_top
    | v16_lattices(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_193,plain,
    ( v11_lattices(sK4) != iProver_top
    | v15_lattices(sK4) != iProver_top
    | l3_lattices(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v17_lattices(sK4) = iProver_top
    | v16_lattices(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_191])).

cnf(c_50,negated_conjecture,
    ( v17_lattices(k7_filter_1(sK4,sK5))
    | v17_lattices(sK5) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_107,plain,
    ( v17_lattices(k7_filter_1(sK4,sK5)) = iProver_top
    | v17_lattices(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_54,negated_conjecture,
    ( v17_lattices(k7_filter_1(sK4,sK5))
    | v17_lattices(sK4) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_103,plain,
    ( v17_lattices(k7_filter_1(sK4,sK5)) = iProver_top
    | v17_lattices(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_58,negated_conjecture,
    ( v10_lattices(k7_filter_1(sK4,sK5))
    | v17_lattices(sK5) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_99,plain,
    ( v10_lattices(k7_filter_1(sK4,sK5)) = iProver_top
    | v17_lattices(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58])).

cnf(c_62,negated_conjecture,
    ( v10_lattices(k7_filter_1(sK4,sK5))
    | v17_lattices(sK4) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_95,plain,
    ( v10_lattices(k7_filter_1(sK4,sK5)) = iProver_top
    | v17_lattices(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_62])).

cnf(c_66,negated_conjecture,
    ( ~ v2_struct_0(k7_filter_1(sK4,sK5))
    | v17_lattices(sK5) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_91,plain,
    ( v2_struct_0(k7_filter_1(sK4,sK5)) != iProver_top
    | v17_lattices(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_66])).

cnf(c_70,negated_conjecture,
    ( ~ v2_struct_0(k7_filter_1(sK4,sK5))
    | v17_lattices(sK4) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_87,plain,
    ( v2_struct_0(k7_filter_1(sK4,sK5)) != iProver_top
    | v17_lattices(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_70])).

cnf(c_84,plain,
    ( l3_lattices(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_73])).

cnf(c_83,plain,
    ( v10_lattices(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_74])).

cnf(c_82,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_75])).

cnf(c_81,plain,
    ( l3_lattices(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_76])).

cnf(c_80,plain,
    ( v10_lattices(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_77])).

cnf(c_79,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_78])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2919,c_2895,c_2829,c_2818,c_2746,c_2728,c_2692,c_2669,c_2667,c_2665,c_2663,c_2661,c_2659,c_2645,c_2643,c_2641,c_2639,c_2637,c_2626,c_2617,c_2610,c_2587,c_2584,c_2581,c_499,c_203,c_200,c_197,c_193,c_107,c_103,c_99,c_95,c_91,c_87,c_84,c_83,c_82,c_81,c_80,c_79])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:54:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.02/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.01  
% 2.02/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.02/1.01  
% 2.02/1.01  ------  iProver source info
% 2.02/1.01  
% 2.02/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.02/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.02/1.01  git: non_committed_changes: false
% 2.02/1.01  git: last_make_outside_of_git: false
% 2.02/1.01  
% 2.02/1.01  ------ 
% 2.02/1.01  
% 2.02/1.01  ------ Input Options
% 2.02/1.01  
% 2.02/1.01  --out_options                           all
% 2.02/1.01  --tptp_safe_out                         true
% 2.02/1.01  --problem_path                          ""
% 2.02/1.01  --include_path                          ""
% 2.02/1.01  --clausifier                            res/vclausify_rel
% 2.02/1.01  --clausifier_options                    --mode clausify
% 2.02/1.01  --stdin                                 false
% 2.02/1.01  --stats_out                             all
% 2.02/1.01  
% 2.02/1.01  ------ General Options
% 2.02/1.01  
% 2.02/1.01  --fof                                   false
% 2.02/1.01  --time_out_real                         305.
% 2.02/1.01  --time_out_virtual                      -1.
% 2.02/1.01  --symbol_type_check                     false
% 2.02/1.01  --clausify_out                          false
% 2.02/1.01  --sig_cnt_out                           false
% 2.02/1.01  --trig_cnt_out                          false
% 2.02/1.01  --trig_cnt_out_tolerance                1.
% 2.02/1.01  --trig_cnt_out_sk_spl                   false
% 2.02/1.01  --abstr_cl_out                          false
% 2.02/1.01  
% 2.02/1.01  ------ Global Options
% 2.02/1.01  
% 2.02/1.01  --schedule                              default
% 2.02/1.01  --add_important_lit                     false
% 2.02/1.01  --prop_solver_per_cl                    1000
% 2.02/1.01  --min_unsat_core                        false
% 2.02/1.01  --soft_assumptions                      false
% 2.02/1.01  --soft_lemma_size                       3
% 2.02/1.01  --prop_impl_unit_size                   0
% 2.02/1.01  --prop_impl_unit                        []
% 2.02/1.01  --share_sel_clauses                     true
% 2.02/1.01  --reset_solvers                         false
% 2.02/1.01  --bc_imp_inh                            [conj_cone]
% 2.02/1.01  --conj_cone_tolerance                   3.
% 2.02/1.01  --extra_neg_conj                        none
% 2.02/1.01  --large_theory_mode                     true
% 2.02/1.01  --prolific_symb_bound                   200
% 2.02/1.01  --lt_threshold                          2000
% 2.02/1.01  --clause_weak_htbl                      true
% 2.02/1.01  --gc_record_bc_elim                     false
% 2.02/1.01  
% 2.02/1.01  ------ Preprocessing Options
% 2.02/1.01  
% 2.02/1.01  --preprocessing_flag                    true
% 2.02/1.01  --time_out_prep_mult                    0.1
% 2.02/1.01  --splitting_mode                        input
% 2.02/1.01  --splitting_grd                         true
% 2.02/1.01  --splitting_cvd                         false
% 2.02/1.01  --splitting_cvd_svl                     false
% 2.02/1.01  --splitting_nvd                         32
% 2.02/1.01  --sub_typing                            true
% 2.02/1.01  --prep_gs_sim                           true
% 2.02/1.01  --prep_unflatten                        true
% 2.02/1.01  --prep_res_sim                          true
% 2.02/1.01  --prep_upred                            true
% 2.02/1.01  --prep_sem_filter                       exhaustive
% 2.02/1.01  --prep_sem_filter_out                   false
% 2.02/1.01  --pred_elim                             true
% 2.02/1.01  --res_sim_input                         true
% 2.02/1.01  --eq_ax_congr_red                       true
% 2.02/1.01  --pure_diseq_elim                       true
% 2.02/1.01  --brand_transform                       false
% 2.02/1.01  --non_eq_to_eq                          false
% 2.02/1.01  --prep_def_merge                        true
% 2.02/1.01  --prep_def_merge_prop_impl              false
% 2.02/1.01  --prep_def_merge_mbd                    true
% 2.02/1.01  --prep_def_merge_tr_red                 false
% 2.02/1.01  --prep_def_merge_tr_cl                  false
% 2.02/1.01  --smt_preprocessing                     true
% 2.02/1.01  --smt_ac_axioms                         fast
% 2.02/1.01  --preprocessed_out                      false
% 2.02/1.01  --preprocessed_stats                    false
% 2.02/1.01  
% 2.02/1.01  ------ Abstraction refinement Options
% 2.02/1.01  
% 2.02/1.01  --abstr_ref                             []
% 2.02/1.01  --abstr_ref_prep                        false
% 2.02/1.01  --abstr_ref_until_sat                   false
% 2.02/1.01  --abstr_ref_sig_restrict                funpre
% 2.02/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.02/1.01  --abstr_ref_under                       []
% 2.02/1.01  
% 2.02/1.01  ------ SAT Options
% 2.02/1.01  
% 2.02/1.01  --sat_mode                              false
% 2.02/1.01  --sat_fm_restart_options                ""
% 2.02/1.01  --sat_gr_def                            false
% 2.02/1.01  --sat_epr_types                         true
% 2.02/1.01  --sat_non_cyclic_types                  false
% 2.02/1.01  --sat_finite_models                     false
% 2.02/1.01  --sat_fm_lemmas                         false
% 2.02/1.01  --sat_fm_prep                           false
% 2.02/1.01  --sat_fm_uc_incr                        true
% 2.02/1.01  --sat_out_model                         small
% 2.02/1.01  --sat_out_clauses                       false
% 2.02/1.01  
% 2.02/1.01  ------ QBF Options
% 2.02/1.01  
% 2.02/1.01  --qbf_mode                              false
% 2.02/1.01  --qbf_elim_univ                         false
% 2.02/1.01  --qbf_dom_inst                          none
% 2.02/1.01  --qbf_dom_pre_inst                      false
% 2.02/1.01  --qbf_sk_in                             false
% 2.02/1.01  --qbf_pred_elim                         true
% 2.02/1.01  --qbf_split                             512
% 2.02/1.01  
% 2.02/1.01  ------ BMC1 Options
% 2.02/1.01  
% 2.02/1.01  --bmc1_incremental                      false
% 2.02/1.01  --bmc1_axioms                           reachable_all
% 2.02/1.01  --bmc1_min_bound                        0
% 2.02/1.01  --bmc1_max_bound                        -1
% 2.02/1.01  --bmc1_max_bound_default                -1
% 2.02/1.01  --bmc1_symbol_reachability              true
% 2.02/1.01  --bmc1_property_lemmas                  false
% 2.02/1.01  --bmc1_k_induction                      false
% 2.02/1.01  --bmc1_non_equiv_states                 false
% 2.02/1.01  --bmc1_deadlock                         false
% 2.02/1.01  --bmc1_ucm                              false
% 2.02/1.01  --bmc1_add_unsat_core                   none
% 2.02/1.01  --bmc1_unsat_core_children              false
% 2.02/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.02/1.01  --bmc1_out_stat                         full
% 2.02/1.01  --bmc1_ground_init                      false
% 2.02/1.01  --bmc1_pre_inst_next_state              false
% 2.02/1.01  --bmc1_pre_inst_state                   false
% 2.02/1.01  --bmc1_pre_inst_reach_state             false
% 2.02/1.01  --bmc1_out_unsat_core                   false
% 2.02/1.01  --bmc1_aig_witness_out                  false
% 2.02/1.01  --bmc1_verbose                          false
% 2.02/1.01  --bmc1_dump_clauses_tptp                false
% 2.02/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.02/1.01  --bmc1_dump_file                        -
% 2.02/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.02/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.02/1.01  --bmc1_ucm_extend_mode                  1
% 2.02/1.01  --bmc1_ucm_init_mode                    2
% 2.02/1.01  --bmc1_ucm_cone_mode                    none
% 2.02/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.02/1.01  --bmc1_ucm_relax_model                  4
% 2.02/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.02/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.02/1.01  --bmc1_ucm_layered_model                none
% 2.02/1.01  --bmc1_ucm_max_lemma_size               10
% 2.02/1.01  
% 2.02/1.01  ------ AIG Options
% 2.02/1.01  
% 2.02/1.01  --aig_mode                              false
% 2.02/1.01  
% 2.02/1.01  ------ Instantiation Options
% 2.02/1.01  
% 2.02/1.01  --instantiation_flag                    true
% 2.02/1.01  --inst_sos_flag                         false
% 2.02/1.01  --inst_sos_phase                        true
% 2.02/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.02/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.02/1.01  --inst_lit_sel_side                     num_symb
% 2.02/1.01  --inst_solver_per_active                1400
% 2.02/1.01  --inst_solver_calls_frac                1.
% 2.02/1.01  --inst_passive_queue_type               priority_queues
% 2.02/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.02/1.01  --inst_passive_queues_freq              [25;2]
% 2.02/1.01  --inst_dismatching                      true
% 2.02/1.01  --inst_eager_unprocessed_to_passive     true
% 2.02/1.01  --inst_prop_sim_given                   true
% 2.02/1.01  --inst_prop_sim_new                     false
% 2.02/1.01  --inst_subs_new                         false
% 2.02/1.01  --inst_eq_res_simp                      false
% 2.02/1.01  --inst_subs_given                       false
% 2.02/1.01  --inst_orphan_elimination               true
% 2.02/1.01  --inst_learning_loop_flag               true
% 2.02/1.01  --inst_learning_start                   3000
% 2.02/1.01  --inst_learning_factor                  2
% 2.02/1.01  --inst_start_prop_sim_after_learn       3
% 2.02/1.01  --inst_sel_renew                        solver
% 2.02/1.01  --inst_lit_activity_flag                true
% 2.02/1.01  --inst_restr_to_given                   false
% 2.02/1.01  --inst_activity_threshold               500
% 2.02/1.01  --inst_out_proof                        true
% 2.02/1.01  
% 2.02/1.01  ------ Resolution Options
% 2.02/1.01  
% 2.02/1.01  --resolution_flag                       true
% 2.02/1.01  --res_lit_sel                           adaptive
% 2.02/1.01  --res_lit_sel_side                      none
% 2.02/1.01  --res_ordering                          kbo
% 2.02/1.01  --res_to_prop_solver                    active
% 2.02/1.01  --res_prop_simpl_new                    false
% 2.02/1.01  --res_prop_simpl_given                  true
% 2.02/1.01  --res_passive_queue_type                priority_queues
% 2.02/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.02/1.01  --res_passive_queues_freq               [15;5]
% 2.02/1.01  --res_forward_subs                      full
% 2.02/1.01  --res_backward_subs                     full
% 2.02/1.01  --res_forward_subs_resolution           true
% 2.02/1.01  --res_backward_subs_resolution          true
% 2.02/1.01  --res_orphan_elimination                true
% 2.02/1.01  --res_time_limit                        2.
% 2.02/1.01  --res_out_proof                         true
% 2.02/1.01  
% 2.02/1.01  ------ Superposition Options
% 2.02/1.01  
% 2.02/1.01  --superposition_flag                    true
% 2.02/1.01  --sup_passive_queue_type                priority_queues
% 2.02/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.02/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.02/1.01  --demod_completeness_check              fast
% 2.02/1.01  --demod_use_ground                      true
% 2.02/1.01  --sup_to_prop_solver                    passive
% 2.02/1.01  --sup_prop_simpl_new                    true
% 2.02/1.01  --sup_prop_simpl_given                  true
% 2.02/1.01  --sup_fun_splitting                     false
% 2.02/1.01  --sup_smt_interval                      50000
% 2.02/1.01  
% 2.02/1.01  ------ Superposition Simplification Setup
% 2.02/1.01  
% 2.02/1.01  --sup_indices_passive                   []
% 2.02/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.02/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.02/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.02/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.02/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.02/1.01  --sup_full_bw                           [BwDemod]
% 2.02/1.01  --sup_immed_triv                        [TrivRules]
% 2.02/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.02/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.02/1.01  --sup_immed_bw_main                     []
% 2.02/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.02/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.02/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.02/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.02/1.01  
% 2.02/1.01  ------ Combination Options
% 2.02/1.01  
% 2.02/1.01  --comb_res_mult                         3
% 2.02/1.01  --comb_sup_mult                         2
% 2.02/1.01  --comb_inst_mult                        10
% 2.02/1.01  
% 2.02/1.01  ------ Debug Options
% 2.02/1.01  
% 2.02/1.01  --dbg_backtrace                         false
% 2.02/1.01  --dbg_dump_prop_clauses                 false
% 2.02/1.01  --dbg_dump_prop_clauses_file            -
% 2.02/1.01  --dbg_out_stat                          false
% 2.02/1.01  ------ Parsing...
% 2.02/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.02/1.01  
% 2.02/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 2.02/1.01  
% 2.02/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.02/1.01  ------ Proving...
% 2.02/1.01  ------ Problem Properties 
% 2.02/1.01  
% 2.02/1.01  
% 2.02/1.01  clauses                                 51
% 2.02/1.01  conjectures                             15
% 2.02/1.01  EPR                                     30
% 2.02/1.01  Horn                                    36
% 2.02/1.01  unary                                   6
% 2.02/1.01  binary                                  35
% 2.02/1.01  lits                                    146
% 2.02/1.01  lits eq                                 0
% 2.02/1.01  fd_pure                                 0
% 2.02/1.01  fd_pseudo                               0
% 2.02/1.01  fd_cond                                 0
% 2.02/1.01  fd_pseudo_cond                          0
% 2.02/1.01  AC symbols                              0
% 2.02/1.01  
% 2.02/1.01  ------ Schedule dynamic 5 is on 
% 2.02/1.01  
% 2.02/1.01  ------ no equalities: superposition off 
% 2.02/1.01  
% 2.02/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.02/1.01  
% 2.02/1.01  
% 2.02/1.01  ------ 
% 2.02/1.01  Current options:
% 2.02/1.01  ------ 
% 2.02/1.01  
% 2.02/1.01  ------ Input Options
% 2.02/1.01  
% 2.02/1.01  --out_options                           all
% 2.02/1.01  --tptp_safe_out                         true
% 2.02/1.01  --problem_path                          ""
% 2.02/1.01  --include_path                          ""
% 2.02/1.01  --clausifier                            res/vclausify_rel
% 2.02/1.01  --clausifier_options                    --mode clausify
% 2.02/1.01  --stdin                                 false
% 2.02/1.01  --stats_out                             all
% 2.02/1.01  
% 2.02/1.01  ------ General Options
% 2.02/1.01  
% 2.02/1.01  --fof                                   false
% 2.02/1.01  --time_out_real                         305.
% 2.02/1.01  --time_out_virtual                      -1.
% 2.02/1.01  --symbol_type_check                     false
% 2.02/1.01  --clausify_out                          false
% 2.02/1.01  --sig_cnt_out                           false
% 2.02/1.01  --trig_cnt_out                          false
% 2.02/1.01  --trig_cnt_out_tolerance                1.
% 2.02/1.01  --trig_cnt_out_sk_spl                   false
% 2.02/1.01  --abstr_cl_out                          false
% 2.02/1.01  
% 2.02/1.01  ------ Global Options
% 2.02/1.01  
% 2.02/1.01  --schedule                              default
% 2.02/1.01  --add_important_lit                     false
% 2.02/1.01  --prop_solver_per_cl                    1000
% 2.02/1.01  --min_unsat_core                        false
% 2.02/1.01  --soft_assumptions                      false
% 2.02/1.01  --soft_lemma_size                       3
% 2.02/1.01  --prop_impl_unit_size                   0
% 2.02/1.01  --prop_impl_unit                        []
% 2.02/1.01  --share_sel_clauses                     true
% 2.02/1.01  --reset_solvers                         false
% 2.02/1.01  --bc_imp_inh                            [conj_cone]
% 2.02/1.01  --conj_cone_tolerance                   3.
% 2.02/1.01  --extra_neg_conj                        none
% 2.02/1.01  --large_theory_mode                     true
% 2.02/1.01  --prolific_symb_bound                   200
% 2.02/1.01  --lt_threshold                          2000
% 2.02/1.01  --clause_weak_htbl                      true
% 2.02/1.01  --gc_record_bc_elim                     false
% 2.02/1.01  
% 2.02/1.01  ------ Preprocessing Options
% 2.02/1.01  
% 2.02/1.01  --preprocessing_flag                    true
% 2.02/1.01  --time_out_prep_mult                    0.1
% 2.02/1.01  --splitting_mode                        input
% 2.02/1.01  --splitting_grd                         true
% 2.02/1.01  --splitting_cvd                         false
% 2.02/1.01  --splitting_cvd_svl                     false
% 2.02/1.01  --splitting_nvd                         32
% 2.02/1.01  --sub_typing                            true
% 2.02/1.01  --prep_gs_sim                           true
% 2.02/1.01  --prep_unflatten                        true
% 2.02/1.01  --prep_res_sim                          true
% 2.02/1.01  --prep_upred                            true
% 2.02/1.01  --prep_sem_filter                       exhaustive
% 2.02/1.01  --prep_sem_filter_out                   false
% 2.02/1.01  --pred_elim                             true
% 2.02/1.01  --res_sim_input                         true
% 2.02/1.01  --eq_ax_congr_red                       true
% 2.02/1.01  --pure_diseq_elim                       true
% 2.02/1.01  --brand_transform                       false
% 2.02/1.01  --non_eq_to_eq                          false
% 2.02/1.01  --prep_def_merge                        true
% 2.02/1.01  --prep_def_merge_prop_impl              false
% 2.02/1.01  --prep_def_merge_mbd                    true
% 2.02/1.01  --prep_def_merge_tr_red                 false
% 2.02/1.01  --prep_def_merge_tr_cl                  false
% 2.02/1.01  --smt_preprocessing                     true
% 2.02/1.01  --smt_ac_axioms                         fast
% 2.02/1.01  --preprocessed_out                      false
% 2.02/1.01  --preprocessed_stats                    false
% 2.02/1.01  
% 2.02/1.01  ------ Abstraction refinement Options
% 2.02/1.01  
% 2.02/1.01  --abstr_ref                             []
% 2.02/1.01  --abstr_ref_prep                        false
% 2.02/1.01  --abstr_ref_until_sat                   false
% 2.02/1.01  --abstr_ref_sig_restrict                funpre
% 2.02/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.02/1.01  --abstr_ref_under                       []
% 2.02/1.01  
% 2.02/1.01  ------ SAT Options
% 2.02/1.01  
% 2.02/1.01  --sat_mode                              false
% 2.02/1.01  --sat_fm_restart_options                ""
% 2.02/1.01  --sat_gr_def                            false
% 2.02/1.01  --sat_epr_types                         true
% 2.02/1.01  --sat_non_cyclic_types                  false
% 2.02/1.01  --sat_finite_models                     false
% 2.02/1.01  --sat_fm_lemmas                         false
% 2.02/1.01  --sat_fm_prep                           false
% 2.02/1.01  --sat_fm_uc_incr                        true
% 2.02/1.01  --sat_out_model                         small
% 2.02/1.01  --sat_out_clauses                       false
% 2.02/1.01  
% 2.02/1.01  ------ QBF Options
% 2.02/1.01  
% 2.02/1.01  --qbf_mode                              false
% 2.02/1.01  --qbf_elim_univ                         false
% 2.02/1.01  --qbf_dom_inst                          none
% 2.02/1.01  --qbf_dom_pre_inst                      false
% 2.02/1.01  --qbf_sk_in                             false
% 2.02/1.01  --qbf_pred_elim                         true
% 2.02/1.01  --qbf_split                             512
% 2.02/1.01  
% 2.02/1.01  ------ BMC1 Options
% 2.02/1.01  
% 2.02/1.01  --bmc1_incremental                      false
% 2.02/1.01  --bmc1_axioms                           reachable_all
% 2.02/1.01  --bmc1_min_bound                        0
% 2.02/1.01  --bmc1_max_bound                        -1
% 2.02/1.01  --bmc1_max_bound_default                -1
% 2.02/1.01  --bmc1_symbol_reachability              true
% 2.02/1.01  --bmc1_property_lemmas                  false
% 2.02/1.01  --bmc1_k_induction                      false
% 2.02/1.01  --bmc1_non_equiv_states                 false
% 2.02/1.01  --bmc1_deadlock                         false
% 2.02/1.01  --bmc1_ucm                              false
% 2.02/1.01  --bmc1_add_unsat_core                   none
% 2.02/1.01  --bmc1_unsat_core_children              false
% 2.02/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.02/1.01  --bmc1_out_stat                         full
% 2.02/1.01  --bmc1_ground_init                      false
% 2.02/1.01  --bmc1_pre_inst_next_state              false
% 2.02/1.01  --bmc1_pre_inst_state                   false
% 2.02/1.01  --bmc1_pre_inst_reach_state             false
% 2.02/1.01  --bmc1_out_unsat_core                   false
% 2.02/1.01  --bmc1_aig_witness_out                  false
% 2.02/1.01  --bmc1_verbose                          false
% 2.02/1.01  --bmc1_dump_clauses_tptp                false
% 2.02/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.02/1.01  --bmc1_dump_file                        -
% 2.02/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.02/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.02/1.01  --bmc1_ucm_extend_mode                  1
% 2.02/1.01  --bmc1_ucm_init_mode                    2
% 2.02/1.01  --bmc1_ucm_cone_mode                    none
% 2.02/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.02/1.01  --bmc1_ucm_relax_model                  4
% 2.02/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.02/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.02/1.01  --bmc1_ucm_layered_model                none
% 2.02/1.01  --bmc1_ucm_max_lemma_size               10
% 2.02/1.01  
% 2.02/1.01  ------ AIG Options
% 2.02/1.01  
% 2.02/1.01  --aig_mode                              false
% 2.02/1.01  
% 2.02/1.01  ------ Instantiation Options
% 2.02/1.01  
% 2.02/1.01  --instantiation_flag                    true
% 2.02/1.01  --inst_sos_flag                         false
% 2.02/1.01  --inst_sos_phase                        true
% 2.02/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.02/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.02/1.01  --inst_lit_sel_side                     none
% 2.02/1.01  --inst_solver_per_active                1400
% 2.02/1.01  --inst_solver_calls_frac                1.
% 2.02/1.01  --inst_passive_queue_type               priority_queues
% 2.02/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.02/1.01  --inst_passive_queues_freq              [25;2]
% 2.02/1.01  --inst_dismatching                      true
% 2.02/1.01  --inst_eager_unprocessed_to_passive     true
% 2.02/1.01  --inst_prop_sim_given                   true
% 2.02/1.01  --inst_prop_sim_new                     false
% 2.02/1.01  --inst_subs_new                         false
% 2.02/1.01  --inst_eq_res_simp                      false
% 2.02/1.01  --inst_subs_given                       false
% 2.02/1.01  --inst_orphan_elimination               true
% 2.02/1.01  --inst_learning_loop_flag               true
% 2.02/1.01  --inst_learning_start                   3000
% 2.02/1.01  --inst_learning_factor                  2
% 2.02/1.01  --inst_start_prop_sim_after_learn       3
% 2.02/1.01  --inst_sel_renew                        solver
% 2.02/1.01  --inst_lit_activity_flag                true
% 2.02/1.01  --inst_restr_to_given                   false
% 2.02/1.01  --inst_activity_threshold               500
% 2.02/1.01  --inst_out_proof                        true
% 2.02/1.01  
% 2.02/1.01  ------ Resolution Options
% 2.02/1.01  
% 2.02/1.01  --resolution_flag                       false
% 2.02/1.01  --res_lit_sel                           adaptive
% 2.02/1.01  --res_lit_sel_side                      none
% 2.02/1.01  --res_ordering                          kbo
% 2.02/1.01  --res_to_prop_solver                    active
% 2.02/1.01  --res_prop_simpl_new                    false
% 2.02/1.01  --res_prop_simpl_given                  true
% 2.02/1.01  --res_passive_queue_type                priority_queues
% 2.02/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.02/1.01  --res_passive_queues_freq               [15;5]
% 2.02/1.01  --res_forward_subs                      full
% 2.02/1.01  --res_backward_subs                     full
% 2.02/1.01  --res_forward_subs_resolution           true
% 2.02/1.01  --res_backward_subs_resolution          true
% 2.02/1.01  --res_orphan_elimination                true
% 2.02/1.01  --res_time_limit                        2.
% 2.02/1.01  --res_out_proof                         true
% 2.02/1.01  
% 2.02/1.01  ------ Superposition Options
% 2.02/1.01  
% 2.02/1.01  --superposition_flag                    false
% 2.02/1.01  --sup_passive_queue_type                priority_queues
% 2.02/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.02/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.02/1.01  --demod_completeness_check              fast
% 2.02/1.01  --demod_use_ground                      true
% 2.02/1.01  --sup_to_prop_solver                    passive
% 2.02/1.01  --sup_prop_simpl_new                    true
% 2.02/1.01  --sup_prop_simpl_given                  true
% 2.02/1.01  --sup_fun_splitting                     false
% 2.02/1.01  --sup_smt_interval                      50000
% 2.02/1.01  
% 2.02/1.01  ------ Superposition Simplification Setup
% 2.02/1.01  
% 2.02/1.01  --sup_indices_passive                   []
% 2.02/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.02/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.02/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.02/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.02/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.02/1.01  --sup_full_bw                           [BwDemod]
% 2.02/1.01  --sup_immed_triv                        [TrivRules]
% 2.02/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.02/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.02/1.01  --sup_immed_bw_main                     []
% 2.02/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.02/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.02/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.02/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.02/1.01  
% 2.02/1.01  ------ Combination Options
% 2.02/1.01  
% 2.02/1.01  --comb_res_mult                         3
% 2.02/1.01  --comb_sup_mult                         2
% 2.02/1.01  --comb_inst_mult                        10
% 2.02/1.01  
% 2.02/1.01  ------ Debug Options
% 2.02/1.01  
% 2.02/1.01  --dbg_backtrace                         false
% 2.02/1.01  --dbg_dump_prop_clauses                 false
% 2.02/1.01  --dbg_dump_prop_clauses_file            -
% 2.02/1.01  --dbg_out_stat                          false
% 2.02/1.01  
% 2.02/1.01  
% 2.02/1.01  
% 2.02/1.01  
% 2.02/1.01  ------ Proving...
% 2.02/1.01  
% 2.02/1.01  
% 2.02/1.01  % SZS status Theorem for theBenchmark.p
% 2.02/1.01  
% 2.02/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.02/1.01  
% 2.02/1.01  fof(f1,axiom,(
% 2.02/1.01    ! [X0] : (l3_lattices(X0) => ((v17_lattices(X0) & ~v2_struct_0(X0)) => (v16_lattices(X0) & v15_lattices(X0) & v11_lattices(X0) & ~v2_struct_0(X0))))),
% 2.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/1.01  
% 2.02/1.01  fof(f9,plain,(
% 2.02/1.01    ! [X0] : (((v16_lattices(X0) & v15_lattices(X0) & v11_lattices(X0) & ~v2_struct_0(X0)) | (~v17_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 2.02/1.01    inference(ennf_transformation,[],[f1])).
% 2.02/1.01  
% 2.02/1.01  fof(f10,plain,(
% 2.02/1.01    ! [X0] : ((v16_lattices(X0) & v15_lattices(X0) & v11_lattices(X0) & ~v2_struct_0(X0)) | ~v17_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 2.02/1.01    inference(flattening,[],[f9])).
% 2.02/1.01  
% 2.02/1.01  fof(f47,plain,(
% 2.02/1.01    ( ! [X0] : (v16_lattices(X0) | ~v17_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f10])).
% 2.02/1.01  
% 2.02/1.01  fof(f2,axiom,(
% 2.02/1.01    ! [X0] : (l3_lattices(X0) => ((v16_lattices(X0) & v15_lattices(X0) & v11_lattices(X0) & ~v2_struct_0(X0)) => (v17_lattices(X0) & ~v2_struct_0(X0))))),
% 2.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/1.01  
% 2.02/1.01  fof(f11,plain,(
% 2.02/1.01    ! [X0] : (((v17_lattices(X0) & ~v2_struct_0(X0)) | (~v16_lattices(X0) | ~v15_lattices(X0) | ~v11_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 2.02/1.01    inference(ennf_transformation,[],[f2])).
% 2.02/1.01  
% 2.02/1.01  fof(f12,plain,(
% 2.02/1.01    ! [X0] : ((v17_lattices(X0) & ~v2_struct_0(X0)) | ~v16_lattices(X0) | ~v15_lattices(X0) | ~v11_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 2.02/1.01    inference(flattening,[],[f11])).
% 2.02/1.01  
% 2.02/1.01  fof(f49,plain,(
% 2.02/1.01    ( ! [X0] : (v17_lattices(X0) | ~v16_lattices(X0) | ~v15_lattices(X0) | ~v11_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f12])).
% 2.02/1.01  
% 2.02/1.01  fof(f46,plain,(
% 2.02/1.01    ( ! [X0] : (v15_lattices(X0) | ~v17_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f10])).
% 2.02/1.01  
% 2.02/1.01  fof(f45,plain,(
% 2.02/1.01    ( ! [X0] : (v11_lattices(X0) | ~v17_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f10])).
% 2.02/1.01  
% 2.02/1.01  fof(f24,plain,(
% 2.02/1.01    ! [X1,X0] : (sP2(X1,X0) <=> (l3_lattices(X1) & v16_lattices(X1) & v15_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1) & l3_lattices(X0) & v16_lattices(X0) & v15_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 2.02/1.01    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 2.02/1.01  
% 2.02/1.01  fof(f36,plain,(
% 2.02/1.01    ! [X1,X0] : ((sP2(X1,X0) | (~l3_lattices(X1) | ~v16_lattices(X1) | ~v15_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v16_lattices(X0) | ~v15_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) & ((l3_lattices(X1) & v16_lattices(X1) & v15_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1) & l3_lattices(X0) & v16_lattices(X0) & v15_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) | ~sP2(X1,X0)))),
% 2.02/1.01    inference(nnf_transformation,[],[f24])).
% 2.02/1.01  
% 2.02/1.01  fof(f37,plain,(
% 2.02/1.01    ! [X1,X0] : ((sP2(X1,X0) | ~l3_lattices(X1) | ~v16_lattices(X1) | ~v15_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v16_lattices(X0) | ~v15_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & ((l3_lattices(X1) & v16_lattices(X1) & v15_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1) & l3_lattices(X0) & v16_lattices(X0) & v15_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) | ~sP2(X1,X0)))),
% 2.02/1.01    inference(flattening,[],[f36])).
% 2.02/1.01  
% 2.02/1.01  fof(f38,plain,(
% 2.02/1.01    ! [X0,X1] : ((sP2(X0,X1) | ~l3_lattices(X0) | ~v16_lattices(X0) | ~v15_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X1) | ~v16_lattices(X1) | ~v15_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) & ((l3_lattices(X0) & v16_lattices(X0) & v15_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0) & l3_lattices(X1) & v16_lattices(X1) & v15_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) | ~sP2(X0,X1)))),
% 2.02/1.01    inference(rectify,[],[f37])).
% 2.02/1.01  
% 2.02/1.01  fof(f82,plain,(
% 2.02/1.01    ( ! [X0,X1] : (sP2(X0,X1) | ~l3_lattices(X0) | ~v16_lattices(X0) | ~v15_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X1) | ~v16_lattices(X1) | ~v15_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f38])).
% 2.02/1.01  
% 2.02/1.01  fof(f21,plain,(
% 2.02/1.01    ! [X1,X0] : (sP0(X1,X0) <=> (l3_lattices(X1) & v11_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1) & l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 2.02/1.01    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.02/1.01  
% 2.02/1.01  fof(f30,plain,(
% 2.02/1.01    ! [X1,X0] : ((sP0(X1,X0) | (~l3_lattices(X1) | ~v11_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) & ((l3_lattices(X1) & v11_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1) & l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) | ~sP0(X1,X0)))),
% 2.02/1.01    inference(nnf_transformation,[],[f21])).
% 2.02/1.01  
% 2.02/1.01  fof(f31,plain,(
% 2.02/1.01    ! [X1,X0] : ((sP0(X1,X0) | ~l3_lattices(X1) | ~v11_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & ((l3_lattices(X1) & v11_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1) & l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) | ~sP0(X1,X0)))),
% 2.02/1.01    inference(flattening,[],[f30])).
% 2.02/1.01  
% 2.02/1.01  fof(f32,plain,(
% 2.02/1.01    ! [X0,X1] : ((sP0(X0,X1) | ~l3_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X1) | ~v11_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) & ((l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0) & l3_lattices(X1) & v11_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) | ~sP0(X0,X1)))),
% 2.02/1.01    inference(rectify,[],[f31])).
% 2.02/1.01  
% 2.02/1.01  fof(f64,plain,(
% 2.02/1.01    ( ! [X0,X1] : (sP0(X0,X1) | ~l3_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X1) | ~v11_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f32])).
% 2.02/1.01  
% 2.02/1.01  fof(f3,axiom,(
% 2.02/1.01    ! [X0,X1] : ((l3_lattices(X1) & ~v2_struct_0(X1) & l3_lattices(X0) & ~v2_struct_0(X0)) => (l3_lattices(k7_filter_1(X0,X1)) & v3_lattices(k7_filter_1(X0,X1))))),
% 2.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/1.01  
% 2.02/1.01  fof(f8,plain,(
% 2.02/1.01    ! [X0,X1] : ((l3_lattices(X1) & ~v2_struct_0(X1) & l3_lattices(X0) & ~v2_struct_0(X0)) => l3_lattices(k7_filter_1(X0,X1)))),
% 2.02/1.01    inference(pure_predicate_removal,[],[f3])).
% 2.02/1.01  
% 2.02/1.01  fof(f13,plain,(
% 2.02/1.01    ! [X0,X1] : (l3_lattices(k7_filter_1(X0,X1)) | (~l3_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | v2_struct_0(X0)))),
% 2.02/1.01    inference(ennf_transformation,[],[f8])).
% 2.02/1.01  
% 2.02/1.01  fof(f14,plain,(
% 2.02/1.01    ! [X0,X1] : (l3_lattices(k7_filter_1(X0,X1)) | ~l3_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.02/1.01    inference(flattening,[],[f13])).
% 2.02/1.01  
% 2.02/1.01  fof(f50,plain,(
% 2.02/1.01    ( ! [X0,X1] : (l3_lattices(k7_filter_1(X0,X1)) | ~l3_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f14])).
% 2.02/1.01  
% 2.02/1.01  fof(f74,plain,(
% 2.02/1.01    ( ! [X0,X1] : (v15_lattices(X1) | ~sP2(X0,X1)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f38])).
% 2.02/1.01  
% 2.02/1.01  fof(f75,plain,(
% 2.02/1.01    ( ! [X0,X1] : (v16_lattices(X1) | ~sP2(X0,X1)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f38])).
% 2.02/1.01  
% 2.02/1.01  fof(f79,plain,(
% 2.02/1.01    ( ! [X0,X1] : (v15_lattices(X0) | ~sP2(X0,X1)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f38])).
% 2.02/1.01  
% 2.02/1.01  fof(f80,plain,(
% 2.02/1.01    ( ! [X0,X1] : (v16_lattices(X0) | ~sP2(X0,X1)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f38])).
% 2.02/1.01  
% 2.02/1.01  fof(f25,plain,(
% 2.02/1.01    ! [X1,X0] : ((sP2(X1,X0) <=> (l3_lattices(k7_filter_1(X0,X1)) & v16_lattices(k7_filter_1(X0,X1)) & v15_lattices(k7_filter_1(X0,X1)) & v10_lattices(k7_filter_1(X0,X1)) & ~v2_struct_0(k7_filter_1(X0,X1)))) | ~sP3(X1,X0))),
% 2.02/1.01    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 2.02/1.01  
% 2.02/1.01  fof(f33,plain,(
% 2.02/1.01    ! [X1,X0] : (((sP2(X1,X0) | (~l3_lattices(k7_filter_1(X0,X1)) | ~v16_lattices(k7_filter_1(X0,X1)) | ~v15_lattices(k7_filter_1(X0,X1)) | ~v10_lattices(k7_filter_1(X0,X1)) | v2_struct_0(k7_filter_1(X0,X1)))) & ((l3_lattices(k7_filter_1(X0,X1)) & v16_lattices(k7_filter_1(X0,X1)) & v15_lattices(k7_filter_1(X0,X1)) & v10_lattices(k7_filter_1(X0,X1)) & ~v2_struct_0(k7_filter_1(X0,X1))) | ~sP2(X1,X0))) | ~sP3(X1,X0))),
% 2.02/1.01    inference(nnf_transformation,[],[f25])).
% 2.02/1.01  
% 2.02/1.01  fof(f34,plain,(
% 2.02/1.01    ! [X1,X0] : (((sP2(X1,X0) | ~l3_lattices(k7_filter_1(X0,X1)) | ~v16_lattices(k7_filter_1(X0,X1)) | ~v15_lattices(k7_filter_1(X0,X1)) | ~v10_lattices(k7_filter_1(X0,X1)) | v2_struct_0(k7_filter_1(X0,X1))) & ((l3_lattices(k7_filter_1(X0,X1)) & v16_lattices(k7_filter_1(X0,X1)) & v15_lattices(k7_filter_1(X0,X1)) & v10_lattices(k7_filter_1(X0,X1)) & ~v2_struct_0(k7_filter_1(X0,X1))) | ~sP2(X1,X0))) | ~sP3(X1,X0))),
% 2.02/1.01    inference(flattening,[],[f33])).
% 2.02/1.01  
% 2.02/1.01  fof(f35,plain,(
% 2.02/1.01    ! [X0,X1] : (((sP2(X0,X1) | ~l3_lattices(k7_filter_1(X1,X0)) | ~v16_lattices(k7_filter_1(X1,X0)) | ~v15_lattices(k7_filter_1(X1,X0)) | ~v10_lattices(k7_filter_1(X1,X0)) | v2_struct_0(k7_filter_1(X1,X0))) & ((l3_lattices(k7_filter_1(X1,X0)) & v16_lattices(k7_filter_1(X1,X0)) & v15_lattices(k7_filter_1(X1,X0)) & v10_lattices(k7_filter_1(X1,X0)) & ~v2_struct_0(k7_filter_1(X1,X0))) | ~sP2(X0,X1))) | ~sP3(X0,X1))),
% 2.02/1.01    inference(rectify,[],[f34])).
% 2.02/1.01  
% 2.02/1.01  fof(f69,plain,(
% 2.02/1.01    ( ! [X0,X1] : (v16_lattices(k7_filter_1(X1,X0)) | ~sP2(X0,X1) | ~sP3(X0,X1)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f35])).
% 2.02/1.01  
% 2.02/1.01  fof(f5,axiom,(
% 2.02/1.01    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => ((l3_lattices(X1) & v16_lattices(X1) & v15_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1) & l3_lattices(X0) & v16_lattices(X0) & v15_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) <=> (l3_lattices(k7_filter_1(X0,X1)) & v16_lattices(k7_filter_1(X0,X1)) & v15_lattices(k7_filter_1(X0,X1)) & v10_lattices(k7_filter_1(X0,X1)) & ~v2_struct_0(k7_filter_1(X0,X1))))))),
% 2.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/1.01  
% 2.02/1.01  fof(f17,plain,(
% 2.02/1.01    ! [X0] : (! [X1] : (((l3_lattices(X1) & v16_lattices(X1) & v15_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1) & l3_lattices(X0) & v16_lattices(X0) & v15_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) <=> (l3_lattices(k7_filter_1(X0,X1)) & v16_lattices(k7_filter_1(X0,X1)) & v15_lattices(k7_filter_1(X0,X1)) & v10_lattices(k7_filter_1(X0,X1)) & ~v2_struct_0(k7_filter_1(X0,X1)))) | (~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 2.02/1.01    inference(ennf_transformation,[],[f5])).
% 2.02/1.01  
% 2.02/1.01  fof(f18,plain,(
% 2.02/1.01    ! [X0] : (! [X1] : (((l3_lattices(X1) & v16_lattices(X1) & v15_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1) & l3_lattices(X0) & v16_lattices(X0) & v15_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) <=> (l3_lattices(k7_filter_1(X0,X1)) & v16_lattices(k7_filter_1(X0,X1)) & v15_lattices(k7_filter_1(X0,X1)) & v10_lattices(k7_filter_1(X0,X1)) & ~v2_struct_0(k7_filter_1(X0,X1)))) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 2.02/1.01    inference(flattening,[],[f17])).
% 2.02/1.01  
% 2.02/1.01  fof(f26,plain,(
% 2.02/1.01    ! [X0] : (! [X1] : (sP3(X1,X0) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 2.02/1.01    inference(definition_folding,[],[f18,f25,f24])).
% 2.02/1.01  
% 2.02/1.01  fof(f83,plain,(
% 2.02/1.01    ( ! [X0,X1] : (sP3(X1,X0) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f26])).
% 2.02/1.01  
% 2.02/1.01  fof(f72,plain,(
% 2.02/1.01    ( ! [X0,X1] : (~v2_struct_0(X1) | ~sP2(X0,X1)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f38])).
% 2.02/1.01  
% 2.02/1.01  fof(f73,plain,(
% 2.02/1.01    ( ! [X0,X1] : (v10_lattices(X1) | ~sP2(X0,X1)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f38])).
% 2.02/1.01  
% 2.02/1.01  fof(f76,plain,(
% 2.02/1.01    ( ! [X0,X1] : (l3_lattices(X1) | ~sP2(X0,X1)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f38])).
% 2.02/1.01  
% 2.02/1.01  fof(f77,plain,(
% 2.02/1.01    ( ! [X0,X1] : (~v2_struct_0(X0) | ~sP2(X0,X1)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f38])).
% 2.02/1.01  
% 2.02/1.01  fof(f78,plain,(
% 2.02/1.01    ( ! [X0,X1] : (v10_lattices(X0) | ~sP2(X0,X1)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f38])).
% 2.02/1.01  
% 2.02/1.01  fof(f81,plain,(
% 2.02/1.01    ( ! [X0,X1] : (l3_lattices(X0) | ~sP2(X0,X1)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f38])).
% 2.02/1.01  
% 2.02/1.01  fof(f68,plain,(
% 2.02/1.01    ( ! [X0,X1] : (v15_lattices(k7_filter_1(X1,X0)) | ~sP2(X0,X1) | ~sP3(X0,X1)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f35])).
% 2.02/1.01  
% 2.02/1.01  fof(f22,plain,(
% 2.02/1.01    ! [X1,X0] : ((sP0(X1,X0) <=> (l3_lattices(k7_filter_1(X0,X1)) & v11_lattices(k7_filter_1(X0,X1)) & v10_lattices(k7_filter_1(X0,X1)) & ~v2_struct_0(k7_filter_1(X0,X1)))) | ~sP1(X1,X0))),
% 2.02/1.01    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.02/1.01  
% 2.02/1.01  fof(f27,plain,(
% 2.02/1.01    ! [X1,X0] : (((sP0(X1,X0) | (~l3_lattices(k7_filter_1(X0,X1)) | ~v11_lattices(k7_filter_1(X0,X1)) | ~v10_lattices(k7_filter_1(X0,X1)) | v2_struct_0(k7_filter_1(X0,X1)))) & ((l3_lattices(k7_filter_1(X0,X1)) & v11_lattices(k7_filter_1(X0,X1)) & v10_lattices(k7_filter_1(X0,X1)) & ~v2_struct_0(k7_filter_1(X0,X1))) | ~sP0(X1,X0))) | ~sP1(X1,X0))),
% 2.02/1.01    inference(nnf_transformation,[],[f22])).
% 2.02/1.01  
% 2.02/1.01  fof(f28,plain,(
% 2.02/1.01    ! [X1,X0] : (((sP0(X1,X0) | ~l3_lattices(k7_filter_1(X0,X1)) | ~v11_lattices(k7_filter_1(X0,X1)) | ~v10_lattices(k7_filter_1(X0,X1)) | v2_struct_0(k7_filter_1(X0,X1))) & ((l3_lattices(k7_filter_1(X0,X1)) & v11_lattices(k7_filter_1(X0,X1)) & v10_lattices(k7_filter_1(X0,X1)) & ~v2_struct_0(k7_filter_1(X0,X1))) | ~sP0(X1,X0))) | ~sP1(X1,X0))),
% 2.02/1.01    inference(flattening,[],[f27])).
% 2.02/1.01  
% 2.02/1.01  fof(f29,plain,(
% 2.02/1.01    ! [X0,X1] : (((sP0(X0,X1) | ~l3_lattices(k7_filter_1(X1,X0)) | ~v11_lattices(k7_filter_1(X1,X0)) | ~v10_lattices(k7_filter_1(X1,X0)) | v2_struct_0(k7_filter_1(X1,X0))) & ((l3_lattices(k7_filter_1(X1,X0)) & v11_lattices(k7_filter_1(X1,X0)) & v10_lattices(k7_filter_1(X1,X0)) & ~v2_struct_0(k7_filter_1(X1,X0))) | ~sP0(X0,X1))) | ~sP1(X0,X1))),
% 2.02/1.01    inference(rectify,[],[f28])).
% 2.02/1.01  
% 2.02/1.01  fof(f53,plain,(
% 2.02/1.01    ( ! [X0,X1] : (v11_lattices(k7_filter_1(X1,X0)) | ~sP0(X0,X1) | ~sP1(X0,X1)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f29])).
% 2.02/1.01  
% 2.02/1.01  fof(f4,axiom,(
% 2.02/1.01    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => ((l3_lattices(X1) & v11_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1) & l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) <=> (l3_lattices(k7_filter_1(X0,X1)) & v11_lattices(k7_filter_1(X0,X1)) & v10_lattices(k7_filter_1(X0,X1)) & ~v2_struct_0(k7_filter_1(X0,X1))))))),
% 2.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/1.01  
% 2.02/1.01  fof(f15,plain,(
% 2.02/1.01    ! [X0] : (! [X1] : (((l3_lattices(X1) & v11_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1) & l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) <=> (l3_lattices(k7_filter_1(X0,X1)) & v11_lattices(k7_filter_1(X0,X1)) & v10_lattices(k7_filter_1(X0,X1)) & ~v2_struct_0(k7_filter_1(X0,X1)))) | (~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 2.02/1.01    inference(ennf_transformation,[],[f4])).
% 2.02/1.01  
% 2.02/1.01  fof(f16,plain,(
% 2.02/1.01    ! [X0] : (! [X1] : (((l3_lattices(X1) & v11_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1) & l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) <=> (l3_lattices(k7_filter_1(X0,X1)) & v11_lattices(k7_filter_1(X0,X1)) & v10_lattices(k7_filter_1(X0,X1)) & ~v2_struct_0(k7_filter_1(X0,X1)))) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 2.02/1.01    inference(flattening,[],[f15])).
% 2.02/1.01  
% 2.02/1.01  fof(f23,plain,(
% 2.02/1.01    ! [X0] : (! [X1] : (sP1(X1,X0) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 2.02/1.01    inference(definition_folding,[],[f16,f22,f21])).
% 2.02/1.01  
% 2.02/1.01  fof(f65,plain,(
% 2.02/1.01    ( ! [X0,X1] : (sP1(X1,X0) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f23])).
% 2.02/1.01  
% 2.02/1.01  fof(f56,plain,(
% 2.02/1.01    ( ! [X0,X1] : (~v2_struct_0(X1) | ~sP0(X0,X1)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f32])).
% 2.02/1.01  
% 2.02/1.01  fof(f57,plain,(
% 2.02/1.01    ( ! [X0,X1] : (v10_lattices(X1) | ~sP0(X0,X1)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f32])).
% 2.02/1.01  
% 2.02/1.01  fof(f59,plain,(
% 2.02/1.01    ( ! [X0,X1] : (l3_lattices(X1) | ~sP0(X0,X1)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f32])).
% 2.02/1.01  
% 2.02/1.01  fof(f60,plain,(
% 2.02/1.01    ( ! [X0,X1] : (~v2_struct_0(X0) | ~sP0(X0,X1)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f32])).
% 2.02/1.01  
% 2.02/1.01  fof(f61,plain,(
% 2.02/1.01    ( ! [X0,X1] : (v10_lattices(X0) | ~sP0(X0,X1)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f32])).
% 2.02/1.01  
% 2.02/1.01  fof(f63,plain,(
% 2.02/1.01    ( ! [X0,X1] : (l3_lattices(X0) | ~sP0(X0,X1)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f32])).
% 2.02/1.01  
% 2.02/1.01  fof(f52,plain,(
% 2.02/1.01    ( ! [X0,X1] : (v10_lattices(k7_filter_1(X1,X0)) | ~sP0(X0,X1) | ~sP1(X0,X1)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f29])).
% 2.02/1.01  
% 2.02/1.01  fof(f51,plain,(
% 2.02/1.01    ( ! [X0,X1] : (~v2_struct_0(k7_filter_1(X1,X0)) | ~sP0(X0,X1) | ~sP1(X0,X1)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f29])).
% 2.02/1.01  
% 2.02/1.01  fof(f58,plain,(
% 2.02/1.01    ( ! [X0,X1] : (v11_lattices(X1) | ~sP0(X0,X1)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f32])).
% 2.02/1.01  
% 2.02/1.01  fof(f62,plain,(
% 2.02/1.01    ( ! [X0,X1] : (v11_lattices(X0) | ~sP0(X0,X1)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f32])).
% 2.02/1.01  
% 2.02/1.01  fof(f71,plain,(
% 2.02/1.01    ( ! [X0,X1] : (sP2(X0,X1) | ~l3_lattices(k7_filter_1(X1,X0)) | ~v16_lattices(k7_filter_1(X1,X0)) | ~v15_lattices(k7_filter_1(X1,X0)) | ~v10_lattices(k7_filter_1(X1,X0)) | v2_struct_0(k7_filter_1(X1,X0)) | ~sP3(X0,X1)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f35])).
% 2.02/1.01  
% 2.02/1.01  fof(f55,plain,(
% 2.02/1.01    ( ! [X0,X1] : (sP0(X0,X1) | ~l3_lattices(k7_filter_1(X1,X0)) | ~v11_lattices(k7_filter_1(X1,X0)) | ~v10_lattices(k7_filter_1(X1,X0)) | v2_struct_0(k7_filter_1(X1,X0)) | ~sP1(X0,X1)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f29])).
% 2.02/1.01  
% 2.02/1.01  fof(f6,conjecture,(
% 2.02/1.01    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => ((l3_lattices(X1) & v17_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) <=> (l3_lattices(k7_filter_1(X0,X1)) & v17_lattices(k7_filter_1(X0,X1)) & v10_lattices(k7_filter_1(X0,X1)) & ~v2_struct_0(k7_filter_1(X0,X1))))))),
% 2.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/1.01  
% 2.02/1.01  fof(f7,negated_conjecture,(
% 2.02/1.01    ~! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => ((l3_lattices(X1) & v17_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) <=> (l3_lattices(k7_filter_1(X0,X1)) & v17_lattices(k7_filter_1(X0,X1)) & v10_lattices(k7_filter_1(X0,X1)) & ~v2_struct_0(k7_filter_1(X0,X1))))))),
% 2.02/1.01    inference(negated_conjecture,[],[f6])).
% 2.02/1.01  
% 2.02/1.01  fof(f19,plain,(
% 2.02/1.01    ? [X0] : (? [X1] : (((l3_lattices(X1) & v17_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) <~> (l3_lattices(k7_filter_1(X0,X1)) & v17_lattices(k7_filter_1(X0,X1)) & v10_lattices(k7_filter_1(X0,X1)) & ~v2_struct_0(k7_filter_1(X0,X1)))) & (l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1))) & (l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 2.02/1.01    inference(ennf_transformation,[],[f7])).
% 2.02/1.01  
% 2.02/1.01  fof(f20,plain,(
% 2.02/1.01    ? [X0] : (? [X1] : (((l3_lattices(X1) & v17_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) <~> (l3_lattices(k7_filter_1(X0,X1)) & v17_lattices(k7_filter_1(X0,X1)) & v10_lattices(k7_filter_1(X0,X1)) & ~v2_struct_0(k7_filter_1(X0,X1)))) & l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) & l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 2.02/1.01    inference(flattening,[],[f19])).
% 2.02/1.01  
% 2.02/1.01  fof(f39,plain,(
% 2.02/1.01    ? [X0] : (? [X1] : ((((~l3_lattices(k7_filter_1(X0,X1)) | ~v17_lattices(k7_filter_1(X0,X1)) | ~v10_lattices(k7_filter_1(X0,X1)) | v2_struct_0(k7_filter_1(X0,X1))) | (~l3_lattices(X1) | ~v17_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) & ((l3_lattices(k7_filter_1(X0,X1)) & v17_lattices(k7_filter_1(X0,X1)) & v10_lattices(k7_filter_1(X0,X1)) & ~v2_struct_0(k7_filter_1(X0,X1))) | (l3_lattices(X1) & v17_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))) & l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) & l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 2.02/1.01    inference(nnf_transformation,[],[f20])).
% 2.02/1.01  
% 2.02/1.01  fof(f40,plain,(
% 2.02/1.01    ? [X0] : (? [X1] : ((~l3_lattices(k7_filter_1(X0,X1)) | ~v17_lattices(k7_filter_1(X0,X1)) | ~v10_lattices(k7_filter_1(X0,X1)) | v2_struct_0(k7_filter_1(X0,X1)) | ~l3_lattices(X1) | ~v17_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & ((l3_lattices(k7_filter_1(X0,X1)) & v17_lattices(k7_filter_1(X0,X1)) & v10_lattices(k7_filter_1(X0,X1)) & ~v2_struct_0(k7_filter_1(X0,X1))) | (l3_lattices(X1) & v17_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))) & l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) & l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 2.02/1.01    inference(flattening,[],[f39])).
% 2.02/1.01  
% 2.02/1.01  fof(f42,plain,(
% 2.02/1.01    ( ! [X0] : (? [X1] : ((~l3_lattices(k7_filter_1(X0,X1)) | ~v17_lattices(k7_filter_1(X0,X1)) | ~v10_lattices(k7_filter_1(X0,X1)) | v2_struct_0(k7_filter_1(X0,X1)) | ~l3_lattices(X1) | ~v17_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & ((l3_lattices(k7_filter_1(X0,X1)) & v17_lattices(k7_filter_1(X0,X1)) & v10_lattices(k7_filter_1(X0,X1)) & ~v2_struct_0(k7_filter_1(X0,X1))) | (l3_lattices(X1) & v17_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))) & l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => ((~l3_lattices(k7_filter_1(X0,sK5)) | ~v17_lattices(k7_filter_1(X0,sK5)) | ~v10_lattices(k7_filter_1(X0,sK5)) | v2_struct_0(k7_filter_1(X0,sK5)) | ~l3_lattices(sK5) | ~v17_lattices(sK5) | ~v10_lattices(sK5) | v2_struct_0(sK5) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & ((l3_lattices(k7_filter_1(X0,sK5)) & v17_lattices(k7_filter_1(X0,sK5)) & v10_lattices(k7_filter_1(X0,sK5)) & ~v2_struct_0(k7_filter_1(X0,sK5))) | (l3_lattices(sK5) & v17_lattices(sK5) & v10_lattices(sK5) & ~v2_struct_0(sK5) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))) & l3_lattices(sK5) & v10_lattices(sK5) & ~v2_struct_0(sK5))) )),
% 2.02/1.01    introduced(choice_axiom,[])).
% 2.02/1.01  
% 2.02/1.01  fof(f41,plain,(
% 2.02/1.01    ? [X0] : (? [X1] : ((~l3_lattices(k7_filter_1(X0,X1)) | ~v17_lattices(k7_filter_1(X0,X1)) | ~v10_lattices(k7_filter_1(X0,X1)) | v2_struct_0(k7_filter_1(X0,X1)) | ~l3_lattices(X1) | ~v17_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & ((l3_lattices(k7_filter_1(X0,X1)) & v17_lattices(k7_filter_1(X0,X1)) & v10_lattices(k7_filter_1(X0,X1)) & ~v2_struct_0(k7_filter_1(X0,X1))) | (l3_lattices(X1) & v17_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))) & l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) & l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~l3_lattices(k7_filter_1(sK4,X1)) | ~v17_lattices(k7_filter_1(sK4,X1)) | ~v10_lattices(k7_filter_1(sK4,X1)) | v2_struct_0(k7_filter_1(sK4,X1)) | ~l3_lattices(X1) | ~v17_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(sK4) | ~v17_lattices(sK4) | ~v10_lattices(sK4) | v2_struct_0(sK4)) & ((l3_lattices(k7_filter_1(sK4,X1)) & v17_lattices(k7_filter_1(sK4,X1)) & v10_lattices(k7_filter_1(sK4,X1)) & ~v2_struct_0(k7_filter_1(sK4,X1))) | (l3_lattices(X1) & v17_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1) & l3_lattices(sK4) & v17_lattices(sK4) & v10_lattices(sK4) & ~v2_struct_0(sK4))) & l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) & l3_lattices(sK4) & v10_lattices(sK4) & ~v2_struct_0(sK4))),
% 2.02/1.01    introduced(choice_axiom,[])).
% 2.02/1.01  
% 2.02/1.01  fof(f43,plain,(
% 2.02/1.01    ((~l3_lattices(k7_filter_1(sK4,sK5)) | ~v17_lattices(k7_filter_1(sK4,sK5)) | ~v10_lattices(k7_filter_1(sK4,sK5)) | v2_struct_0(k7_filter_1(sK4,sK5)) | ~l3_lattices(sK5) | ~v17_lattices(sK5) | ~v10_lattices(sK5) | v2_struct_0(sK5) | ~l3_lattices(sK4) | ~v17_lattices(sK4) | ~v10_lattices(sK4) | v2_struct_0(sK4)) & ((l3_lattices(k7_filter_1(sK4,sK5)) & v17_lattices(k7_filter_1(sK4,sK5)) & v10_lattices(k7_filter_1(sK4,sK5)) & ~v2_struct_0(k7_filter_1(sK4,sK5))) | (l3_lattices(sK5) & v17_lattices(sK5) & v10_lattices(sK5) & ~v2_struct_0(sK5) & l3_lattices(sK4) & v17_lattices(sK4) & v10_lattices(sK4) & ~v2_struct_0(sK4))) & l3_lattices(sK5) & v10_lattices(sK5) & ~v2_struct_0(sK5)) & l3_lattices(sK4) & v10_lattices(sK4) & ~v2_struct_0(sK4)),
% 2.02/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f40,f42,f41])).
% 2.02/1.01  
% 2.02/1.01  fof(f122,plain,(
% 2.02/1.01    ~l3_lattices(k7_filter_1(sK4,sK5)) | ~v17_lattices(k7_filter_1(sK4,sK5)) | ~v10_lattices(k7_filter_1(sK4,sK5)) | v2_struct_0(k7_filter_1(sK4,sK5)) | ~l3_lattices(sK5) | ~v17_lattices(sK5) | ~v10_lattices(sK5) | v2_struct_0(sK5) | ~l3_lattices(sK4) | ~v17_lattices(sK4) | ~v10_lattices(sK4) | v2_struct_0(sK4)),
% 2.02/1.01    inference(cnf_transformation,[],[f43])).
% 2.02/1.01  
% 2.02/1.01  fof(f84,plain,(
% 2.02/1.01    ~v2_struct_0(sK4)),
% 2.02/1.01    inference(cnf_transformation,[],[f43])).
% 2.02/1.01  
% 2.02/1.01  fof(f85,plain,(
% 2.02/1.01    v10_lattices(sK4)),
% 2.02/1.01    inference(cnf_transformation,[],[f43])).
% 2.02/1.01  
% 2.02/1.01  fof(f86,plain,(
% 2.02/1.01    l3_lattices(sK4)),
% 2.02/1.01    inference(cnf_transformation,[],[f43])).
% 2.02/1.01  
% 2.02/1.01  fof(f87,plain,(
% 2.02/1.01    ~v2_struct_0(sK5)),
% 2.02/1.01    inference(cnf_transformation,[],[f43])).
% 2.02/1.01  
% 2.02/1.01  fof(f88,plain,(
% 2.02/1.01    v10_lattices(sK5)),
% 2.02/1.01    inference(cnf_transformation,[],[f43])).
% 2.02/1.01  
% 2.02/1.01  fof(f89,plain,(
% 2.02/1.01    l3_lattices(sK5)),
% 2.02/1.01    inference(cnf_transformation,[],[f43])).
% 2.02/1.01  
% 2.02/1.01  fof(f112,plain,(
% 2.02/1.01    v17_lattices(k7_filter_1(sK4,sK5)) | v17_lattices(sK5)),
% 2.02/1.01    inference(cnf_transformation,[],[f43])).
% 2.02/1.01  
% 2.02/1.01  fof(f108,plain,(
% 2.02/1.01    v17_lattices(k7_filter_1(sK4,sK5)) | v17_lattices(sK4)),
% 2.02/1.01    inference(cnf_transformation,[],[f43])).
% 2.02/1.01  
% 2.02/1.01  fof(f104,plain,(
% 2.02/1.01    v10_lattices(k7_filter_1(sK4,sK5)) | v17_lattices(sK5)),
% 2.02/1.01    inference(cnf_transformation,[],[f43])).
% 2.02/1.01  
% 2.02/1.01  fof(f100,plain,(
% 2.02/1.01    v10_lattices(k7_filter_1(sK4,sK5)) | v17_lattices(sK4)),
% 2.02/1.01    inference(cnf_transformation,[],[f43])).
% 2.02/1.01  
% 2.02/1.01  fof(f96,plain,(
% 2.02/1.01    ~v2_struct_0(k7_filter_1(sK4,sK5)) | v17_lattices(sK5)),
% 2.02/1.01    inference(cnf_transformation,[],[f43])).
% 2.02/1.01  
% 2.02/1.01  fof(f92,plain,(
% 2.02/1.01    ~v2_struct_0(k7_filter_1(sK4,sK5)) | v17_lattices(sK4)),
% 2.02/1.01    inference(cnf_transformation,[],[f43])).
% 2.02/1.01  
% 2.02/1.01  cnf(c_0,plain,
% 2.02/1.01      ( ~ l3_lattices(X0)
% 2.02/1.01      | v2_struct_0(X0)
% 2.02/1.01      | ~ v17_lattices(X0)
% 2.02/1.01      | v16_lattices(X0) ),
% 2.02/1.01      inference(cnf_transformation,[],[f47]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2918,plain,
% 2.02/1.01      ( ~ l3_lattices(sK5)
% 2.02/1.01      | v2_struct_0(sK5)
% 2.02/1.01      | ~ v17_lattices(sK5)
% 2.02/1.01      | v16_lattices(sK5) ),
% 2.02/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2919,plain,
% 2.02/1.01      ( l3_lattices(sK5) != iProver_top
% 2.02/1.01      | v2_struct_0(sK5) = iProver_top
% 2.02/1.01      | v17_lattices(sK5) != iProver_top
% 2.02/1.01      | v16_lattices(sK5) = iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_2918]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_4,plain,
% 2.02/1.01      ( ~ v11_lattices(X0)
% 2.02/1.01      | ~ v15_lattices(X0)
% 2.02/1.01      | ~ l3_lattices(X0)
% 2.02/1.01      | v2_struct_0(X0)
% 2.02/1.01      | v17_lattices(X0)
% 2.02/1.01      | ~ v16_lattices(X0) ),
% 2.02/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2894,plain,
% 2.02/1.01      ( ~ v11_lattices(sK5)
% 2.02/1.01      | ~ v15_lattices(sK5)
% 2.02/1.01      | ~ l3_lattices(sK5)
% 2.02/1.01      | v2_struct_0(sK5)
% 2.02/1.01      | v17_lattices(sK5)
% 2.02/1.01      | ~ v16_lattices(sK5) ),
% 2.02/1.01      inference(instantiation,[status(thm)],[c_4]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2895,plain,
% 2.02/1.01      ( v11_lattices(sK5) != iProver_top
% 2.02/1.01      | v15_lattices(sK5) != iProver_top
% 2.02/1.01      | l3_lattices(sK5) != iProver_top
% 2.02/1.01      | v2_struct_0(sK5) = iProver_top
% 2.02/1.01      | v17_lattices(sK5) = iProver_top
% 2.02/1.01      | v16_lattices(sK5) != iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_2894]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_1,plain,
% 2.02/1.01      ( v15_lattices(X0)
% 2.02/1.01      | ~ l3_lattices(X0)
% 2.02/1.01      | v2_struct_0(X0)
% 2.02/1.01      | ~ v17_lattices(X0) ),
% 2.02/1.01      inference(cnf_transformation,[],[f46]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2828,plain,
% 2.02/1.01      ( v15_lattices(sK5)
% 2.02/1.01      | ~ l3_lattices(sK5)
% 2.02/1.01      | v2_struct_0(sK5)
% 2.02/1.01      | ~ v17_lattices(sK5) ),
% 2.02/1.01      inference(instantiation,[status(thm)],[c_1]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2829,plain,
% 2.02/1.01      ( v15_lattices(sK5) = iProver_top
% 2.02/1.01      | l3_lattices(sK5) != iProver_top
% 2.02/1.01      | v2_struct_0(sK5) = iProver_top
% 2.02/1.01      | v17_lattices(sK5) != iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_2828]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2,plain,
% 2.02/1.01      ( v11_lattices(X0)
% 2.02/1.01      | ~ l3_lattices(X0)
% 2.02/1.01      | v2_struct_0(X0)
% 2.02/1.01      | ~ v17_lattices(X0) ),
% 2.02/1.01      inference(cnf_transformation,[],[f45]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2817,plain,
% 2.02/1.01      ( v11_lattices(sK5)
% 2.02/1.01      | ~ l3_lattices(sK5)
% 2.02/1.01      | v2_struct_0(sK5)
% 2.02/1.01      | ~ v17_lattices(sK5) ),
% 2.02/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2818,plain,
% 2.02/1.01      ( v11_lattices(sK5) = iProver_top
% 2.02/1.01      | l3_lattices(sK5) != iProver_top
% 2.02/1.01      | v2_struct_0(sK5) = iProver_top
% 2.02/1.01      | v17_lattices(sK5) != iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_2817]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_28,plain,
% 2.02/1.01      ( sP2(X0,X1)
% 2.02/1.01      | ~ v10_lattices(X0)
% 2.02/1.01      | ~ v10_lattices(X1)
% 2.02/1.01      | ~ v15_lattices(X0)
% 2.02/1.01      | ~ v15_lattices(X1)
% 2.02/1.01      | ~ l3_lattices(X0)
% 2.02/1.01      | ~ l3_lattices(X1)
% 2.02/1.01      | v2_struct_0(X0)
% 2.02/1.01      | v2_struct_0(X1)
% 2.02/1.01      | ~ v16_lattices(X0)
% 2.02/1.01      | ~ v16_lattices(X1) ),
% 2.02/1.01      inference(cnf_transformation,[],[f82]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2745,plain,
% 2.02/1.01      ( sP2(sK5,sK4)
% 2.02/1.01      | ~ v10_lattices(sK5)
% 2.02/1.01      | ~ v10_lattices(sK4)
% 2.02/1.01      | ~ v15_lattices(sK5)
% 2.02/1.01      | ~ v15_lattices(sK4)
% 2.02/1.01      | ~ l3_lattices(sK5)
% 2.02/1.01      | ~ l3_lattices(sK4)
% 2.02/1.01      | v2_struct_0(sK5)
% 2.02/1.01      | v2_struct_0(sK4)
% 2.02/1.01      | ~ v16_lattices(sK5)
% 2.02/1.01      | ~ v16_lattices(sK4) ),
% 2.02/1.01      inference(instantiation,[status(thm)],[c_28]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2746,plain,
% 2.02/1.01      ( sP2(sK5,sK4) = iProver_top
% 2.02/1.01      | v10_lattices(sK5) != iProver_top
% 2.02/1.01      | v10_lattices(sK4) != iProver_top
% 2.02/1.01      | v15_lattices(sK5) != iProver_top
% 2.02/1.01      | v15_lattices(sK4) != iProver_top
% 2.02/1.01      | l3_lattices(sK5) != iProver_top
% 2.02/1.01      | l3_lattices(sK4) != iProver_top
% 2.02/1.01      | v2_struct_0(sK5) = iProver_top
% 2.02/1.01      | v2_struct_0(sK4) = iProver_top
% 2.02/1.01      | v16_lattices(sK5) != iProver_top
% 2.02/1.01      | v16_lattices(sK4) != iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_2745]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_12,plain,
% 2.02/1.01      ( sP0(X0,X1)
% 2.02/1.01      | ~ v10_lattices(X0)
% 2.02/1.01      | ~ v10_lattices(X1)
% 2.02/1.01      | ~ v11_lattices(X0)
% 2.02/1.01      | ~ v11_lattices(X1)
% 2.02/1.01      | ~ l3_lattices(X0)
% 2.02/1.01      | ~ l3_lattices(X1)
% 2.02/1.01      | v2_struct_0(X0)
% 2.02/1.01      | v2_struct_0(X1) ),
% 2.02/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2726,plain,
% 2.02/1.01      ( sP0(sK5,sK4)
% 2.02/1.01      | ~ v10_lattices(sK5)
% 2.02/1.01      | ~ v10_lattices(sK4)
% 2.02/1.01      | ~ v11_lattices(sK5)
% 2.02/1.01      | ~ v11_lattices(sK4)
% 2.02/1.01      | ~ l3_lattices(sK5)
% 2.02/1.01      | ~ l3_lattices(sK4)
% 2.02/1.01      | v2_struct_0(sK5)
% 2.02/1.01      | v2_struct_0(sK4) ),
% 2.02/1.01      inference(instantiation,[status(thm)],[c_12]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2728,plain,
% 2.02/1.01      ( sP0(sK5,sK4) = iProver_top
% 2.02/1.01      | v10_lattices(sK5) != iProver_top
% 2.02/1.01      | v10_lattices(sK4) != iProver_top
% 2.02/1.01      | v11_lattices(sK5) != iProver_top
% 2.02/1.01      | v11_lattices(sK4) != iProver_top
% 2.02/1.01      | l3_lattices(sK5) != iProver_top
% 2.02/1.01      | l3_lattices(sK4) != iProver_top
% 2.02/1.01      | v2_struct_0(sK5) = iProver_top
% 2.02/1.01      | v2_struct_0(sK4) = iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_2726]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_6,plain,
% 2.02/1.01      ( ~ l3_lattices(X0)
% 2.02/1.01      | ~ l3_lattices(X1)
% 2.02/1.01      | l3_lattices(k7_filter_1(X0,X1))
% 2.02/1.01      | v2_struct_0(X0)
% 2.02/1.01      | v2_struct_0(X1) ),
% 2.02/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2691,plain,
% 2.02/1.01      ( l3_lattices(k7_filter_1(sK4,sK5))
% 2.02/1.01      | ~ l3_lattices(sK5)
% 2.02/1.01      | ~ l3_lattices(sK4)
% 2.02/1.01      | v2_struct_0(sK5)
% 2.02/1.01      | v2_struct_0(sK4) ),
% 2.02/1.01      inference(instantiation,[status(thm)],[c_6]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2692,plain,
% 2.02/1.01      ( l3_lattices(k7_filter_1(sK4,sK5)) = iProver_top
% 2.02/1.01      | l3_lattices(sK5) != iProver_top
% 2.02/1.01      | l3_lattices(sK4) != iProver_top
% 2.02/1.01      | v2_struct_0(sK5) = iProver_top
% 2.02/1.01      | v2_struct_0(sK4) = iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_2691]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_36,plain,
% 2.02/1.01      ( ~ sP2(X0,X1) | v15_lattices(X1) ),
% 2.02/1.01      inference(cnf_transformation,[],[f74]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2647,plain,
% 2.02/1.01      ( ~ sP2(sK5,sK4) | v15_lattices(sK4) ),
% 2.02/1.01      inference(instantiation,[status(thm)],[c_36]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2669,plain,
% 2.02/1.01      ( sP2(sK5,sK4) != iProver_top | v15_lattices(sK4) = iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_2647]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_35,plain,
% 2.02/1.01      ( ~ sP2(X0,X1) | v16_lattices(X1) ),
% 2.02/1.01      inference(cnf_transformation,[],[f75]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2648,plain,
% 2.02/1.01      ( ~ sP2(sK5,sK4) | v16_lattices(sK4) ),
% 2.02/1.01      inference(instantiation,[status(thm)],[c_35]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2667,plain,
% 2.02/1.01      ( sP2(sK5,sK4) != iProver_top | v16_lattices(sK4) = iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_2648]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_31,plain,
% 2.02/1.01      ( ~ sP2(X0,X1) | v15_lattices(X0) ),
% 2.02/1.01      inference(cnf_transformation,[],[f79]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2649,plain,
% 2.02/1.01      ( ~ sP2(sK5,sK4) | v15_lattices(sK5) ),
% 2.02/1.01      inference(instantiation,[status(thm)],[c_31]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2665,plain,
% 2.02/1.01      ( sP2(sK5,sK4) != iProver_top | v15_lattices(sK5) = iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_2649]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_30,plain,
% 2.02/1.01      ( ~ sP2(X0,X1) | v16_lattices(X0) ),
% 2.02/1.01      inference(cnf_transformation,[],[f80]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2650,plain,
% 2.02/1.01      ( ~ sP2(sK5,sK4) | v16_lattices(sK5) ),
% 2.02/1.01      inference(instantiation,[status(thm)],[c_30]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2663,plain,
% 2.02/1.01      ( sP2(sK5,sK4) != iProver_top | v16_lattices(sK5) = iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_2650]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_24,plain,
% 2.02/1.01      ( ~ sP3(X0,X1) | ~ sP2(X0,X1) | v16_lattices(k7_filter_1(X1,X0)) ),
% 2.02/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_39,plain,
% 2.02/1.01      ( sP3(X0,X1)
% 2.02/1.01      | ~ v10_lattices(X1)
% 2.02/1.01      | ~ v10_lattices(X0)
% 2.02/1.01      | ~ l3_lattices(X1)
% 2.02/1.01      | ~ l3_lattices(X0)
% 2.02/1.01      | v2_struct_0(X1)
% 2.02/1.01      | v2_struct_0(X0) ),
% 2.02/1.01      inference(cnf_transformation,[],[f83]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_38,plain,
% 2.02/1.01      ( ~ sP2(X0,X1) | ~ v2_struct_0(X1) ),
% 2.02/1.01      inference(cnf_transformation,[],[f72]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_37,plain,
% 2.02/1.01      ( ~ sP2(X0,X1) | v10_lattices(X1) ),
% 2.02/1.01      inference(cnf_transformation,[],[f73]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_34,plain,
% 2.02/1.01      ( ~ sP2(X0,X1) | l3_lattices(X1) ),
% 2.02/1.01      inference(cnf_transformation,[],[f76]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_33,plain,
% 2.02/1.01      ( ~ sP2(X0,X1) | ~ v2_struct_0(X0) ),
% 2.02/1.01      inference(cnf_transformation,[],[f77]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_32,plain,
% 2.02/1.01      ( ~ sP2(X0,X1) | v10_lattices(X0) ),
% 2.02/1.01      inference(cnf_transformation,[],[f78]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_29,plain,
% 2.02/1.01      ( ~ sP2(X0,X1) | l3_lattices(X0) ),
% 2.02/1.01      inference(cnf_transformation,[],[f81]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_535,plain,
% 2.02/1.01      ( ~ sP2(X0,X1) | v16_lattices(k7_filter_1(X1,X0)) ),
% 2.02/1.01      inference(global_propositional_subsumption,
% 2.02/1.01                [status(thm)],
% 2.02/1.01                [c_24,c_39,c_38,c_37,c_34,c_33,c_32,c_29]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2651,plain,
% 2.02/1.01      ( ~ sP2(sK5,sK4) | v16_lattices(k7_filter_1(sK4,sK5)) ),
% 2.02/1.01      inference(instantiation,[status(thm)],[c_535]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2661,plain,
% 2.02/1.01      ( sP2(sK5,sK4) != iProver_top
% 2.02/1.01      | v16_lattices(k7_filter_1(sK4,sK5)) = iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_2651]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_25,plain,
% 2.02/1.01      ( ~ sP3(X0,X1) | ~ sP2(X0,X1) | v15_lattices(k7_filter_1(X1,X0)) ),
% 2.02/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_528,plain,
% 2.02/1.01      ( ~ sP2(X0,X1) | v15_lattices(k7_filter_1(X1,X0)) ),
% 2.02/1.01      inference(global_propositional_subsumption,
% 2.02/1.01                [status(thm)],
% 2.02/1.01                [c_25,c_39,c_38,c_37,c_34,c_33,c_32,c_29]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2652,plain,
% 2.02/1.01      ( ~ sP2(sK5,sK4) | v15_lattices(k7_filter_1(sK4,sK5)) ),
% 2.02/1.01      inference(instantiation,[status(thm)],[c_528]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2659,plain,
% 2.02/1.01      ( sP2(sK5,sK4) != iProver_top
% 2.02/1.01      | v15_lattices(k7_filter_1(sK4,sK5)) = iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_2652]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_9,plain,
% 2.02/1.01      ( ~ sP1(X0,X1) | ~ sP0(X0,X1) | v11_lattices(k7_filter_1(X1,X0)) ),
% 2.02/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_21,plain,
% 2.02/1.01      ( sP1(X0,X1)
% 2.02/1.01      | ~ v10_lattices(X1)
% 2.02/1.01      | ~ v10_lattices(X0)
% 2.02/1.01      | ~ l3_lattices(X1)
% 2.02/1.01      | ~ l3_lattices(X0)
% 2.02/1.01      | v2_struct_0(X1)
% 2.02/1.01      | v2_struct_0(X0) ),
% 2.02/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_20,plain,
% 2.02/1.01      ( ~ sP0(X0,X1) | ~ v2_struct_0(X1) ),
% 2.02/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_19,plain,
% 2.02/1.01      ( ~ sP0(X0,X1) | v10_lattices(X1) ),
% 2.02/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_17,plain,
% 2.02/1.01      ( ~ sP0(X0,X1) | l3_lattices(X1) ),
% 2.02/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_16,plain,
% 2.02/1.01      ( ~ sP0(X0,X1) | ~ v2_struct_0(X0) ),
% 2.02/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_15,plain,
% 2.02/1.01      ( ~ sP0(X0,X1) | v10_lattices(X0) ),
% 2.02/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_13,plain,
% 2.02/1.01      ( ~ sP0(X0,X1) | l3_lattices(X0) ),
% 2.02/1.01      inference(cnf_transformation,[],[f63]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_574,plain,
% 2.02/1.01      ( ~ sP0(X0,X1) | v11_lattices(k7_filter_1(X1,X0)) ),
% 2.02/1.01      inference(global_propositional_subsumption,
% 2.02/1.01                [status(thm)],
% 2.02/1.01                [c_9,c_21,c_20,c_19,c_17,c_16,c_15,c_13]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2632,plain,
% 2.02/1.01      ( ~ sP0(sK5,sK4) | v11_lattices(k7_filter_1(sK4,sK5)) ),
% 2.02/1.01      inference(instantiation,[status(thm)],[c_574]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2645,plain,
% 2.02/1.01      ( sP0(sK5,sK4) != iProver_top
% 2.02/1.01      | v11_lattices(k7_filter_1(sK4,sK5)) = iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_2632]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_10,plain,
% 2.02/1.01      ( ~ sP1(X0,X1) | ~ sP0(X0,X1) | v10_lattices(k7_filter_1(X1,X0)) ),
% 2.02/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_567,plain,
% 2.02/1.01      ( ~ sP0(X0,X1) | v10_lattices(k7_filter_1(X1,X0)) ),
% 2.02/1.01      inference(global_propositional_subsumption,
% 2.02/1.01                [status(thm)],
% 2.02/1.01                [c_10,c_21,c_20,c_19,c_17,c_16,c_15,c_13]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2633,plain,
% 2.02/1.01      ( ~ sP0(sK5,sK4) | v10_lattices(k7_filter_1(sK4,sK5)) ),
% 2.02/1.01      inference(instantiation,[status(thm)],[c_567]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2643,plain,
% 2.02/1.01      ( sP0(sK5,sK4) != iProver_top
% 2.02/1.01      | v10_lattices(k7_filter_1(sK4,sK5)) = iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_2633]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_11,plain,
% 2.02/1.01      ( ~ sP1(X0,X1) | ~ sP0(X0,X1) | ~ v2_struct_0(k7_filter_1(X1,X0)) ),
% 2.02/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_560,plain,
% 2.02/1.01      ( ~ sP0(X0,X1) | ~ v2_struct_0(k7_filter_1(X1,X0)) ),
% 2.02/1.01      inference(global_propositional_subsumption,
% 2.02/1.01                [status(thm)],
% 2.02/1.01                [c_11,c_21,c_20,c_19,c_17,c_16,c_15,c_13]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2634,plain,
% 2.02/1.01      ( ~ sP0(sK5,sK4) | ~ v2_struct_0(k7_filter_1(sK4,sK5)) ),
% 2.02/1.01      inference(instantiation,[status(thm)],[c_560]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2641,plain,
% 2.02/1.01      ( sP0(sK5,sK4) != iProver_top
% 2.02/1.01      | v2_struct_0(k7_filter_1(sK4,sK5)) != iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_2634]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_18,plain,
% 2.02/1.01      ( ~ sP0(X0,X1) | v11_lattices(X1) ),
% 2.02/1.01      inference(cnf_transformation,[],[f58]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2635,plain,
% 2.02/1.01      ( ~ sP0(sK5,sK4) | v11_lattices(sK4) ),
% 2.02/1.01      inference(instantiation,[status(thm)],[c_18]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2639,plain,
% 2.02/1.01      ( sP0(sK5,sK4) != iProver_top | v11_lattices(sK4) = iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_2635]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_14,plain,
% 2.02/1.01      ( ~ sP0(X0,X1) | v11_lattices(X0) ),
% 2.02/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2636,plain,
% 2.02/1.01      ( ~ sP0(sK5,sK4) | v11_lattices(sK5) ),
% 2.02/1.01      inference(instantiation,[status(thm)],[c_14]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2637,plain,
% 2.02/1.01      ( sP0(sK5,sK4) != iProver_top | v11_lattices(sK5) = iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_2636]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2625,plain,
% 2.02/1.01      ( ~ v11_lattices(k7_filter_1(sK4,sK5))
% 2.02/1.01      | ~ v15_lattices(k7_filter_1(sK4,sK5))
% 2.02/1.01      | ~ l3_lattices(k7_filter_1(sK4,sK5))
% 2.02/1.01      | v2_struct_0(k7_filter_1(sK4,sK5))
% 2.02/1.01      | v17_lattices(k7_filter_1(sK4,sK5))
% 2.02/1.01      | ~ v16_lattices(k7_filter_1(sK4,sK5)) ),
% 2.02/1.01      inference(instantiation,[status(thm)],[c_4]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2626,plain,
% 2.02/1.01      ( v11_lattices(k7_filter_1(sK4,sK5)) != iProver_top
% 2.02/1.01      | v15_lattices(k7_filter_1(sK4,sK5)) != iProver_top
% 2.02/1.01      | l3_lattices(k7_filter_1(sK4,sK5)) != iProver_top
% 2.02/1.01      | v2_struct_0(k7_filter_1(sK4,sK5)) = iProver_top
% 2.02/1.01      | v17_lattices(k7_filter_1(sK4,sK5)) = iProver_top
% 2.02/1.01      | v16_lattices(k7_filter_1(sK4,sK5)) != iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_2625]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_22,plain,
% 2.02/1.01      ( ~ sP3(X0,X1)
% 2.02/1.01      | sP2(X0,X1)
% 2.02/1.01      | ~ v10_lattices(k7_filter_1(X1,X0))
% 2.02/1.01      | ~ v15_lattices(k7_filter_1(X1,X0))
% 2.02/1.01      | ~ l3_lattices(k7_filter_1(X1,X0))
% 2.02/1.01      | v2_struct_0(k7_filter_1(X1,X0))
% 2.02/1.01      | ~ v16_lattices(k7_filter_1(X1,X0)) ),
% 2.02/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_891,plain,
% 2.02/1.01      ( sP2(X0,X1)
% 2.02/1.01      | ~ v10_lattices(X0)
% 2.02/1.01      | ~ v10_lattices(X1)
% 2.02/1.01      | ~ v10_lattices(k7_filter_1(X1,X0))
% 2.02/1.01      | ~ v15_lattices(k7_filter_1(X1,X0))
% 2.02/1.01      | ~ l3_lattices(X0)
% 2.02/1.01      | ~ l3_lattices(X1)
% 2.02/1.01      | ~ l3_lattices(k7_filter_1(X1,X0))
% 2.02/1.01      | v2_struct_0(X0)
% 2.02/1.01      | v2_struct_0(X1)
% 2.02/1.01      | v2_struct_0(k7_filter_1(X1,X0))
% 2.02/1.01      | ~ v16_lattices(k7_filter_1(X1,X0)) ),
% 2.02/1.01      inference(resolution,[status(thm)],[c_39,c_22]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_919,plain,
% 2.02/1.01      ( sP2(X0,X1)
% 2.02/1.01      | ~ v10_lattices(X0)
% 2.02/1.01      | ~ v10_lattices(X1)
% 2.02/1.01      | ~ v10_lattices(k7_filter_1(X1,X0))
% 2.02/1.01      | ~ v15_lattices(k7_filter_1(X1,X0))
% 2.02/1.01      | ~ l3_lattices(X0)
% 2.02/1.01      | ~ l3_lattices(X1)
% 2.02/1.01      | v2_struct_0(X0)
% 2.02/1.01      | v2_struct_0(X1)
% 2.02/1.01      | v2_struct_0(k7_filter_1(X1,X0))
% 2.02/1.01      | ~ v16_lattices(k7_filter_1(X1,X0)) ),
% 2.02/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_891,c_6]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2616,plain,
% 2.02/1.01      ( sP2(sK5,sK4)
% 2.02/1.01      | ~ v10_lattices(k7_filter_1(sK4,sK5))
% 2.02/1.01      | ~ v10_lattices(sK5)
% 2.02/1.01      | ~ v10_lattices(sK4)
% 2.02/1.01      | ~ v15_lattices(k7_filter_1(sK4,sK5))
% 2.02/1.01      | ~ l3_lattices(sK5)
% 2.02/1.01      | ~ l3_lattices(sK4)
% 2.02/1.01      | v2_struct_0(k7_filter_1(sK4,sK5))
% 2.02/1.01      | v2_struct_0(sK5)
% 2.02/1.01      | v2_struct_0(sK4)
% 2.02/1.01      | ~ v16_lattices(k7_filter_1(sK4,sK5)) ),
% 2.02/1.01      inference(instantiation,[status(thm)],[c_919]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2617,plain,
% 2.02/1.01      ( sP2(sK5,sK4) = iProver_top
% 2.02/1.01      | v10_lattices(k7_filter_1(sK4,sK5)) != iProver_top
% 2.02/1.01      | v10_lattices(sK5) != iProver_top
% 2.02/1.01      | v10_lattices(sK4) != iProver_top
% 2.02/1.01      | v15_lattices(k7_filter_1(sK4,sK5)) != iProver_top
% 2.02/1.01      | l3_lattices(sK5) != iProver_top
% 2.02/1.01      | l3_lattices(sK4) != iProver_top
% 2.02/1.01      | v2_struct_0(k7_filter_1(sK4,sK5)) = iProver_top
% 2.02/1.01      | v2_struct_0(sK5) = iProver_top
% 2.02/1.01      | v2_struct_0(sK4) = iProver_top
% 2.02/1.01      | v16_lattices(k7_filter_1(sK4,sK5)) != iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_2616]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_7,plain,
% 2.02/1.01      ( ~ sP1(X0,X1)
% 2.02/1.01      | sP0(X0,X1)
% 2.02/1.01      | ~ v10_lattices(k7_filter_1(X1,X0))
% 2.02/1.01      | ~ v11_lattices(k7_filter_1(X1,X0))
% 2.02/1.01      | ~ l3_lattices(k7_filter_1(X1,X0))
% 2.02/1.01      | v2_struct_0(k7_filter_1(X1,X0)) ),
% 2.02/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_840,plain,
% 2.02/1.01      ( sP0(X0,X1)
% 2.02/1.01      | ~ v10_lattices(X0)
% 2.02/1.01      | ~ v10_lattices(X1)
% 2.02/1.01      | ~ v10_lattices(k7_filter_1(X1,X0))
% 2.02/1.01      | ~ v11_lattices(k7_filter_1(X1,X0))
% 2.02/1.01      | ~ l3_lattices(X0)
% 2.02/1.01      | ~ l3_lattices(X1)
% 2.02/1.01      | ~ l3_lattices(k7_filter_1(X1,X0))
% 2.02/1.01      | v2_struct_0(X0)
% 2.02/1.01      | v2_struct_0(X1)
% 2.02/1.01      | v2_struct_0(k7_filter_1(X1,X0)) ),
% 2.02/1.01      inference(resolution,[status(thm)],[c_21,c_7]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_866,plain,
% 2.02/1.01      ( sP0(X0,X1)
% 2.02/1.01      | ~ v10_lattices(X0)
% 2.02/1.01      | ~ v10_lattices(X1)
% 2.02/1.01      | ~ v10_lattices(k7_filter_1(X1,X0))
% 2.02/1.01      | ~ v11_lattices(k7_filter_1(X1,X0))
% 2.02/1.01      | ~ l3_lattices(X0)
% 2.02/1.01      | ~ l3_lattices(X1)
% 2.02/1.01      | v2_struct_0(X0)
% 2.02/1.01      | v2_struct_0(X1)
% 2.02/1.01      | v2_struct_0(k7_filter_1(X1,X0)) ),
% 2.02/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_840,c_6]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2609,plain,
% 2.02/1.01      ( sP0(sK5,sK4)
% 2.02/1.01      | ~ v10_lattices(k7_filter_1(sK4,sK5))
% 2.02/1.01      | ~ v10_lattices(sK5)
% 2.02/1.01      | ~ v10_lattices(sK4)
% 2.02/1.01      | ~ v11_lattices(k7_filter_1(sK4,sK5))
% 2.02/1.01      | ~ l3_lattices(sK5)
% 2.02/1.01      | ~ l3_lattices(sK4)
% 2.02/1.01      | v2_struct_0(k7_filter_1(sK4,sK5))
% 2.02/1.01      | v2_struct_0(sK5)
% 2.02/1.01      | v2_struct_0(sK4) ),
% 2.02/1.01      inference(instantiation,[status(thm)],[c_866]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2610,plain,
% 2.02/1.01      ( sP0(sK5,sK4) = iProver_top
% 2.02/1.01      | v10_lattices(k7_filter_1(sK4,sK5)) != iProver_top
% 2.02/1.01      | v10_lattices(sK5) != iProver_top
% 2.02/1.01      | v10_lattices(sK4) != iProver_top
% 2.02/1.01      | v11_lattices(k7_filter_1(sK4,sK5)) != iProver_top
% 2.02/1.01      | l3_lattices(sK5) != iProver_top
% 2.02/1.01      | l3_lattices(sK4) != iProver_top
% 2.02/1.01      | v2_struct_0(k7_filter_1(sK4,sK5)) = iProver_top
% 2.02/1.01      | v2_struct_0(sK5) = iProver_top
% 2.02/1.01      | v2_struct_0(sK4) = iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_2609]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2586,plain,
% 2.02/1.01      ( v11_lattices(k7_filter_1(sK4,sK5))
% 2.02/1.01      | ~ l3_lattices(k7_filter_1(sK4,sK5))
% 2.02/1.01      | v2_struct_0(k7_filter_1(sK4,sK5))
% 2.02/1.01      | ~ v17_lattices(k7_filter_1(sK4,sK5)) ),
% 2.02/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2587,plain,
% 2.02/1.01      ( v11_lattices(k7_filter_1(sK4,sK5)) = iProver_top
% 2.02/1.01      | l3_lattices(k7_filter_1(sK4,sK5)) != iProver_top
% 2.02/1.01      | v2_struct_0(k7_filter_1(sK4,sK5)) = iProver_top
% 2.02/1.01      | v17_lattices(k7_filter_1(sK4,sK5)) != iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_2586]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2583,plain,
% 2.02/1.01      ( v15_lattices(k7_filter_1(sK4,sK5))
% 2.02/1.01      | ~ l3_lattices(k7_filter_1(sK4,sK5))
% 2.02/1.01      | v2_struct_0(k7_filter_1(sK4,sK5))
% 2.02/1.01      | ~ v17_lattices(k7_filter_1(sK4,sK5)) ),
% 2.02/1.01      inference(instantiation,[status(thm)],[c_1]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2584,plain,
% 2.02/1.01      ( v15_lattices(k7_filter_1(sK4,sK5)) = iProver_top
% 2.02/1.01      | l3_lattices(k7_filter_1(sK4,sK5)) != iProver_top
% 2.02/1.01      | v2_struct_0(k7_filter_1(sK4,sK5)) = iProver_top
% 2.02/1.01      | v17_lattices(k7_filter_1(sK4,sK5)) != iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_2583]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2580,plain,
% 2.02/1.01      ( ~ l3_lattices(k7_filter_1(sK4,sK5))
% 2.02/1.01      | v2_struct_0(k7_filter_1(sK4,sK5))
% 2.02/1.01      | ~ v17_lattices(k7_filter_1(sK4,sK5))
% 2.02/1.01      | v16_lattices(k7_filter_1(sK4,sK5)) ),
% 2.02/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2581,plain,
% 2.02/1.01      ( l3_lattices(k7_filter_1(sK4,sK5)) != iProver_top
% 2.02/1.01      | v2_struct_0(k7_filter_1(sK4,sK5)) = iProver_top
% 2.02/1.01      | v17_lattices(k7_filter_1(sK4,sK5)) != iProver_top
% 2.02/1.01      | v16_lattices(k7_filter_1(sK4,sK5)) = iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_2580]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_40,negated_conjecture,
% 2.02/1.01      ( ~ v10_lattices(k7_filter_1(sK4,sK5))
% 2.02/1.01      | ~ v10_lattices(sK5)
% 2.02/1.01      | ~ v10_lattices(sK4)
% 2.02/1.01      | ~ l3_lattices(k7_filter_1(sK4,sK5))
% 2.02/1.01      | ~ l3_lattices(sK5)
% 2.02/1.01      | ~ l3_lattices(sK4)
% 2.02/1.01      | v2_struct_0(k7_filter_1(sK4,sK5))
% 2.02/1.01      | v2_struct_0(sK5)
% 2.02/1.01      | v2_struct_0(sK4)
% 2.02/1.01      | ~ v17_lattices(k7_filter_1(sK4,sK5))
% 2.02/1.01      | ~ v17_lattices(sK5)
% 2.02/1.01      | ~ v17_lattices(sK4) ),
% 2.02/1.01      inference(cnf_transformation,[],[f122]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_78,negated_conjecture,
% 2.02/1.01      ( ~ v2_struct_0(sK4) ),
% 2.02/1.01      inference(cnf_transformation,[],[f84]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_77,negated_conjecture,
% 2.02/1.01      ( v10_lattices(sK4) ),
% 2.02/1.01      inference(cnf_transformation,[],[f85]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_76,negated_conjecture,
% 2.02/1.01      ( l3_lattices(sK4) ),
% 2.02/1.01      inference(cnf_transformation,[],[f86]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_75,negated_conjecture,
% 2.02/1.01      ( ~ v2_struct_0(sK5) ),
% 2.02/1.01      inference(cnf_transformation,[],[f87]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_74,negated_conjecture,
% 2.02/1.01      ( v10_lattices(sK5) ),
% 2.02/1.01      inference(cnf_transformation,[],[f88]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_73,negated_conjecture,
% 2.02/1.01      ( l3_lattices(sK5) ),
% 2.02/1.01      inference(cnf_transformation,[],[f89]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_497,negated_conjecture,
% 2.02/1.01      ( ~ v10_lattices(k7_filter_1(sK4,sK5))
% 2.02/1.01      | ~ l3_lattices(k7_filter_1(sK4,sK5))
% 2.02/1.01      | v2_struct_0(k7_filter_1(sK4,sK5))
% 2.02/1.01      | ~ v17_lattices(k7_filter_1(sK4,sK5))
% 2.02/1.01      | ~ v17_lattices(sK5)
% 2.02/1.01      | ~ v17_lattices(sK4) ),
% 2.02/1.01      inference(global_propositional_subsumption,
% 2.02/1.01                [status(thm)],
% 2.02/1.01                [c_40,c_78,c_77,c_76,c_75,c_74,c_73]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_499,plain,
% 2.02/1.01      ( v10_lattices(k7_filter_1(sK4,sK5)) != iProver_top
% 2.02/1.01      | l3_lattices(k7_filter_1(sK4,sK5)) != iProver_top
% 2.02/1.01      | v2_struct_0(k7_filter_1(sK4,sK5)) = iProver_top
% 2.02/1.01      | v17_lattices(k7_filter_1(sK4,sK5)) != iProver_top
% 2.02/1.01      | v17_lattices(sK5) != iProver_top
% 2.02/1.01      | v17_lattices(sK4) != iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_497]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_201,plain,
% 2.02/1.01      ( l3_lattices(X0) != iProver_top
% 2.02/1.01      | v2_struct_0(X0) = iProver_top
% 2.02/1.01      | v17_lattices(X0) != iProver_top
% 2.02/1.01      | v16_lattices(X0) = iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_203,plain,
% 2.02/1.01      ( l3_lattices(sK4) != iProver_top
% 2.02/1.01      | v2_struct_0(sK4) = iProver_top
% 2.02/1.01      | v17_lattices(sK4) != iProver_top
% 2.02/1.01      | v16_lattices(sK4) = iProver_top ),
% 2.02/1.01      inference(instantiation,[status(thm)],[c_201]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_198,plain,
% 2.02/1.01      ( v15_lattices(X0) = iProver_top
% 2.02/1.01      | l3_lattices(X0) != iProver_top
% 2.02/1.01      | v2_struct_0(X0) = iProver_top
% 2.02/1.01      | v17_lattices(X0) != iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_200,plain,
% 2.02/1.01      ( v15_lattices(sK4) = iProver_top
% 2.02/1.01      | l3_lattices(sK4) != iProver_top
% 2.02/1.01      | v2_struct_0(sK4) = iProver_top
% 2.02/1.01      | v17_lattices(sK4) != iProver_top ),
% 2.02/1.01      inference(instantiation,[status(thm)],[c_198]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_195,plain,
% 2.02/1.01      ( v11_lattices(X0) = iProver_top
% 2.02/1.01      | l3_lattices(X0) != iProver_top
% 2.02/1.01      | v2_struct_0(X0) = iProver_top
% 2.02/1.01      | v17_lattices(X0) != iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_197,plain,
% 2.02/1.01      ( v11_lattices(sK4) = iProver_top
% 2.02/1.01      | l3_lattices(sK4) != iProver_top
% 2.02/1.01      | v2_struct_0(sK4) = iProver_top
% 2.02/1.01      | v17_lattices(sK4) != iProver_top ),
% 2.02/1.01      inference(instantiation,[status(thm)],[c_195]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_191,plain,
% 2.02/1.01      ( v11_lattices(X0) != iProver_top
% 2.02/1.01      | v15_lattices(X0) != iProver_top
% 2.02/1.01      | l3_lattices(X0) != iProver_top
% 2.02/1.01      | v2_struct_0(X0) = iProver_top
% 2.02/1.01      | v17_lattices(X0) = iProver_top
% 2.02/1.01      | v16_lattices(X0) != iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_193,plain,
% 2.02/1.01      ( v11_lattices(sK4) != iProver_top
% 2.02/1.01      | v15_lattices(sK4) != iProver_top
% 2.02/1.01      | l3_lattices(sK4) != iProver_top
% 2.02/1.01      | v2_struct_0(sK4) = iProver_top
% 2.02/1.01      | v17_lattices(sK4) = iProver_top
% 2.02/1.01      | v16_lattices(sK4) != iProver_top ),
% 2.02/1.01      inference(instantiation,[status(thm)],[c_191]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_50,negated_conjecture,
% 2.02/1.01      ( v17_lattices(k7_filter_1(sK4,sK5)) | v17_lattices(sK5) ),
% 2.02/1.01      inference(cnf_transformation,[],[f112]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_107,plain,
% 2.02/1.01      ( v17_lattices(k7_filter_1(sK4,sK5)) = iProver_top
% 2.02/1.01      | v17_lattices(sK5) = iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_54,negated_conjecture,
% 2.02/1.01      ( v17_lattices(k7_filter_1(sK4,sK5)) | v17_lattices(sK4) ),
% 2.02/1.01      inference(cnf_transformation,[],[f108]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_103,plain,
% 2.02/1.01      ( v17_lattices(k7_filter_1(sK4,sK5)) = iProver_top
% 2.02/1.01      | v17_lattices(sK4) = iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_58,negated_conjecture,
% 2.02/1.01      ( v10_lattices(k7_filter_1(sK4,sK5)) | v17_lattices(sK5) ),
% 2.02/1.01      inference(cnf_transformation,[],[f104]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_99,plain,
% 2.02/1.01      ( v10_lattices(k7_filter_1(sK4,sK5)) = iProver_top
% 2.02/1.01      | v17_lattices(sK5) = iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_58]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_62,negated_conjecture,
% 2.02/1.01      ( v10_lattices(k7_filter_1(sK4,sK5)) | v17_lattices(sK4) ),
% 2.02/1.01      inference(cnf_transformation,[],[f100]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_95,plain,
% 2.02/1.01      ( v10_lattices(k7_filter_1(sK4,sK5)) = iProver_top
% 2.02/1.01      | v17_lattices(sK4) = iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_62]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_66,negated_conjecture,
% 2.02/1.01      ( ~ v2_struct_0(k7_filter_1(sK4,sK5)) | v17_lattices(sK5) ),
% 2.02/1.01      inference(cnf_transformation,[],[f96]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_91,plain,
% 2.02/1.01      ( v2_struct_0(k7_filter_1(sK4,sK5)) != iProver_top
% 2.02/1.01      | v17_lattices(sK5) = iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_66]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_70,negated_conjecture,
% 2.02/1.01      ( ~ v2_struct_0(k7_filter_1(sK4,sK5)) | v17_lattices(sK4) ),
% 2.02/1.01      inference(cnf_transformation,[],[f92]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_87,plain,
% 2.02/1.01      ( v2_struct_0(k7_filter_1(sK4,sK5)) != iProver_top
% 2.02/1.01      | v17_lattices(sK4) = iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_70]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_84,plain,
% 2.02/1.01      ( l3_lattices(sK5) = iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_73]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_83,plain,
% 2.02/1.01      ( v10_lattices(sK5) = iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_74]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_82,plain,
% 2.02/1.01      ( v2_struct_0(sK5) != iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_75]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_81,plain,
% 2.02/1.01      ( l3_lattices(sK4) = iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_76]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_80,plain,
% 2.02/1.01      ( v10_lattices(sK4) = iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_77]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_79,plain,
% 2.02/1.01      ( v2_struct_0(sK4) != iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_78]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(contradiction,plain,
% 2.02/1.01      ( $false ),
% 2.02/1.01      inference(minisat,
% 2.02/1.01                [status(thm)],
% 2.02/1.01                [c_2919,c_2895,c_2829,c_2818,c_2746,c_2728,c_2692,c_2669,
% 2.02/1.01                 c_2667,c_2665,c_2663,c_2661,c_2659,c_2645,c_2643,c_2641,
% 2.02/1.01                 c_2639,c_2637,c_2626,c_2617,c_2610,c_2587,c_2584,c_2581,
% 2.02/1.01                 c_499,c_203,c_200,c_197,c_193,c_107,c_103,c_99,c_95,
% 2.02/1.01                 c_91,c_87,c_84,c_83,c_82,c_81,c_80,c_79]) ).
% 2.02/1.01  
% 2.02/1.01  
% 2.02/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.02/1.01  
% 2.02/1.01  ------                               Statistics
% 2.02/1.01  
% 2.02/1.01  ------ General
% 2.02/1.01  
% 2.02/1.01  abstr_ref_over_cycles:                  0
% 2.02/1.01  abstr_ref_under_cycles:                 0
% 2.02/1.01  gc_basic_clause_elim:                   0
% 2.02/1.01  forced_gc_time:                         0
% 2.02/1.01  parsing_time:                           0.014
% 2.02/1.01  unif_index_cands_time:                  0.
% 2.02/1.01  unif_index_add_time:                    0.
% 2.02/1.01  orderings_time:                         0.
% 2.02/1.01  out_proof_time:                         0.016
% 2.02/1.01  total_time:                             0.114
% 2.02/1.01  num_of_symbols:                         45
% 2.02/1.01  num_of_terms:                           495
% 2.02/1.01  
% 2.02/1.01  ------ Preprocessing
% 2.02/1.01  
% 2.02/1.01  num_of_splits:                          0
% 2.02/1.01  num_of_split_atoms:                     0
% 2.02/1.01  num_of_reused_defs:                     0
% 2.02/1.01  num_eq_ax_congr_red:                    0
% 2.02/1.01  num_of_sem_filtered_clauses:            0
% 2.02/1.01  num_of_subtypes:                        1
% 2.02/1.01  monotx_restored_types:                  0
% 2.02/1.01  sat_num_of_epr_types:                   0
% 2.02/1.01  sat_num_of_non_cyclic_types:            0
% 2.02/1.01  sat_guarded_non_collapsed_types:        0
% 2.02/1.01  num_pure_diseq_elim:                    0
% 2.02/1.01  simp_replaced_by:                       0
% 2.02/1.01  res_preprocessed:                       104
% 2.02/1.01  prep_upred:                             0
% 2.02/1.01  prep_unflattend:                        0
% 2.02/1.01  smt_new_axioms:                         0
% 2.02/1.01  pred_elim_cands:                        9
% 2.02/1.01  pred_elim:                              2
% 2.02/1.01  pred_elim_cl:                           2
% 2.02/1.01  pred_elim_cycles:                       6
% 2.02/1.01  merged_defs:                            0
% 2.02/1.01  merged_defs_ncl:                        0
% 2.02/1.01  bin_hyper_res:                          0
% 2.02/1.01  prep_cycles:                            2
% 2.02/1.01  pred_elim_time:                         0.025
% 2.02/1.01  splitting_time:                         0.
% 2.02/1.01  sem_filter_time:                        0.
% 2.02/1.01  monotx_time:                            0.
% 2.02/1.01  subtype_inf_time:                       0.
% 2.02/1.01  
% 2.02/1.01  ------ Problem properties
% 2.02/1.01  
% 2.02/1.01  clauses:                                51
% 2.02/1.01  conjectures:                            15
% 2.02/1.01  epr:                                    30
% 2.02/1.01  horn:                                   36
% 2.02/1.01  ground:                                 15
% 2.02/1.01  unary:                                  6
% 2.02/1.01  binary:                                 35
% 2.02/1.01  lits:                                   146
% 2.02/1.01  lits_eq:                                0
% 2.02/1.01  fd_pure:                                0
% 2.02/1.01  fd_pseudo:                              0
% 2.02/1.01  fd_cond:                                0
% 2.02/1.01  fd_pseudo_cond:                         0
% 2.02/1.01  ac_symbols:                             0
% 2.02/1.01  
% 2.02/1.01  ------ Propositional Solver
% 2.02/1.01  
% 2.02/1.01  prop_solver_calls:                      17
% 2.02/1.01  prop_fast_solver_calls:                 1082
% 2.02/1.01  smt_solver_calls:                       0
% 2.02/1.01  smt_fast_solver_calls:                  0
% 2.02/1.01  prop_num_of_clauses:                    454
% 2.02/1.01  prop_preprocess_simplified:             4050
% 2.02/1.01  prop_fo_subsumed:                       39
% 2.02/1.01  prop_solver_time:                       0.
% 2.02/1.01  smt_solver_time:                        0.
% 2.02/1.01  smt_fast_solver_time:                   0.
% 2.02/1.01  prop_fast_solver_time:                  0.
% 2.02/1.01  prop_unsat_core_time:                   0.
% 2.02/1.01  
% 2.02/1.01  ------ QBF
% 2.02/1.01  
% 2.02/1.01  qbf_q_res:                              0
% 2.02/1.01  qbf_num_tautologies:                    0
% 2.02/1.01  qbf_prep_cycles:                        0
% 2.02/1.01  
% 2.02/1.01  ------ BMC1
% 2.02/1.01  
% 2.02/1.01  bmc1_current_bound:                     -1
% 2.02/1.01  bmc1_last_solved_bound:                 -1
% 2.02/1.01  bmc1_unsat_core_size:                   -1
% 2.02/1.01  bmc1_unsat_core_parents_size:           -1
% 2.02/1.01  bmc1_merge_next_fun:                    0
% 2.02/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.02/1.01  
% 2.02/1.01  ------ Instantiation
% 2.02/1.01  
% 2.02/1.01  inst_num_of_clauses:                    113
% 2.02/1.01  inst_num_in_passive:                    4
% 2.02/1.01  inst_num_in_active:                     108
% 2.02/1.01  inst_num_in_unprocessed:                0
% 2.02/1.01  inst_num_of_loops:                      176
% 2.02/1.01  inst_num_of_learning_restarts:          0
% 2.02/1.01  inst_num_moves_active_passive:          61
% 2.02/1.01  inst_lit_activity:                      0
% 2.02/1.01  inst_lit_activity_moves:                0
% 2.02/1.01  inst_num_tautologies:                   0
% 2.02/1.01  inst_num_prop_implied:                  0
% 2.02/1.01  inst_num_existing_simplified:           0
% 2.02/1.01  inst_num_eq_res_simplified:             0
% 2.02/1.01  inst_num_child_elim:                    0
% 2.02/1.01  inst_num_of_dismatching_blockings:      4
% 2.02/1.01  inst_num_of_non_proper_insts:           83
% 2.02/1.01  inst_num_of_duplicates:                 0
% 2.02/1.01  inst_inst_num_from_inst_to_res:         0
% 2.02/1.01  inst_dismatching_checking_time:         0.
% 2.02/1.01  
% 2.02/1.01  ------ Resolution
% 2.02/1.01  
% 2.02/1.01  res_num_of_clauses:                     0
% 2.02/1.01  res_num_in_passive:                     0
% 2.02/1.01  res_num_in_active:                      0
% 2.02/1.01  res_num_of_loops:                       106
% 2.02/1.01  res_forward_subset_subsumed:            0
% 2.02/1.01  res_backward_subset_subsumed:           0
% 2.02/1.01  res_forward_subsumed:                   8
% 2.02/1.01  res_backward_subsumed:                  0
% 2.02/1.01  res_forward_subsumption_resolution:     2
% 2.02/1.01  res_backward_subsumption_resolution:    0
% 2.02/1.01  res_clause_to_clause_subsumption:       26
% 2.02/1.01  res_orphan_elimination:                 0
% 2.02/1.01  res_tautology_del:                      76
% 2.02/1.01  res_num_eq_res_simplified:              0
% 2.02/1.01  res_num_sel_changes:                    0
% 2.02/1.01  res_moves_from_active_to_pass:          0
% 2.02/1.01  
% 2.02/1.01  ------ Superposition
% 2.02/1.01  
% 2.02/1.01  sup_time_total:                         0.
% 2.02/1.01  sup_time_generating:                    0.
% 2.02/1.01  sup_time_sim_full:                      0.
% 2.02/1.01  sup_time_sim_immed:                     0.
% 2.02/1.01  
% 2.02/1.01  sup_num_of_clauses:                     0
% 2.02/1.01  sup_num_in_active:                      0
% 2.02/1.01  sup_num_in_passive:                     0
% 2.02/1.01  sup_num_of_loops:                       0
% 2.02/1.01  sup_fw_superposition:                   0
% 2.02/1.01  sup_bw_superposition:                   0
% 2.02/1.01  sup_immediate_simplified:               0
% 2.02/1.01  sup_given_eliminated:                   0
% 2.02/1.01  comparisons_done:                       0
% 2.02/1.01  comparisons_avoided:                    0
% 2.02/1.01  
% 2.02/1.01  ------ Simplifications
% 2.02/1.01  
% 2.02/1.01  
% 2.02/1.01  sim_fw_subset_subsumed:                 0
% 2.02/1.01  sim_bw_subset_subsumed:                 0
% 2.02/1.01  sim_fw_subsumed:                        0
% 2.02/1.01  sim_bw_subsumed:                        0
% 2.02/1.01  sim_fw_subsumption_res:                 0
% 2.02/1.01  sim_bw_subsumption_res:                 0
% 2.02/1.01  sim_tautology_del:                      0
% 2.02/1.01  sim_eq_tautology_del:                   0
% 2.02/1.01  sim_eq_res_simp:                        0
% 2.02/1.01  sim_fw_demodulated:                     0
% 2.02/1.01  sim_bw_demodulated:                     0
% 2.02/1.01  sim_light_normalised:                   0
% 2.02/1.01  sim_joinable_taut:                      0
% 2.02/1.01  sim_joinable_simp:                      0
% 2.02/1.01  sim_ac_normalised:                      0
% 2.02/1.01  sim_smt_subsumption:                    0
% 2.02/1.01  
%------------------------------------------------------------------------------
