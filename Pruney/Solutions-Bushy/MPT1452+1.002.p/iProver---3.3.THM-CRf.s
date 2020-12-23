%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1452+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:42 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 625 expanded)
%              Number of clauses        :   85 ( 129 expanded)
%              Number of leaves         :   14 ( 131 expanded)
%              Depth                    :   12
%              Number of atoms          : 1291 (8606 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal clause size      :   60 (   5 average)
%              Maximal term depth       :    2 (   1 average)

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

fof(f13,plain,(
    ! [X0] :
      ( ( v16_lattices(X0)
        & v15_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0] :
      ( ( v16_lattices(X0)
        & v15_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f13])).

fof(f55,plain,(
    ! [X0] :
      ( v16_lattices(X0)
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f54,plain,(
    ! [X0] :
      ( v15_lattices(X0)
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f53,plain,(
    ! [X0] :
      ( v11_lattices(X0)
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f32,plain,(
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

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f46,plain,(
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
    inference(rectify,[],[f45])).

fof(f92,plain,(
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
    inference(cnf_transformation,[],[f46])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1)
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v3_lattices(k7_filter_1(X0,X1))
        & ~ v2_struct_0(k7_filter_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1)
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ~ v2_struct_0(k7_filter_1(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1)
        & l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v10_lattices(k7_filter_1(X0,X1))
        & v3_lattices(k7_filter_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1)
        & l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => v10_lattices(k7_filter_1(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v10_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v10_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v10_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f29,plain,(
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

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f74,plain,(
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
    inference(cnf_transformation,[],[f40])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
      <=> ( l3_lattices(k7_filter_1(X0,X1))
          & v11_lattices(k7_filter_1(X0,X1))
          & v10_lattices(k7_filter_1(X0,X1))
          & ~ v2_struct_0(k7_filter_1(X0,X1)) ) )
      | ~ sP1(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v11_lattices(k7_filter_1(X1,X0))
      | ~ sP0(X0,X1)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
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

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X1,X0)
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f24,f30,f29])).

fof(f75,plain,(
    ! [X0,X1] :
      ( sP1(X1,X0)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v10_lattices(X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f69,plain,(
    ! [X0,X1] :
      ( l3_lattices(X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v10_lattices(X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f73,plain,(
    ! [X0,X1] :
      ( l3_lattices(X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1)
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( l3_lattices(k7_filter_1(X0,X1))
        & v3_lattices(k7_filter_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1)
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => l3_lattices(k7_filter_1(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f17,plain,(
    ! [X0,X1] :
      ( l3_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f18,plain,(
    ! [X0,X1] :
      ( l3_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f58,plain,(
    ! [X0,X1] :
      ( l3_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

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

fof(f15,plain,(
    ! [X0] :
      ( ( v17_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v16_lattices(X0)
      | ~ v15_lattices(X0)
      | ~ v11_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0] :
      ( ( v17_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v16_lattices(X0)
      | ~ v15_lattices(X0)
      | ~ v11_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f15])).

fof(f57,plain,(
    ! [X0] :
      ( v17_lattices(X0)
      | ~ v16_lattices(X0)
      | ~ v15_lattices(X0)
      | ~ v11_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v15_lattices(X1)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v16_lattices(X1)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ( sP2(X1,X0)
      <=> ( l3_lattices(k7_filter_1(X0,X1))
          & v16_lattices(k7_filter_1(X0,X1))
          & v15_lattices(k7_filter_1(X0,X1))
          & v10_lattices(k7_filter_1(X0,X1))
          & ~ v2_struct_0(k7_filter_1(X0,X1)) ) )
      | ~ sP3(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v16_lattices(k7_filter_1(X1,X0))
      | ~ sP2(X0,X1)
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
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

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP3(X1,X0)
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f26,f33,f32])).

fof(f93,plain,(
    ! [X0,X1] :
      ( sP3(X1,X0)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(X1)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v10_lattices(X1)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f86,plain,(
    ! [X0,X1] :
      ( l3_lattices(X1)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(X0)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v10_lattices(X0)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f91,plain,(
    ! [X0,X1] :
      ( l3_lattices(X0)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v15_lattices(k7_filter_1(X1,X0))
      | ~ sP2(X0,X1)
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v15_lattices(X0)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f90,plain,(
    ! [X0,X1] :
      ( v16_lattices(X0)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f65,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ l3_lattices(k7_filter_1(X1,X0))
      | ~ v11_lattices(k7_filter_1(X1,X0))
      | ~ v10_lattices(k7_filter_1(X1,X0))
      | v2_struct_0(k7_filter_1(X1,X0))
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v11_lattices(X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v11_lattices(X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f81,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
      | ~ l3_lattices(k7_filter_1(X1,X0))
      | ~ v16_lattices(k7_filter_1(X1,X0))
      | ~ v15_lattices(k7_filter_1(X1,X0))
      | ~ v10_lattices(k7_filter_1(X1,X0))
      | v2_struct_0(k7_filter_1(X1,X0))
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,conjecture,(
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

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f50,plain,(
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

fof(f49,plain,
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

fof(f51,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f48,f50,f49])).

fof(f132,plain,
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
    inference(cnf_transformation,[],[f51])).

fof(f94,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f95,plain,(
    v10_lattices(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f96,plain,(
    l3_lattices(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f97,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f98,plain,(
    v10_lattices(sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f99,plain,(
    l3_lattices(sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f122,plain,
    ( v17_lattices(k7_filter_1(sK4,sK5))
    | v17_lattices(sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f118,plain,
    ( v17_lattices(k7_filter_1(sK4,sK5))
    | v17_lattices(sK4) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_0,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v17_lattices(X0)
    | v16_lattices(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2469,plain,
    ( ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ v17_lattices(sK5)
    | v16_lattices(sK5) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1,plain,
    ( v15_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v17_lattices(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2381,plain,
    ( v15_lattices(sK5)
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ v17_lattices(sK5) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( v11_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v17_lattices(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2312,plain,
    ( v11_lattices(sK5)
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ v17_lattices(sK5) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_30,plain,
    ( sP2(X0,X1)
    | ~ v10_lattices(X1)
    | ~ v10_lattices(X0)
    | ~ v15_lattices(X0)
    | ~ v15_lattices(X1)
    | ~ l3_lattices(X0)
    | ~ l3_lattices(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v16_lattices(X0)
    | ~ v16_lattices(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2280,plain,
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
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_7,plain,
    ( ~ l3_lattices(X0)
    | ~ l3_lattices(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_struct_0(k7_filter_1(X0,X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2262,plain,
    ( ~ l3_lattices(sK5)
    | ~ l3_lattices(sK4)
    | ~ v2_struct_0(k7_filter_1(sK4,sK5))
    | v2_struct_0(sK5)
    | v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_8,plain,
    ( ~ v10_lattices(X0)
    | ~ v10_lattices(X1)
    | v10_lattices(k7_filter_1(X1,X0))
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2243,plain,
    ( v10_lattices(k7_filter_1(sK4,sK5))
    | ~ v10_lattices(sK5)
    | ~ v10_lattices(sK4)
    | ~ l3_lattices(sK5)
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_14,plain,
    ( sP0(X0,X1)
    | ~ v10_lattices(X1)
    | ~ v10_lattices(X0)
    | ~ v11_lattices(X0)
    | ~ v11_lattices(X1)
    | ~ l3_lattices(X0)
    | ~ l3_lattices(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_11,plain,
    ( ~ sP1(X0,X1)
    | ~ sP0(X0,X1)
    | v11_lattices(k7_filter_1(X1,X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_23,plain,
    ( sP1(X0,X1)
    | ~ v10_lattices(X0)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_22,plain,
    ( ~ sP0(X0,X1)
    | ~ v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_21,plain,
    ( ~ sP0(X0,X1)
    | v10_lattices(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_19,plain,
    ( ~ sP0(X0,X1)
    | l3_lattices(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_18,plain,
    ( ~ sP0(X0,X1)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_17,plain,
    ( ~ sP0(X0,X1)
    | v10_lattices(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_15,plain,
    ( ~ sP0(X0,X1)
    | l3_lattices(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_586,plain,
    ( ~ sP0(X0,X1)
    | v11_lattices(k7_filter_1(X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_23,c_22,c_21,c_19,c_18,c_17,c_15])).

cnf(c_1049,plain,
    ( ~ v10_lattices(X0)
    | ~ v10_lattices(X1)
    | ~ v11_lattices(X1)
    | ~ v11_lattices(X0)
    | v11_lattices(k7_filter_1(X1,X0))
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_14,c_586])).

cnf(c_2219,plain,
    ( ~ v10_lattices(sK5)
    | ~ v10_lattices(sK4)
    | v11_lattices(k7_filter_1(sK4,sK5))
    | ~ v11_lattices(sK5)
    | ~ v11_lattices(sK4)
    | ~ l3_lattices(sK5)
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1049])).

cnf(c_6,plain,
    ( ~ l3_lattices(X0)
    | ~ l3_lattices(X1)
    | l3_lattices(k7_filter_1(X0,X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2193,plain,
    ( l3_lattices(k7_filter_1(sK4,sK5))
    | ~ l3_lattices(sK5)
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_4,plain,
    ( ~ v11_lattices(X0)
    | ~ v15_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | v17_lattices(X0)
    | ~ v16_lattices(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2175,plain,
    ( ~ v11_lattices(sK5)
    | ~ v15_lattices(sK5)
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | v17_lattices(sK5)
    | ~ v16_lattices(sK5) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_38,plain,
    ( ~ sP2(X0,X1)
    | v15_lattices(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2151,plain,
    ( ~ sP2(sK5,sK4)
    | v15_lattices(sK4) ),
    inference(instantiation,[status(thm)],[c_38])).

cnf(c_37,plain,
    ( ~ sP2(X0,X1)
    | v16_lattices(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2152,plain,
    ( ~ sP2(sK5,sK4)
    | v16_lattices(sK4) ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_26,plain,
    ( ~ sP3(X0,X1)
    | ~ sP2(X0,X1)
    | v16_lattices(k7_filter_1(X1,X0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_41,plain,
    ( sP3(X0,X1)
    | ~ v10_lattices(X0)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_40,plain,
    ( ~ sP2(X0,X1)
    | ~ v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_39,plain,
    ( ~ sP2(X0,X1)
    | v10_lattices(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_36,plain,
    ( ~ sP2(X0,X1)
    | l3_lattices(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_35,plain,
    ( ~ sP2(X0,X1)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_34,plain,
    ( ~ sP2(X0,X1)
    | v10_lattices(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_31,plain,
    ( ~ sP2(X0,X1)
    | l3_lattices(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_547,plain,
    ( ~ sP2(X0,X1)
    | v16_lattices(k7_filter_1(X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_26,c_41,c_40,c_39,c_36,c_35,c_34,c_31])).

cnf(c_2153,plain,
    ( ~ sP2(sK5,sK4)
    | v16_lattices(k7_filter_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_547])).

cnf(c_27,plain,
    ( ~ sP3(X0,X1)
    | ~ sP2(X0,X1)
    | v15_lattices(k7_filter_1(X1,X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_540,plain,
    ( ~ sP2(X0,X1)
    | v15_lattices(k7_filter_1(X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_27,c_41,c_40,c_39,c_36,c_35,c_34,c_31])).

cnf(c_2154,plain,
    ( ~ sP2(sK5,sK4)
    | v15_lattices(k7_filter_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_540])).

cnf(c_33,plain,
    ( ~ sP2(X0,X1)
    | v15_lattices(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2155,plain,
    ( ~ sP2(sK5,sK4)
    | v15_lattices(sK5) ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_32,plain,
    ( ~ sP2(X0,X1)
    | v16_lattices(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2156,plain,
    ( ~ sP2(sK5,sK4)
    | v16_lattices(sK5) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_9,plain,
    ( ~ sP1(X0,X1)
    | sP0(X0,X1)
    | ~ v10_lattices(k7_filter_1(X1,X0))
    | ~ v11_lattices(k7_filter_1(X1,X0))
    | ~ l3_lattices(k7_filter_1(X1,X0))
    | v2_struct_0(k7_filter_1(X1,X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_862,plain,
    ( sP0(X0,X1)
    | ~ v10_lattices(X1)
    | ~ v10_lattices(X0)
    | ~ v10_lattices(k7_filter_1(X1,X0))
    | ~ v11_lattices(k7_filter_1(X1,X0))
    | ~ l3_lattices(X0)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(k7_filter_1(X1,X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(k7_filter_1(X1,X0)) ),
    inference(resolution,[status(thm)],[c_23,c_9])).

cnf(c_866,plain,
    ( ~ v10_lattices(X0)
    | ~ v10_lattices(X1)
    | sP0(X0,X1)
    | ~ v11_lattices(k7_filter_1(X1,X0))
    | ~ l3_lattices(X0)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(k7_filter_1(X1,X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(k7_filter_1(X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_862,c_23,c_9,c_8])).

cnf(c_867,plain,
    ( sP0(X0,X1)
    | ~ v10_lattices(X1)
    | ~ v10_lattices(X0)
    | ~ v11_lattices(k7_filter_1(X1,X0))
    | ~ l3_lattices(X0)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(k7_filter_1(X1,X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(k7_filter_1(X1,X0)) ),
    inference(renaming,[status(thm)],[c_866])).

cnf(c_892,plain,
    ( sP0(X0,X1)
    | ~ v10_lattices(X1)
    | ~ v10_lattices(X0)
    | ~ v11_lattices(k7_filter_1(X1,X0))
    | ~ l3_lattices(X0)
    | ~ l3_lattices(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_867,c_7,c_6])).

cnf(c_16,plain,
    ( ~ sP0(X0,X1)
    | v11_lattices(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1017,plain,
    ( ~ v10_lattices(X0)
    | ~ v10_lattices(X1)
    | v11_lattices(X0)
    | ~ v11_lattices(k7_filter_1(X1,X0))
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_892,c_16])).

cnf(c_2140,plain,
    ( ~ v10_lattices(sK5)
    | ~ v10_lattices(sK4)
    | ~ v11_lattices(k7_filter_1(sK4,sK5))
    | v11_lattices(sK5)
    | ~ l3_lattices(sK5)
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1017])).

cnf(c_20,plain,
    ( ~ sP0(X0,X1)
    | v11_lattices(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_985,plain,
    ( ~ v10_lattices(X0)
    | ~ v10_lattices(X1)
    | v11_lattices(X1)
    | ~ v11_lattices(k7_filter_1(X1,X0))
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_892,c_20])).

cnf(c_2141,plain,
    ( ~ v10_lattices(sK5)
    | ~ v10_lattices(sK4)
    | ~ v11_lattices(k7_filter_1(sK4,sK5))
    | v11_lattices(sK4)
    | ~ l3_lattices(sK5)
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_985])).

cnf(c_2137,plain,
    ( ~ v11_lattices(k7_filter_1(sK4,sK5))
    | ~ v15_lattices(k7_filter_1(sK4,sK5))
    | ~ l3_lattices(k7_filter_1(sK4,sK5))
    | v2_struct_0(k7_filter_1(sK4,sK5))
    | v17_lattices(k7_filter_1(sK4,sK5))
    | ~ v16_lattices(k7_filter_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_24,plain,
    ( ~ sP3(X0,X1)
    | sP2(X0,X1)
    | ~ v10_lattices(k7_filter_1(X1,X0))
    | ~ v15_lattices(k7_filter_1(X1,X0))
    | ~ l3_lattices(k7_filter_1(X1,X0))
    | v2_struct_0(k7_filter_1(X1,X0))
    | ~ v16_lattices(k7_filter_1(X1,X0)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_913,plain,
    ( sP2(X0,X1)
    | ~ v10_lattices(X1)
    | ~ v10_lattices(X0)
    | ~ v10_lattices(k7_filter_1(X1,X0))
    | ~ v15_lattices(k7_filter_1(X1,X0))
    | ~ l3_lattices(X0)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(k7_filter_1(X1,X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(k7_filter_1(X1,X0))
    | ~ v16_lattices(k7_filter_1(X1,X0)) ),
    inference(resolution,[status(thm)],[c_41,c_24])).

cnf(c_917,plain,
    ( ~ v10_lattices(X0)
    | ~ v10_lattices(X1)
    | sP2(X0,X1)
    | ~ v15_lattices(k7_filter_1(X1,X0))
    | ~ l3_lattices(X0)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(k7_filter_1(X1,X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(k7_filter_1(X1,X0))
    | ~ v16_lattices(k7_filter_1(X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_913,c_41,c_24,c_8])).

cnf(c_918,plain,
    ( sP2(X0,X1)
    | ~ v10_lattices(X1)
    | ~ v10_lattices(X0)
    | ~ v15_lattices(k7_filter_1(X1,X0))
    | ~ l3_lattices(X0)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(k7_filter_1(X1,X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(k7_filter_1(X1,X0))
    | ~ v16_lattices(k7_filter_1(X1,X0)) ),
    inference(renaming,[status(thm)],[c_917])).

cnf(c_945,plain,
    ( sP2(X0,X1)
    | ~ v10_lattices(X1)
    | ~ v10_lattices(X0)
    | ~ v15_lattices(k7_filter_1(X1,X0))
    | ~ l3_lattices(X0)
    | ~ l3_lattices(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v16_lattices(k7_filter_1(X1,X0)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_918,c_7,c_6])).

cnf(c_2134,plain,
    ( sP2(sK5,sK4)
    | ~ v10_lattices(sK5)
    | ~ v10_lattices(sK4)
    | ~ v15_lattices(k7_filter_1(sK4,sK5))
    | ~ l3_lattices(sK5)
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | ~ v16_lattices(k7_filter_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_945])).

cnf(c_2126,plain,
    ( v11_lattices(k7_filter_1(sK4,sK5))
    | ~ l3_lattices(k7_filter_1(sK4,sK5))
    | v2_struct_0(k7_filter_1(sK4,sK5))
    | ~ v17_lattices(k7_filter_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2123,plain,
    ( v15_lattices(k7_filter_1(sK4,sK5))
    | ~ l3_lattices(k7_filter_1(sK4,sK5))
    | v2_struct_0(k7_filter_1(sK4,sK5))
    | ~ v17_lattices(k7_filter_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2120,plain,
    ( ~ l3_lattices(k7_filter_1(sK4,sK5))
    | v2_struct_0(k7_filter_1(sK4,sK5))
    | ~ v17_lattices(k7_filter_1(sK4,sK5))
    | v16_lattices(k7_filter_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_42,negated_conjecture,
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
    inference(cnf_transformation,[],[f132])).

cnf(c_80,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_79,negated_conjecture,
    ( v10_lattices(sK4) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_78,negated_conjecture,
    ( l3_lattices(sK4) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_77,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_76,negated_conjecture,
    ( v10_lattices(sK5) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_75,negated_conjecture,
    ( l3_lattices(sK5) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_509,negated_conjecture,
    ( ~ v10_lattices(k7_filter_1(sK4,sK5))
    | ~ l3_lattices(k7_filter_1(sK4,sK5))
    | v2_struct_0(k7_filter_1(sK4,sK5))
    | ~ v17_lattices(k7_filter_1(sK4,sK5))
    | ~ v17_lattices(sK5)
    | ~ v17_lattices(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_42,c_80,c_79,c_78,c_77,c_76,c_75])).

cnf(c_210,plain,
    ( ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v17_lattices(sK4)
    | v16_lattices(sK4) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_207,plain,
    ( v15_lattices(sK4)
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v17_lattices(sK4) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_204,plain,
    ( v11_lattices(sK4)
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v17_lattices(sK4) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_200,plain,
    ( ~ v11_lattices(sK4)
    | ~ v15_lattices(sK4)
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | v17_lattices(sK4)
    | ~ v16_lattices(sK4) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_52,negated_conjecture,
    ( v17_lattices(k7_filter_1(sK4,sK5))
    | v17_lattices(sK5) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_56,negated_conjecture,
    ( v17_lattices(k7_filter_1(sK4,sK5))
    | v17_lattices(sK4) ),
    inference(cnf_transformation,[],[f118])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2469,c_2381,c_2312,c_2280,c_2262,c_2243,c_2219,c_2193,c_2175,c_2151,c_2152,c_2153,c_2154,c_2155,c_2156,c_2140,c_2141,c_2137,c_2134,c_2126,c_2123,c_2120,c_509,c_210,c_207,c_204,c_200,c_52,c_56,c_75,c_76,c_77,c_78,c_79,c_80])).


%------------------------------------------------------------------------------
