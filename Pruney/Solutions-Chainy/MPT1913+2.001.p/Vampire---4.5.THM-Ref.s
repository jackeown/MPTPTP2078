%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 638 expanded)
%              Number of leaves         :   10 ( 265 expanded)
%              Depth                    :   10
%              Number of atoms          :  360 (5284 expanded)
%              Number of equality atoms :   62 ( 768 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f104,plain,(
    $false ),
    inference(subsumption_resolution,[],[f103,f70])).

fof(f70,plain,(
    k1_funct_1(k12_pralg_1(sK0,sK1),sK2) != u1_struct_0(k1_funct_1(sK1,sK2)) ),
    inference(backward_demodulation,[],[f33,f68])).

fof(f68,plain,(
    k10_pralg_1(sK0,sK1,sK2) = k1_funct_1(sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f26,f27,f31,f29,f28,f30,f32,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pralg_1(X1)
      | ~ m1_subset_1(X2,X0)
      | k10_pralg_1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k10_pralg_1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k10_pralg_1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & v2_pralg_1(X1)
        & v1_partfun1(X1,X0)
        & v1_funct_1(X1)
        & v4_relat_1(X1,X0)
        & v1_relat_1(X1)
        & ~ v1_xboole_0(X0) )
     => k10_pralg_1(X0,X1,X2) = k1_funct_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k10_pralg_1)).

fof(f32,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( k1_funct_1(k12_pralg_1(sK0,sK1),sK2) != u1_struct_0(k10_pralg_1(sK0,sK1,sK2))
    & m1_subset_1(sK2,sK0)
    & v2_pralg_1(sK1)
    & v1_partfun1(sK1,sK0)
    & v1_funct_1(sK1)
    & v4_relat_1(sK1,sK0)
    & v1_relat_1(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f18,f17,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_funct_1(k12_pralg_1(X0,X1),X2) != u1_struct_0(k10_pralg_1(X0,X1,X2))
                & m1_subset_1(X2,X0) )
            & v2_pralg_1(X1)
            & v1_partfun1(X1,X0)
            & v1_funct_1(X1)
            & v4_relat_1(X1,X0)
            & v1_relat_1(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_funct_1(k12_pralg_1(sK0,X1),X2) != u1_struct_0(k10_pralg_1(sK0,X1,X2))
              & m1_subset_1(X2,sK0) )
          & v2_pralg_1(X1)
          & v1_partfun1(X1,sK0)
          & v1_funct_1(X1)
          & v4_relat_1(X1,sK0)
          & v1_relat_1(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k1_funct_1(k12_pralg_1(sK0,X1),X2) != u1_struct_0(k10_pralg_1(sK0,X1,X2))
            & m1_subset_1(X2,sK0) )
        & v2_pralg_1(X1)
        & v1_partfun1(X1,sK0)
        & v1_funct_1(X1)
        & v4_relat_1(X1,sK0)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( k1_funct_1(k12_pralg_1(sK0,sK1),X2) != u1_struct_0(k10_pralg_1(sK0,sK1,X2))
          & m1_subset_1(X2,sK0) )
      & v2_pralg_1(sK1)
      & v1_partfun1(sK1,sK0)
      & v1_funct_1(sK1)
      & v4_relat_1(sK1,sK0)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X2] :
        ( k1_funct_1(k12_pralg_1(sK0,sK1),X2) != u1_struct_0(k10_pralg_1(sK0,sK1,X2))
        & m1_subset_1(X2,sK0) )
   => ( k1_funct_1(k12_pralg_1(sK0,sK1),sK2) != u1_struct_0(k10_pralg_1(sK0,sK1,sK2))
      & m1_subset_1(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_funct_1(k12_pralg_1(X0,X1),X2) != u1_struct_0(k10_pralg_1(X0,X1,X2))
              & m1_subset_1(X2,X0) )
          & v2_pralg_1(X1)
          & v1_partfun1(X1,X0)
          & v1_funct_1(X1)
          & v4_relat_1(X1,X0)
          & v1_relat_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_funct_1(k12_pralg_1(X0,X1),X2) != u1_struct_0(k10_pralg_1(X0,X1,X2))
              & m1_subset_1(X2,X0) )
          & v2_pralg_1(X1)
          & v1_partfun1(X1,X0)
          & v1_funct_1(X1)
          & v4_relat_1(X1,X0)
          & v1_relat_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( v2_pralg_1(X1)
              & v1_partfun1(X1,X0)
              & v1_funct_1(X1)
              & v4_relat_1(X1,X0)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,X0)
               => k1_funct_1(k12_pralg_1(X0,X1),X2) = u1_struct_0(k10_pralg_1(X0,X1,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v2_pralg_1(X1)
            & v1_partfun1(X1,X0)
            & v1_funct_1(X1)
            & v4_relat_1(X1,X0)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => k1_funct_1(k12_pralg_1(X0,X1),X2) = u1_struct_0(k10_pralg_1(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_yellow_6)).

fof(f30,plain,(
    v1_partfun1(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f28,plain,(
    v4_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f29,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f31,plain,(
    v2_pralg_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f27,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f26,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f33,plain,(
    k1_funct_1(k12_pralg_1(sK0,sK1),sK2) != u1_struct_0(k10_pralg_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f103,plain,(
    k1_funct_1(k12_pralg_1(sK0,sK1),sK2) = u1_struct_0(k1_funct_1(sK1,sK2)) ),
    inference(backward_demodulation,[],[f102,f101])).

fof(f101,plain,(
    k1_funct_1(sK1,sK2) = sK4(sK1,k12_pralg_1(sK0,sK1),sK2) ),
    inference(unit_resulting_resolution,[],[f27,f31,f29,f69,f28,f30,f64,f66,f65,f67,f50])).

fof(f50,plain,(
    ! [X0,X5,X1] :
      ( ~ v1_funct_1(k12_pralg_1(X0,X1))
      | ~ r2_hidden(X5,X0)
      | ~ v1_partfun1(k12_pralg_1(X0,X1),X0)
      | k1_funct_1(X1,X5) = sK4(X1,k12_pralg_1(X0,X1),X5)
      | ~ v4_relat_1(k12_pralg_1(X0,X1),X0)
      | ~ v1_relat_1(k12_pralg_1(X0,X1))
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X5,X1] :
      ( k1_funct_1(X1,X5) = sK4(X1,X2,X5)
      | ~ r2_hidden(X5,X0)
      | k12_pralg_1(X0,X1) != X2
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k12_pralg_1(X0,X1) = X2
              | ( ! [X4] :
                    ( u1_struct_0(X4) != k1_funct_1(X2,sK3(X0,X1,X2))
                    | k1_funct_1(X1,sK3(X0,X1,X2)) != X4
                    | ~ l1_struct_0(X4) )
                & r2_hidden(sK3(X0,X1,X2),X0) ) )
            & ( ! [X5] :
                  ( ( k1_funct_1(X2,X5) = u1_struct_0(sK4(X1,X2,X5))
                    & k1_funct_1(X1,X5) = sK4(X1,X2,X5)
                    & l1_struct_0(sK4(X1,X2,X5)) )
                  | ~ r2_hidden(X5,X0) )
              | k12_pralg_1(X0,X1) != X2 ) )
          | ~ v1_partfun1(X2,X0)
          | ~ v1_funct_1(X2)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f22,f24,f23])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( k1_funct_1(X2,X3) != u1_struct_0(X4)
              | k1_funct_1(X1,X3) != X4
              | ~ l1_struct_0(X4) )
          & r2_hidden(X3,X0) )
     => ( ! [X4] :
            ( u1_struct_0(X4) != k1_funct_1(X2,sK3(X0,X1,X2))
            | k1_funct_1(X1,sK3(X0,X1,X2)) != X4
            | ~ l1_struct_0(X4) )
        & r2_hidden(sK3(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X5,X2,X1] :
      ( ? [X6] :
          ( k1_funct_1(X2,X5) = u1_struct_0(X6)
          & k1_funct_1(X1,X5) = X6
          & l1_struct_0(X6) )
     => ( k1_funct_1(X2,X5) = u1_struct_0(sK4(X1,X2,X5))
        & k1_funct_1(X1,X5) = sK4(X1,X2,X5)
        & l1_struct_0(sK4(X1,X2,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k12_pralg_1(X0,X1) = X2
              | ? [X3] :
                  ( ! [X4] :
                      ( k1_funct_1(X2,X3) != u1_struct_0(X4)
                      | k1_funct_1(X1,X3) != X4
                      | ~ l1_struct_0(X4) )
                  & r2_hidden(X3,X0) ) )
            & ( ! [X5] :
                  ( ? [X6] :
                      ( k1_funct_1(X2,X5) = u1_struct_0(X6)
                      & k1_funct_1(X1,X5) = X6
                      & l1_struct_0(X6) )
                  | ~ r2_hidden(X5,X0) )
              | k12_pralg_1(X0,X1) != X2 ) )
          | ~ v1_partfun1(X2,X0)
          | ~ v1_funct_1(X2)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k12_pralg_1(X0,X1) = X2
              | ? [X3] :
                  ( ! [X4] :
                      ( k1_funct_1(X2,X3) != u1_struct_0(X4)
                      | k1_funct_1(X1,X3) != X4
                      | ~ l1_struct_0(X4) )
                  & r2_hidden(X3,X0) ) )
            & ( ! [X3] :
                  ( ? [X4] :
                      ( k1_funct_1(X2,X3) = u1_struct_0(X4)
                      & k1_funct_1(X1,X3) = X4
                      & l1_struct_0(X4) )
                  | ~ r2_hidden(X3,X0) )
              | k12_pralg_1(X0,X1) != X2 ) )
          | ~ v1_partfun1(X2,X0)
          | ~ v1_funct_1(X2)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k12_pralg_1(X0,X1) = X2
          <=> ! [X3] :
                ( ? [X4] :
                    ( k1_funct_1(X2,X3) = u1_struct_0(X4)
                    & k1_funct_1(X1,X3) = X4
                    & l1_struct_0(X4) )
                | ~ r2_hidden(X3,X0) ) )
          | ~ v1_partfun1(X2,X0)
          | ~ v1_funct_1(X2)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k12_pralg_1(X0,X1) = X2
          <=> ! [X3] :
                ( ? [X4] :
                    ( k1_funct_1(X2,X3) = u1_struct_0(X4)
                    & k1_funct_1(X1,X3) = X4
                    & l1_struct_0(X4) )
                | ~ r2_hidden(X3,X0) ) )
          | ~ v1_partfun1(X2,X0)
          | ~ v1_funct_1(X2)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v2_pralg_1(X1)
        & v1_partfun1(X1,X0)
        & v1_funct_1(X1)
        & v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2)
            & v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => ( k12_pralg_1(X0,X1) = X2
          <=> ! [X3] :
                ~ ( ! [X4] :
                      ( l1_struct_0(X4)
                     => ~ ( k1_funct_1(X2,X3) = u1_struct_0(X4)
                          & k1_funct_1(X1,X3) = X4 ) )
                  & r2_hidden(X3,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_pralg_1)).

fof(f67,plain,(
    v1_partfun1(k12_pralg_1(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f27,f31,f29,f28,f30,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v2_pralg_1(X1)
      | v1_partfun1(k12_pralg_1(X0,X1),X0)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(k12_pralg_1(X0,X1),X0)
        & v1_funct_1(k12_pralg_1(X0,X1))
        & v4_relat_1(k12_pralg_1(X0,X1),X0)
        & v1_relat_1(k12_pralg_1(X0,X1)) )
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(k12_pralg_1(X0,X1),X0)
        & v1_funct_1(k12_pralg_1(X0,X1))
        & v4_relat_1(k12_pralg_1(X0,X1),X0)
        & v1_relat_1(k12_pralg_1(X0,X1)) )
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v2_pralg_1(X1)
        & v1_partfun1(X1,X0)
        & v1_funct_1(X1)
        & v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(k12_pralg_1(X0,X1),X0)
        & v1_funct_1(k12_pralg_1(X0,X1))
        & v4_relat_1(k12_pralg_1(X0,X1),X0)
        & v1_relat_1(k12_pralg_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k12_pralg_1)).

fof(f65,plain,(
    v4_relat_1(k12_pralg_1(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f27,f31,f29,f28,f30,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v2_pralg_1(X1)
      | v4_relat_1(k12_pralg_1(X0,X1),X0)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f66,plain,(
    v1_funct_1(k12_pralg_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f27,f31,f29,f28,f30,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k12_pralg_1(X0,X1))
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f64,plain,(
    v1_relat_1(k12_pralg_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f27,f31,f29,f28,f30,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k12_pralg_1(X0,X1))
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f69,plain,(
    r2_hidden(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f26,f32,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f102,plain,(
    k1_funct_1(k12_pralg_1(sK0,sK1),sK2) = u1_struct_0(sK4(sK1,k12_pralg_1(sK0,sK1),sK2)) ),
    inference(unit_resulting_resolution,[],[f27,f31,f29,f69,f28,f30,f64,f66,f65,f67,f49])).

fof(f49,plain,(
    ! [X0,X5,X1] :
      ( ~ v1_funct_1(k12_pralg_1(X0,X1))
      | ~ r2_hidden(X5,X0)
      | ~ v1_partfun1(k12_pralg_1(X0,X1),X0)
      | k1_funct_1(k12_pralg_1(X0,X1),X5) = u1_struct_0(sK4(X1,k12_pralg_1(X0,X1),X5))
      | ~ v4_relat_1(k12_pralg_1(X0,X1),X0)
      | ~ v1_relat_1(k12_pralg_1(X0,X1))
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X5,X1] :
      ( k1_funct_1(X2,X5) = u1_struct_0(sK4(X1,X2,X5))
      | ~ r2_hidden(X5,X0)
      | k12_pralg_1(X0,X1) != X2
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n012.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:04:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (22619)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.48  % (22611)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (22619)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f103,f70])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    k1_funct_1(k12_pralg_1(sK0,sK1),sK2) != u1_struct_0(k1_funct_1(sK1,sK2))),
% 0.21/0.48    inference(backward_demodulation,[],[f33,f68])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    k10_pralg_1(sK0,sK1,sK2) = k1_funct_1(sK1,sK2)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f26,f27,f31,f29,f28,f30,f32,f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v2_pralg_1(X1) | ~m1_subset_1(X2,X0) | k10_pralg_1(X0,X1,X2) = k1_funct_1(X1,X2) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k10_pralg_1(X0,X1,X2) = k1_funct_1(X1,X2) | ~m1_subset_1(X2,X0) | ~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | v1_xboole_0(X0))),
% 0.21/0.48    inference(flattening,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k10_pralg_1(X0,X1,X2) = k1_funct_1(X1,X2) | (~m1_subset_1(X2,X0) | ~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | v1_xboole_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,X0) & v2_pralg_1(X1) & v1_partfun1(X1,X0) & v1_funct_1(X1) & v4_relat_1(X1,X0) & v1_relat_1(X1) & ~v1_xboole_0(X0)) => k10_pralg_1(X0,X1,X2) = k1_funct_1(X1,X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k10_pralg_1)).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    m1_subset_1(sK2,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ((k1_funct_1(k12_pralg_1(sK0,sK1),sK2) != u1_struct_0(k10_pralg_1(sK0,sK1,sK2)) & m1_subset_1(sK2,sK0)) & v2_pralg_1(sK1) & v1_partfun1(sK1,sK0) & v1_funct_1(sK1) & v4_relat_1(sK1,sK0) & v1_relat_1(sK1)) & ~v1_xboole_0(sK0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f18,f17,f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (k1_funct_1(k12_pralg_1(X0,X1),X2) != u1_struct_0(k10_pralg_1(X0,X1,X2)) & m1_subset_1(X2,X0)) & v2_pralg_1(X1) & v1_partfun1(X1,X0) & v1_funct_1(X1) & v4_relat_1(X1,X0) & v1_relat_1(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (k1_funct_1(k12_pralg_1(sK0,X1),X2) != u1_struct_0(k10_pralg_1(sK0,X1,X2)) & m1_subset_1(X2,sK0)) & v2_pralg_1(X1) & v1_partfun1(X1,sK0) & v1_funct_1(X1) & v4_relat_1(X1,sK0) & v1_relat_1(X1)) & ~v1_xboole_0(sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ? [X1] : (? [X2] : (k1_funct_1(k12_pralg_1(sK0,X1),X2) != u1_struct_0(k10_pralg_1(sK0,X1,X2)) & m1_subset_1(X2,sK0)) & v2_pralg_1(X1) & v1_partfun1(X1,sK0) & v1_funct_1(X1) & v4_relat_1(X1,sK0) & v1_relat_1(X1)) => (? [X2] : (k1_funct_1(k12_pralg_1(sK0,sK1),X2) != u1_struct_0(k10_pralg_1(sK0,sK1,X2)) & m1_subset_1(X2,sK0)) & v2_pralg_1(sK1) & v1_partfun1(sK1,sK0) & v1_funct_1(sK1) & v4_relat_1(sK1,sK0) & v1_relat_1(sK1))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ? [X2] : (k1_funct_1(k12_pralg_1(sK0,sK1),X2) != u1_struct_0(k10_pralg_1(sK0,sK1,X2)) & m1_subset_1(X2,sK0)) => (k1_funct_1(k12_pralg_1(sK0,sK1),sK2) != u1_struct_0(k10_pralg_1(sK0,sK1,sK2)) & m1_subset_1(sK2,sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (k1_funct_1(k12_pralg_1(X0,X1),X2) != u1_struct_0(k10_pralg_1(X0,X1,X2)) & m1_subset_1(X2,X0)) & v2_pralg_1(X1) & v1_partfun1(X1,X0) & v1_funct_1(X1) & v4_relat_1(X1,X0) & v1_relat_1(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.48    inference(flattening,[],[f7])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (k1_funct_1(k12_pralg_1(X0,X1),X2) != u1_struct_0(k10_pralg_1(X0,X1,X2)) & m1_subset_1(X2,X0)) & (v2_pralg_1(X1) & v1_partfun1(X1,X0) & v1_funct_1(X1) & v4_relat_1(X1,X0) & v1_relat_1(X1))) & ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,negated_conjecture,(
% 0.21/0.48    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v2_pralg_1(X1) & v1_partfun1(X1,X0) & v1_funct_1(X1) & v4_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (m1_subset_1(X2,X0) => k1_funct_1(k12_pralg_1(X0,X1),X2) = u1_struct_0(k10_pralg_1(X0,X1,X2)))))),
% 0.21/0.48    inference(negated_conjecture,[],[f5])).
% 0.21/0.48  fof(f5,conjecture,(
% 0.21/0.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v2_pralg_1(X1) & v1_partfun1(X1,X0) & v1_funct_1(X1) & v4_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (m1_subset_1(X2,X0) => k1_funct_1(k12_pralg_1(X0,X1),X2) = u1_struct_0(k10_pralg_1(X0,X1,X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_yellow_6)).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    v1_partfun1(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    v4_relat_1(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    v1_funct_1(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    v2_pralg_1(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    v1_relat_1(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ~v1_xboole_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    k1_funct_1(k12_pralg_1(sK0,sK1),sK2) != u1_struct_0(k10_pralg_1(sK0,sK1,sK2))),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    k1_funct_1(k12_pralg_1(sK0,sK1),sK2) = u1_struct_0(k1_funct_1(sK1,sK2))),
% 0.21/0.48    inference(backward_demodulation,[],[f102,f101])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    k1_funct_1(sK1,sK2) = sK4(sK1,k12_pralg_1(sK0,sK1),sK2)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f27,f31,f29,f69,f28,f30,f64,f66,f65,f67,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X0,X5,X1] : (~v1_funct_1(k12_pralg_1(X0,X1)) | ~r2_hidden(X5,X0) | ~v1_partfun1(k12_pralg_1(X0,X1),X0) | k1_funct_1(X1,X5) = sK4(X1,k12_pralg_1(X0,X1),X5) | ~v4_relat_1(k12_pralg_1(X0,X1),X0) | ~v1_relat_1(k12_pralg_1(X0,X1)) | ~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(equality_resolution,[],[f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X2,X0,X5,X1] : (k1_funct_1(X1,X5) = sK4(X1,X2,X5) | ~r2_hidden(X5,X0) | k12_pralg_1(X0,X1) != X2 | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2) | ~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (((k12_pralg_1(X0,X1) = X2 | (! [X4] : (u1_struct_0(X4) != k1_funct_1(X2,sK3(X0,X1,X2)) | k1_funct_1(X1,sK3(X0,X1,X2)) != X4 | ~l1_struct_0(X4)) & r2_hidden(sK3(X0,X1,X2),X0))) & (! [X5] : ((k1_funct_1(X2,X5) = u1_struct_0(sK4(X1,X2,X5)) & k1_funct_1(X1,X5) = sK4(X1,X2,X5) & l1_struct_0(sK4(X1,X2,X5))) | ~r2_hidden(X5,X0)) | k12_pralg_1(X0,X1) != X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f22,f24,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X2,X1,X0] : (? [X3] : (! [X4] : (k1_funct_1(X2,X3) != u1_struct_0(X4) | k1_funct_1(X1,X3) != X4 | ~l1_struct_0(X4)) & r2_hidden(X3,X0)) => (! [X4] : (u1_struct_0(X4) != k1_funct_1(X2,sK3(X0,X1,X2)) | k1_funct_1(X1,sK3(X0,X1,X2)) != X4 | ~l1_struct_0(X4)) & r2_hidden(sK3(X0,X1,X2),X0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X5,X2,X1] : (? [X6] : (k1_funct_1(X2,X5) = u1_struct_0(X6) & k1_funct_1(X1,X5) = X6 & l1_struct_0(X6)) => (k1_funct_1(X2,X5) = u1_struct_0(sK4(X1,X2,X5)) & k1_funct_1(X1,X5) = sK4(X1,X2,X5) & l1_struct_0(sK4(X1,X2,X5))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (((k12_pralg_1(X0,X1) = X2 | ? [X3] : (! [X4] : (k1_funct_1(X2,X3) != u1_struct_0(X4) | k1_funct_1(X1,X3) != X4 | ~l1_struct_0(X4)) & r2_hidden(X3,X0))) & (! [X5] : (? [X6] : (k1_funct_1(X2,X5) = u1_struct_0(X6) & k1_funct_1(X1,X5) = X6 & l1_struct_0(X6)) | ~r2_hidden(X5,X0)) | k12_pralg_1(X0,X1) != X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(rectify,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (((k12_pralg_1(X0,X1) = X2 | ? [X3] : (! [X4] : (k1_funct_1(X2,X3) != u1_struct_0(X4) | k1_funct_1(X1,X3) != X4 | ~l1_struct_0(X4)) & r2_hidden(X3,X0))) & (! [X3] : (? [X4] : (k1_funct_1(X2,X3) = u1_struct_0(X4) & k1_funct_1(X1,X3) = X4 & l1_struct_0(X4)) | ~r2_hidden(X3,X0)) | k12_pralg_1(X0,X1) != X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(nnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : ((k12_pralg_1(X0,X1) = X2 <=> ! [X3] : (? [X4] : (k1_funct_1(X2,X3) = u1_struct_0(X4) & k1_funct_1(X1,X3) = X4 & l1_struct_0(X4)) | ~r2_hidden(X3,X0))) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : ((k12_pralg_1(X0,X1) = X2 <=> ! [X3] : (? [X4] : ((k1_funct_1(X2,X3) = u1_struct_0(X4) & k1_funct_1(X1,X3) = X4) & l1_struct_0(X4)) | ~r2_hidden(X3,X0))) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2))) | (~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v2_pralg_1(X1) & v1_partfun1(X1,X0) & v1_funct_1(X1) & v4_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2) & v4_relat_1(X2,X0) & v1_relat_1(X2)) => (k12_pralg_1(X0,X1) = X2 <=> ! [X3] : ~(! [X4] : (l1_struct_0(X4) => ~(k1_funct_1(X2,X3) = u1_struct_0(X4) & k1_funct_1(X1,X3) = X4)) & r2_hidden(X3,X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_pralg_1)).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    v1_partfun1(k12_pralg_1(sK0,sK1),sK0)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f27,f31,f29,f28,f30,f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v2_pralg_1(X1) | v1_partfun1(k12_pralg_1(X0,X1),X0) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0,X1] : ((v1_partfun1(k12_pralg_1(X0,X1),X0) & v1_funct_1(k12_pralg_1(X0,X1)) & v4_relat_1(k12_pralg_1(X0,X1),X0) & v1_relat_1(k12_pralg_1(X0,X1))) | ~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0,X1] : ((v1_partfun1(k12_pralg_1(X0,X1),X0) & v1_funct_1(k12_pralg_1(X0,X1)) & v4_relat_1(k12_pralg_1(X0,X1),X0) & v1_relat_1(k12_pralg_1(X0,X1))) | (~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v2_pralg_1(X1) & v1_partfun1(X1,X0) & v1_funct_1(X1) & v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(k12_pralg_1(X0,X1),X0) & v1_funct_1(k12_pralg_1(X0,X1)) & v4_relat_1(k12_pralg_1(X0,X1),X0) & v1_relat_1(k12_pralg_1(X0,X1))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k12_pralg_1)).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    v4_relat_1(k12_pralg_1(sK0,sK1),sK0)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f27,f31,f29,f28,f30,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v2_pralg_1(X1) | v4_relat_1(k12_pralg_1(X0,X1),X0) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    v1_funct_1(k12_pralg_1(sK0,sK1))),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f27,f31,f29,f28,f30,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_funct_1(k12_pralg_1(X0,X1)) | ~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    v1_relat_1(k12_pralg_1(sK0,sK1))),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f27,f31,f29,f28,f30,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_relat_1(k12_pralg_1(X0,X1)) | ~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    r2_hidden(sK2,sK0)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f26,f32,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.21/0.48    inference(nnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    k1_funct_1(k12_pralg_1(sK0,sK1),sK2) = u1_struct_0(sK4(sK1,k12_pralg_1(sK0,sK1),sK2))),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f27,f31,f29,f69,f28,f30,f64,f66,f65,f67,f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X0,X5,X1] : (~v1_funct_1(k12_pralg_1(X0,X1)) | ~r2_hidden(X5,X0) | ~v1_partfun1(k12_pralg_1(X0,X1),X0) | k1_funct_1(k12_pralg_1(X0,X1),X5) = u1_struct_0(sK4(X1,k12_pralg_1(X0,X1),X5)) | ~v4_relat_1(k12_pralg_1(X0,X1),X0) | ~v1_relat_1(k12_pralg_1(X0,X1)) | ~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(equality_resolution,[],[f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X2,X0,X5,X1] : (k1_funct_1(X2,X5) = u1_struct_0(sK4(X1,X2,X5)) | ~r2_hidden(X5,X0) | k12_pralg_1(X0,X1) != X2 | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2) | ~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (22619)------------------------------
% 0.21/0.48  % (22619)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (22619)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (22619)Memory used [KB]: 6268
% 0.21/0.48  % (22619)Time elapsed: 0.010 s
% 0.21/0.48  % (22619)------------------------------
% 0.21/0.48  % (22619)------------------------------
% 0.21/0.48  % (22603)Success in time 0.12 s
%------------------------------------------------------------------------------
