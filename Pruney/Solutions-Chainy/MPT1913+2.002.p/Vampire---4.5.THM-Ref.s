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
% DateTime   : Thu Dec  3 13:22:34 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 638 expanded)
%              Number of leaves         :   10 ( 265 expanded)
%              Depth                    :   10
%              Number of atoms          :  347 (5258 expanded)
%              Number of equality atoms :   62 ( 768 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f68,plain,(
    $false ),
    inference(global_subsumption,[],[f55,f67])).

fof(f67,plain,(
    k1_funct_1(k12_pralg_1(sK0,sK1),sK2) = u1_struct_0(k1_funct_1(sK1,sK2)) ),
    inference(backward_demodulation,[],[f64,f63])).

fof(f63,plain,(
    k1_funct_1(sK1,sK2) = sK4(sK1,k12_pralg_1(sK0,sK1),sK2) ),
    inference(unit_resulting_resolution,[],[f27,f31,f29,f54,f28,f30,f49,f51,f50,f52,f47])).

fof(f47,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X1,X5) = sK4(X1,k12_pralg_1(X0,X1),X5)
      | ~ r2_hidden(X5,X0)
      | ~ v1_partfun1(k12_pralg_1(X0,X1),X0)
      | ~ v1_funct_1(k12_pralg_1(X0,X1))
      | ~ v4_relat_1(k12_pralg_1(X0,X1),X0)
      | ~ v1_relat_1(k12_pralg_1(X0,X1))
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_pralg_1)).

fof(f52,plain,(
    v1_partfun1(k12_pralg_1(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f27,f31,f29,f28,f30,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_partfun1(k12_pralg_1(X0,X1),X0)
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k12_pralg_1)).

fof(f50,plain,(
    v4_relat_1(k12_pralg_1(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f27,f31,f29,f28,f30,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v4_relat_1(k12_pralg_1(X0,X1),X0)
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f51,plain,(
    v1_funct_1(k12_pralg_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f27,f31,f29,f28,f30,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k12_pralg_1(X0,X1))
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f49,plain,(
    v1_relat_1(k12_pralg_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f27,f31,f29,f28,f30,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k12_pralg_1(X0,X1))
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f30,plain,(
    v1_partfun1(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( k1_funct_1(k12_pralg_1(sK0,sK1),sK2) != u1_struct_0(k10_pralg_1(sK0,sK1,sK2))
    & m1_subset_1(sK2,sK0)
    & v2_pralg_1(sK1)
    & v1_partfun1(sK1,sK0)
    & v1_funct_1(sK1)
    & v4_relat_1(sK1,sK0)
    & v1_relat_1(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f19,f18,f17])).

fof(f17,plain,
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

fof(f18,plain,
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

fof(f19,plain,
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_6)).

fof(f28,plain,(
    v4_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f54,plain,(
    r2_hidden(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f26,f32,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f32,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f26,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f29,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f31,plain,(
    v2_pralg_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f27,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f64,plain,(
    k1_funct_1(k12_pralg_1(sK0,sK1),sK2) = u1_struct_0(sK4(sK1,k12_pralg_1(sK0,sK1),sK2)) ),
    inference(unit_resulting_resolution,[],[f27,f31,f29,f54,f28,f30,f49,f51,f50,f52,f46])).

fof(f46,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(k12_pralg_1(X0,X1),X5) = u1_struct_0(sK4(X1,k12_pralg_1(X0,X1),X5))
      | ~ r2_hidden(X5,X0)
      | ~ v1_partfun1(k12_pralg_1(X0,X1),X0)
      | ~ v1_funct_1(k12_pralg_1(X0,X1))
      | ~ v4_relat_1(k12_pralg_1(X0,X1),X0)
      | ~ v1_relat_1(k12_pralg_1(X0,X1))
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
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

fof(f55,plain,(
    k1_funct_1(k12_pralg_1(sK0,sK1),sK2) != u1_struct_0(k1_funct_1(sK1,sK2)) ),
    inference(backward_demodulation,[],[f33,f53])).

fof(f53,plain,(
    k10_pralg_1(sK0,sK1,sK2) = k1_funct_1(sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f26,f27,f31,f29,f28,f30,f32,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k10_pralg_1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k10_pralg_1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k10_pralg_1)).

fof(f33,plain,(
    k1_funct_1(k12_pralg_1(sK0,sK1),sK2) != u1_struct_0(k10_pralg_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:13:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.48  % (2930)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.49  % (2938)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.49  % (2930)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(global_subsumption,[],[f55,f67])).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    k1_funct_1(k12_pralg_1(sK0,sK1),sK2) = u1_struct_0(k1_funct_1(sK1,sK2))),
% 0.22/0.49    inference(backward_demodulation,[],[f64,f63])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    k1_funct_1(sK1,sK2) = sK4(sK1,k12_pralg_1(sK0,sK1),sK2)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f27,f31,f29,f54,f28,f30,f49,f51,f50,f52,f47])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ( ! [X0,X5,X1] : (k1_funct_1(X1,X5) = sK4(X1,k12_pralg_1(X0,X1),X5) | ~r2_hidden(X5,X0) | ~v1_partfun1(k12_pralg_1(X0,X1),X0) | ~v1_funct_1(k12_pralg_1(X0,X1)) | ~v4_relat_1(k12_pralg_1(X0,X1),X0) | ~v1_relat_1(k12_pralg_1(X0,X1)) | ~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(equality_resolution,[],[f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ( ! [X2,X0,X5,X1] : (k1_funct_1(X1,X5) = sK4(X1,X2,X5) | ~r2_hidden(X5,X0) | k12_pralg_1(X0,X1) != X2 | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2) | ~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X0,X1] : (! [X2] : (((k12_pralg_1(X0,X1) = X2 | (! [X4] : (u1_struct_0(X4) != k1_funct_1(X2,sK3(X0,X1,X2)) | k1_funct_1(X1,sK3(X0,X1,X2)) != X4 | ~l1_struct_0(X4)) & r2_hidden(sK3(X0,X1,X2),X0))) & (! [X5] : ((k1_funct_1(X2,X5) = u1_struct_0(sK4(X1,X2,X5)) & k1_funct_1(X1,X5) = sK4(X1,X2,X5) & l1_struct_0(sK4(X1,X2,X5))) | ~r2_hidden(X5,X0)) | k12_pralg_1(X0,X1) != X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f22,f24,f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X2,X1,X0] : (? [X3] : (! [X4] : (k1_funct_1(X2,X3) != u1_struct_0(X4) | k1_funct_1(X1,X3) != X4 | ~l1_struct_0(X4)) & r2_hidden(X3,X0)) => (! [X4] : (u1_struct_0(X4) != k1_funct_1(X2,sK3(X0,X1,X2)) | k1_funct_1(X1,sK3(X0,X1,X2)) != X4 | ~l1_struct_0(X4)) & r2_hidden(sK3(X0,X1,X2),X0)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X5,X2,X1] : (? [X6] : (k1_funct_1(X2,X5) = u1_struct_0(X6) & k1_funct_1(X1,X5) = X6 & l1_struct_0(X6)) => (k1_funct_1(X2,X5) = u1_struct_0(sK4(X1,X2,X5)) & k1_funct_1(X1,X5) = sK4(X1,X2,X5) & l1_struct_0(sK4(X1,X2,X5))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0,X1] : (! [X2] : (((k12_pralg_1(X0,X1) = X2 | ? [X3] : (! [X4] : (k1_funct_1(X2,X3) != u1_struct_0(X4) | k1_funct_1(X1,X3) != X4 | ~l1_struct_0(X4)) & r2_hidden(X3,X0))) & (! [X5] : (? [X6] : (k1_funct_1(X2,X5) = u1_struct_0(X6) & k1_funct_1(X1,X5) = X6 & l1_struct_0(X6)) | ~r2_hidden(X5,X0)) | k12_pralg_1(X0,X1) != X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(rectify,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0,X1] : (! [X2] : (((k12_pralg_1(X0,X1) = X2 | ? [X3] : (! [X4] : (k1_funct_1(X2,X3) != u1_struct_0(X4) | k1_funct_1(X1,X3) != X4 | ~l1_struct_0(X4)) & r2_hidden(X3,X0))) & (! [X3] : (? [X4] : (k1_funct_1(X2,X3) = u1_struct_0(X4) & k1_funct_1(X1,X3) = X4 & l1_struct_0(X4)) | ~r2_hidden(X3,X0)) | k12_pralg_1(X0,X1) != X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(nnf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0,X1] : (! [X2] : ((k12_pralg_1(X0,X1) = X2 <=> ! [X3] : (? [X4] : (k1_funct_1(X2,X3) = u1_struct_0(X4) & k1_funct_1(X1,X3) = X4 & l1_struct_0(X4)) | ~r2_hidden(X3,X0))) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(flattening,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ! [X0,X1] : (! [X2] : ((k12_pralg_1(X0,X1) = X2 <=> ! [X3] : (? [X4] : ((k1_funct_1(X2,X3) = u1_struct_0(X4) & k1_funct_1(X1,X3) = X4) & l1_struct_0(X4)) | ~r2_hidden(X3,X0))) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2))) | (~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1] : ((v2_pralg_1(X1) & v1_partfun1(X1,X0) & v1_funct_1(X1) & v4_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2) & v4_relat_1(X2,X0) & v1_relat_1(X2)) => (k12_pralg_1(X0,X1) = X2 <=> ! [X3] : ~(! [X4] : (l1_struct_0(X4) => ~(k1_funct_1(X2,X3) = u1_struct_0(X4) & k1_funct_1(X1,X3) = X4)) & r2_hidden(X3,X0)))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_pralg_1)).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    v1_partfun1(k12_pralg_1(sK0,sK1),sK0)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f27,f31,f29,f28,f30,f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v1_partfun1(k12_pralg_1(X0,X1),X0) | ~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ! [X0,X1] : ((v1_partfun1(k12_pralg_1(X0,X1),X0) & v1_funct_1(k12_pralg_1(X0,X1)) & v4_relat_1(k12_pralg_1(X0,X1),X0) & v1_relat_1(k12_pralg_1(X0,X1))) | ~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(flattening,[],[f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ! [X0,X1] : ((v1_partfun1(k12_pralg_1(X0,X1),X0) & v1_funct_1(k12_pralg_1(X0,X1)) & v4_relat_1(k12_pralg_1(X0,X1),X0) & v1_relat_1(k12_pralg_1(X0,X1))) | (~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : ((v2_pralg_1(X1) & v1_partfun1(X1,X0) & v1_funct_1(X1) & v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(k12_pralg_1(X0,X1),X0) & v1_funct_1(k12_pralg_1(X0,X1)) & v4_relat_1(k12_pralg_1(X0,X1),X0) & v1_relat_1(k12_pralg_1(X0,X1))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k12_pralg_1)).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    v4_relat_1(k12_pralg_1(sK0,sK1),sK0)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f27,f31,f29,f28,f30,f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v4_relat_1(k12_pralg_1(X0,X1),X0) | ~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    v1_funct_1(k12_pralg_1(sK0,sK1))),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f27,f31,f29,f28,f30,f37])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v1_funct_1(k12_pralg_1(X0,X1)) | ~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    v1_relat_1(k12_pralg_1(sK0,sK1))),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f27,f31,f29,f28,f30,f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v1_relat_1(k12_pralg_1(X0,X1)) | ~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    v1_partfun1(sK1,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ((k1_funct_1(k12_pralg_1(sK0,sK1),sK2) != u1_struct_0(k10_pralg_1(sK0,sK1,sK2)) & m1_subset_1(sK2,sK0)) & v2_pralg_1(sK1) & v1_partfun1(sK1,sK0) & v1_funct_1(sK1) & v4_relat_1(sK1,sK0) & v1_relat_1(sK1)) & ~v1_xboole_0(sK0)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f19,f18,f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (k1_funct_1(k12_pralg_1(X0,X1),X2) != u1_struct_0(k10_pralg_1(X0,X1,X2)) & m1_subset_1(X2,X0)) & v2_pralg_1(X1) & v1_partfun1(X1,X0) & v1_funct_1(X1) & v4_relat_1(X1,X0) & v1_relat_1(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (k1_funct_1(k12_pralg_1(sK0,X1),X2) != u1_struct_0(k10_pralg_1(sK0,X1,X2)) & m1_subset_1(X2,sK0)) & v2_pralg_1(X1) & v1_partfun1(X1,sK0) & v1_funct_1(X1) & v4_relat_1(X1,sK0) & v1_relat_1(X1)) & ~v1_xboole_0(sK0))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ? [X1] : (? [X2] : (k1_funct_1(k12_pralg_1(sK0,X1),X2) != u1_struct_0(k10_pralg_1(sK0,X1,X2)) & m1_subset_1(X2,sK0)) & v2_pralg_1(X1) & v1_partfun1(X1,sK0) & v1_funct_1(X1) & v4_relat_1(X1,sK0) & v1_relat_1(X1)) => (? [X2] : (k1_funct_1(k12_pralg_1(sK0,sK1),X2) != u1_struct_0(k10_pralg_1(sK0,sK1,X2)) & m1_subset_1(X2,sK0)) & v2_pralg_1(sK1) & v1_partfun1(sK1,sK0) & v1_funct_1(sK1) & v4_relat_1(sK1,sK0) & v1_relat_1(sK1))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ? [X2] : (k1_funct_1(k12_pralg_1(sK0,sK1),X2) != u1_struct_0(k10_pralg_1(sK0,sK1,X2)) & m1_subset_1(X2,sK0)) => (k1_funct_1(k12_pralg_1(sK0,sK1),sK2) != u1_struct_0(k10_pralg_1(sK0,sK1,sK2)) & m1_subset_1(sK2,sK0))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f8,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (k1_funct_1(k12_pralg_1(X0,X1),X2) != u1_struct_0(k10_pralg_1(X0,X1,X2)) & m1_subset_1(X2,X0)) & v2_pralg_1(X1) & v1_partfun1(X1,X0) & v1_funct_1(X1) & v4_relat_1(X1,X0) & v1_relat_1(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.51    inference(flattening,[],[f7])).
% 0.22/0.51  fof(f7,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (k1_funct_1(k12_pralg_1(X0,X1),X2) != u1_struct_0(k10_pralg_1(X0,X1,X2)) & m1_subset_1(X2,X0)) & (v2_pralg_1(X1) & v1_partfun1(X1,X0) & v1_funct_1(X1) & v4_relat_1(X1,X0) & v1_relat_1(X1))) & ~v1_xboole_0(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,negated_conjecture,(
% 0.22/0.51    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v2_pralg_1(X1) & v1_partfun1(X1,X0) & v1_funct_1(X1) & v4_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (m1_subset_1(X2,X0) => k1_funct_1(k12_pralg_1(X0,X1),X2) = u1_struct_0(k10_pralg_1(X0,X1,X2)))))),
% 0.22/0.51    inference(negated_conjecture,[],[f5])).
% 0.22/0.51  fof(f5,conjecture,(
% 0.22/0.51    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v2_pralg_1(X1) & v1_partfun1(X1,X0) & v1_funct_1(X1) & v4_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (m1_subset_1(X2,X0) => k1_funct_1(k12_pralg_1(X0,X1),X2) = u1_struct_0(k10_pralg_1(X0,X1,X2)))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_6)).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    v4_relat_1(sK1,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    r2_hidden(sK2,sK0)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f26,f32,f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.51    inference(flattening,[],[f9])).
% 0.22/0.51  fof(f9,plain,(
% 0.22/0.51    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    m1_subset_1(sK2,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ~v1_xboole_0(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    v1_funct_1(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    v2_pralg_1(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    v1_relat_1(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    k1_funct_1(k12_pralg_1(sK0,sK1),sK2) = u1_struct_0(sK4(sK1,k12_pralg_1(sK0,sK1),sK2))),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f27,f31,f29,f54,f28,f30,f49,f51,f50,f52,f46])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ( ! [X0,X5,X1] : (k1_funct_1(k12_pralg_1(X0,X1),X5) = u1_struct_0(sK4(X1,k12_pralg_1(X0,X1),X5)) | ~r2_hidden(X5,X0) | ~v1_partfun1(k12_pralg_1(X0,X1),X0) | ~v1_funct_1(k12_pralg_1(X0,X1)) | ~v4_relat_1(k12_pralg_1(X0,X1),X0) | ~v1_relat_1(k12_pralg_1(X0,X1)) | ~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.51    inference(equality_resolution,[],[f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ( ! [X2,X0,X5,X1] : (k1_funct_1(X2,X5) = u1_struct_0(sK4(X1,X2,X5)) | ~r2_hidden(X5,X0) | k12_pralg_1(X0,X1) != X2 | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2) | ~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    k1_funct_1(k12_pralg_1(sK0,sK1),sK2) != u1_struct_0(k1_funct_1(sK1,sK2))),
% 0.22/0.51    inference(backward_demodulation,[],[f33,f53])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    k10_pralg_1(sK0,sK1,sK2) = k1_funct_1(sK1,sK2)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f26,f27,f31,f29,f28,f30,f32,f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k10_pralg_1(X0,X1,X2) = k1_funct_1(X1,X2) | ~m1_subset_1(X2,X0) | ~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | v1_xboole_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k10_pralg_1(X0,X1,X2) = k1_funct_1(X1,X2) | ~m1_subset_1(X2,X0) | ~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | v1_xboole_0(X0))),
% 0.22/0.51    inference(flattening,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k10_pralg_1(X0,X1,X2) = k1_funct_1(X1,X2) | (~m1_subset_1(X2,X0) | ~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | v1_xboole_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,X0) & v2_pralg_1(X1) & v1_partfun1(X1,X0) & v1_funct_1(X1) & v4_relat_1(X1,X0) & v1_relat_1(X1) & ~v1_xboole_0(X0)) => k10_pralg_1(X0,X1,X2) = k1_funct_1(X1,X2))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k10_pralg_1)).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    k1_funct_1(k12_pralg_1(sK0,sK1),sK2) != u1_struct_0(k10_pralg_1(sK0,sK1,sK2))),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (2930)------------------------------
% 0.22/0.51  % (2930)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (2930)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (2930)Memory used [KB]: 10618
% 0.22/0.51  % (2930)Time elapsed: 0.071 s
% 0.22/0.51  % (2930)------------------------------
% 0.22/0.51  % (2930)------------------------------
% 0.22/0.51  % (2918)Success in time 0.15 s
%------------------------------------------------------------------------------
