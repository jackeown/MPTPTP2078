%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1703+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:29 EST 2020

% Result     : Theorem 8.26s
% Output     : Refutation 8.26s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 210 expanded)
%              Number of leaves         :    9 (  66 expanded)
%              Depth                    :   19
%              Number of atoms          :  262 (1886 expanded)
%              Number of equality atoms :   39 ( 224 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9258,plain,(
    $false ),
    inference(subsumption_resolution,[],[f9257,f3466])).

fof(f3466,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f3413])).

fof(f3413,plain,
    ( ( ~ m1_pre_topc(sK4,sK2)
      | ~ m1_pre_topc(sK3,sK2) )
    & ( m1_pre_topc(sK4,sK2)
      | m1_pre_topc(sK3,sK2) )
    & sK3 = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f3409,f3412,f3411,f3410])).

fof(f3410,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0) )
                & ( m1_pre_topc(X2,X0)
                  | m1_pre_topc(X1,X0) )
                & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
                & l1_pre_topc(X2)
                & v2_pre_topc(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,sK2)
                | ~ m1_pre_topc(X1,sK2) )
              & ( m1_pre_topc(X2,sK2)
                | m1_pre_topc(X1,sK2) )
              & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f3411,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ m1_pre_topc(X2,sK2)
              | ~ m1_pre_topc(X1,sK2) )
            & ( m1_pre_topc(X2,sK2)
              | m1_pre_topc(X1,sK2) )
            & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
            & l1_pre_topc(X2)
            & v2_pre_topc(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1) )
   => ( ? [X2] :
          ( ( ~ m1_pre_topc(X2,sK2)
            | ~ m1_pre_topc(sK3,sK2) )
          & ( m1_pre_topc(X2,sK2)
            | m1_pre_topc(sK3,sK2) )
          & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK3
          & l1_pre_topc(X2)
          & v2_pre_topc(X2) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f3412,plain,
    ( ? [X2] :
        ( ( ~ m1_pre_topc(X2,sK2)
          | ~ m1_pre_topc(sK3,sK2) )
        & ( m1_pre_topc(X2,sK2)
          | m1_pre_topc(sK3,sK2) )
        & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK3
        & l1_pre_topc(X2)
        & v2_pre_topc(X2) )
   => ( ( ~ m1_pre_topc(sK4,sK2)
        | ~ m1_pre_topc(sK3,sK2) )
      & ( m1_pre_topc(sK4,sK2)
        | m1_pre_topc(sK3,sK2) )
      & sK3 = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f3409,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,X0)
                | ~ m1_pre_topc(X1,X0) )
              & ( m1_pre_topc(X2,X0)
                | m1_pre_topc(X1,X0) )
              & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f3408])).

fof(f3408,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,X0)
                | ~ m1_pre_topc(X1,X0) )
              & ( m1_pre_topc(X2,X0)
                | m1_pre_topc(X1,X0) )
              & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f3344])).

fof(f3344,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( m1_pre_topc(X1,X0)
              <~> m1_pre_topc(X2,X0) )
              & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f3343])).

fof(f3343,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( m1_pre_topc(X1,X0)
              <~> m1_pre_topc(X2,X0) )
              & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3329])).

fof(f3329,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( l1_pre_topc(X2)
                  & v2_pre_topc(X2) )
               => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
                 => ( m1_pre_topc(X1,X0)
                  <=> m1_pre_topc(X2,X0) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3328])).

fof(f3328,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
               => ( m1_pre_topc(X1,X0)
                <=> m1_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tmap_1)).

fof(f9257,plain,(
    ~ l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f9245,f3663])).

fof(f3663,plain,(
    ~ m1_pre_topc(sK4,sK2) ),
    inference(subsumption_resolution,[],[f3473,f3662])).

fof(f3662,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(duplicate_literal_removal,[],[f3661])).

fof(f3661,plain,
    ( m1_pre_topc(sK3,sK2)
    | m1_pre_topc(sK3,sK2) ),
    inference(forward_demodulation,[],[f3660,f3471])).

fof(f3471,plain,(
    sK3 = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
    inference(cnf_transformation,[],[f3413])).

fof(f3660,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK2)
    | m1_pre_topc(sK3,sK2) ),
    inference(subsumption_resolution,[],[f3657,f3466])).

fof(f3657,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK2)
    | ~ l1_pre_topc(sK2)
    | m1_pre_topc(sK3,sK2) ),
    inference(resolution,[],[f3537,f3472])).

fof(f3472,plain,
    ( m1_pre_topc(sK4,sK2)
    | m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f3413])).

fof(f3537,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3385])).

fof(f3385,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3327])).

fof(f3327,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

fof(f3473,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f3413])).

fof(f9245,plain,
    ( m1_pre_topc(sK4,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(equality_resolution,[],[f6180])).

fof(f6180,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
      | m1_pre_topc(sK4,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f6178,f3466])).

fof(f6178,plain,(
    ! [X0] :
      ( m1_pre_topc(sK4,X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(sK2) ) ),
    inference(resolution,[],[f4527,f3662])).

fof(f4527,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(sK3,X0)
      | m1_pre_topc(sK4,X1)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(trivial_inequality_removal,[],[f4526])).

fof(f4526,plain,(
    ! [X0,X1] :
      ( sK3 != sK3
      | ~ m1_pre_topc(sK3,X0)
      | m1_pre_topc(sK4,X1)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f3916,f3641])).

fof(f3641,plain,(
    sK3 = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
    inference(subsumption_resolution,[],[f3638,f3468])).

fof(f3468,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f3413])).

fof(f3638,plain,
    ( sK3 = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f3542,f3615])).

fof(f3615,plain,(
    v1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f3614,f3469])).

fof(f3469,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f3413])).

fof(f3614,plain,
    ( v1_pre_topc(sK3)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f3613,f3470])).

fof(f3470,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f3413])).

fof(f3613,plain,
    ( v1_pre_topc(sK3)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(superposition,[],[f3522,f3471])).

fof(f3522,plain,(
    ! [X0] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3375])).

fof(f3375,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f3374])).

fof(f3374,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1801])).

fof(f1801,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(f3542,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3392])).

fof(f3392,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f3391])).

fof(f3391,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1759])).

fof(f1759,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f3916,plain,(
    ! [X2,X0,X1] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK3
      | ~ m1_pre_topc(X0,X1)
      | m1_pre_topc(sK4,X2)
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(X1) ) ),
    inference(subsumption_resolution,[],[f3913,f3470])).

fof(f3913,plain,(
    ! [X2,X0,X1] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK3
      | ~ m1_pre_topc(X0,X1)
      | m1_pre_topc(sK4,X2)
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
      | ~ l1_pre_topc(sK4)
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(X1) ) ),
    inference(superposition,[],[f3600,f3471])).

fof(f3600,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
      | ~ m1_pre_topc(X2,X0)
      | m1_pre_topc(X3,X1)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | ~ l1_pre_topc(X3)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f3538,f3497])).

fof(f3497,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3364])).

fof(f3364,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1784])).

fof(f1784,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f3538,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_pre_topc(X3,X1)
      | ~ m1_pre_topc(X2,X0)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | ~ l1_pre_topc(X3)
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3387])).

fof(f3387,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( m1_pre_topc(X3,X1)
                  | ~ m1_pre_topc(X2,X0)
                  | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ l1_pre_topc(X3) )
              | ~ l1_pre_topc(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f3386])).

fof(f3386,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( m1_pre_topc(X3,X1)
                  | ~ m1_pre_topc(X2,X0)
                  | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ l1_pre_topc(X3) )
              | ~ l1_pre_topc(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1831])).

fof(f1831,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( l1_pre_topc(X2)
             => ! [X3] :
                  ( l1_pre_topc(X3)
                 => ( ( m1_pre_topc(X2,X0)
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                      & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                   => m1_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_pre_topc)).
%------------------------------------------------------------------------------
