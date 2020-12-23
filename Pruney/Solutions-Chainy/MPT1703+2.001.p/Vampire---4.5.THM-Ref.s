%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:42 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   76 (1639 expanded)
%              Number of leaves         :    9 ( 507 expanded)
%              Depth                    :   40
%              Number of atoms          :  323 (13984 expanded)
%              Number of equality atoms :   87 (1855 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f146,plain,(
    $false ),
    inference(subsumption_resolution,[],[f145,f45])).

fof(f45,plain,(
    sK1 = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(subsumption_resolution,[],[f44,f26])).

fof(f26,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( ~ m1_pre_topc(sK2,sK0)
      | ~ m1_pre_topc(sK1,sK0) )
    & ( m1_pre_topc(sK2,sK0)
      | m1_pre_topc(sK1,sK0) )
    & sK1 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f22,f21,f20])).

fof(f20,plain,
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
              ( ( ~ m1_pre_topc(X2,sK0)
                | ~ m1_pre_topc(X1,sK0) )
              & ( m1_pre_topc(X2,sK0)
                | m1_pre_topc(X1,sK0) )
              & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ m1_pre_topc(X2,sK0)
              | ~ m1_pre_topc(X1,sK0) )
            & ( m1_pre_topc(X2,sK0)
              | m1_pre_topc(X1,sK0) )
            & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
            & l1_pre_topc(X2)
            & v2_pre_topc(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1) )
   => ( ? [X2] :
          ( ( ~ m1_pre_topc(X2,sK0)
            | ~ m1_pre_topc(sK1,sK0) )
          & ( m1_pre_topc(X2,sK0)
            | m1_pre_topc(sK1,sK0) )
          & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK1
          & l1_pre_topc(X2)
          & v2_pre_topc(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X2] :
        ( ( ~ m1_pre_topc(X2,sK0)
          | ~ m1_pre_topc(sK1,sK0) )
        & ( m1_pre_topc(X2,sK0)
          | m1_pre_topc(sK1,sK0) )
        & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK1
        & l1_pre_topc(X2)
        & v2_pre_topc(X2) )
   => ( ( ~ m1_pre_topc(sK2,sK0)
        | ~ m1_pre_topc(sK1,sK0) )
      & ( m1_pre_topc(sK2,sK0)
        | m1_pre_topc(sK1,sK0) )
      & sK1 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
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
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
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

fof(f44,plain,
    ( sK1 = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f33,f41])).

fof(f41,plain,(
    v1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f40,f27])).

fof(f27,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f40,plain,
    ( v1_pre_topc(sK1)
    | ~ v2_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f39,f28])).

fof(f28,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f39,plain,
    ( v1_pre_topc(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(superposition,[],[f35,f29])).

fof(f29,plain,(
    sK1 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f35,plain,(
    ! [X0] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f145,plain,(
    sK1 != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(forward_demodulation,[],[f144,f57])).

fof(f57,plain,(
    u1_struct_0(sK2) = u1_struct_0(sK1) ),
    inference(trivial_inequality_removal,[],[f55])).

fof(f55,plain,
    ( sK1 != sK1
    | u1_struct_0(sK2) = u1_struct_0(sK1) ),
    inference(superposition,[],[f53,f29])).

fof(f53,plain,(
    ! [X2,X3] :
      ( g1_pre_topc(X2,X3) != sK1
      | u1_struct_0(sK1) = X2 ) ),
    inference(forward_demodulation,[],[f51,f45])).

fof(f51,plain,(
    ! [X2,X3] :
      ( u1_struct_0(sK1) = X2
      | g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ) ),
    inference(resolution,[],[f48,f26])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = X1
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(X1,X2) ) ),
    inference(resolution,[],[f37,f32])).

fof(f32,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f144,plain,(
    sK1 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK1)) ),
    inference(forward_demodulation,[],[f143,f77])).

fof(f77,plain,(
    u1_pre_topc(sK2) = u1_pre_topc(sK1) ),
    inference(trivial_inequality_removal,[],[f75])).

fof(f75,plain,
    ( sK1 != sK1
    | u1_pre_topc(sK2) = u1_pre_topc(sK1) ),
    inference(superposition,[],[f73,f45])).

fof(f73,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) != sK1
      | u1_pre_topc(sK2) = X1 ) ),
    inference(forward_demodulation,[],[f71,f59])).

fof(f59,plain,(
    sK1 = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) ),
    inference(backward_demodulation,[],[f29,f57])).

fof(f71,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))
      | u1_pre_topc(sK2) = X1 ) ),
    inference(resolution,[],[f69,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f69,plain,(
    m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f62,f28])).

fof(f62,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK2) ),
    inference(superposition,[],[f32,f57])).

fof(f143,plain,(
    sK1 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(subsumption_resolution,[],[f142,f24])).

fof(f24,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f142,plain,
    ( sK1 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f137,f28])).

fof(f137,plain,
    ( sK1 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(trivial_inequality_removal,[],[f136])).

fof(f136,plain,
    ( sK1 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f134,f130])).

fof(f130,plain,(
    ~ m1_pre_topc(sK2,sK0) ),
    inference(subsumption_resolution,[],[f31,f129])).

fof(f129,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f128,f45])).

fof(f128,plain,
    ( m1_pre_topc(sK1,sK0)
    | sK1 != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(duplicate_literal_removal,[],[f126])).

fof(f126,plain,
    ( m1_pre_topc(sK1,sK0)
    | sK1 != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | m1_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f120,f26])).

fof(f120,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,sK0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK1
      | m1_pre_topc(sK1,sK0) ) ),
    inference(trivial_inequality_removal,[],[f117])).

fof(f117,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,sK0)
      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK1
      | m1_pre_topc(sK1,sK0) ) ),
    inference(resolution,[],[f86,f24])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | m1_pre_topc(X0,X1)
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK1
      | m1_pre_topc(sK1,sK0) ) ),
    inference(forward_demodulation,[],[f85,f45])).

fof(f85,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
      | m1_pre_topc(X0,X1)
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | m1_pre_topc(sK1,sK0) ) ),
    inference(forward_demodulation,[],[f84,f57])).

fof(f84,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK1))
      | m1_pre_topc(X0,X1)
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | m1_pre_topc(sK1,sK0) ) ),
    inference(forward_demodulation,[],[f83,f77])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,X1)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | m1_pre_topc(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f82,f24])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,X1)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(sK0)
      | m1_pre_topc(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f81,f28])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,X1)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(sK2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(sK0)
      | m1_pre_topc(sK1,sK0) ) ),
    inference(resolution,[],[f34,f30])).

fof(f30,plain,
    ( m1_pre_topc(sK2,sK0)
    | m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_pre_topc(X2,X0)
      | m1_pre_topc(X3,X1)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | ~ l1_pre_topc(X3)
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f31,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f134,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,X1)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK1
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1) ) ),
    inference(forward_demodulation,[],[f133,f45])).

fof(f133,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,X1)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1) ) ),
    inference(subsumption_resolution,[],[f132,f24])).

fof(f132,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,X1)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f131,f26])).

fof(f131,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,X1)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(sK1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f129,f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:12:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (2524)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.47  % (2508)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.47  % (2508)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f146,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(subsumption_resolution,[],[f145,f45])).
% 0.22/0.47  fof(f45,plain,(
% 0.22/0.47    sK1 = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 0.22/0.47    inference(subsumption_resolution,[],[f44,f26])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    l1_pre_topc(sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f23])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    (((~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK1,sK0)) & (m1_pre_topc(sK2,sK0) | m1_pre_topc(sK1,sK0)) & sK1 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)) & l1_pre_topc(sK0)),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f22,f21,f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0)) & (m1_pre_topc(X2,X0) | m1_pre_topc(X1,X0)) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : ((~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X1,sK0)) & (m1_pre_topc(X2,sK0) | m1_pre_topc(X1,sK0)) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK0))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ? [X1] : (? [X2] : ((~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X1,sK0)) & (m1_pre_topc(X2,sK0) | m1_pre_topc(X1,sK0)) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : ((~m1_pre_topc(X2,sK0) | ~m1_pre_topc(sK1,sK0)) & (m1_pre_topc(X2,sK0) | m1_pre_topc(sK1,sK0)) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK1 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ? [X2] : ((~m1_pre_topc(X2,sK0) | ~m1_pre_topc(sK1,sK0)) & (m1_pre_topc(X2,sK0) | m1_pre_topc(sK1,sK0)) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK1 & l1_pre_topc(X2) & v2_pre_topc(X2)) => ((~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK1,sK0)) & (m1_pre_topc(sK2,sK0) | m1_pre_topc(sK1,sK0)) & sK1 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0)) & (m1_pre_topc(X2,X0) | m1_pre_topc(X1,X0)) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.22/0.48    inference(flattening,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (? [X2] : (((~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0)) & (m1_pre_topc(X2,X0) | m1_pre_topc(X1,X0))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.22/0.48    inference(nnf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (? [X2] : ((m1_pre_topc(X1,X0) <~> m1_pre_topc(X2,X0)) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.22/0.48    inference(flattening,[],[f8])).
% 0.22/0.48  fof(f8,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (? [X2] : (((m1_pre_topc(X1,X0) <~> m1_pre_topc(X2,X0)) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1) & (l1_pre_topc(X2) & v2_pre_topc(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & l1_pre_topc(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,negated_conjecture,(
% 0.22/0.48    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1 => (m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0))))))),
% 0.22/0.48    inference(negated_conjecture,[],[f6])).
% 0.22/0.48  fof(f6,conjecture,(
% 0.22/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1 => (m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0))))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tmap_1)).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    sK1 = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) | ~l1_pre_topc(sK1)),
% 0.22/0.48    inference(resolution,[],[f33,f41])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    v1_pre_topc(sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f40,f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    v2_pre_topc(sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f23])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    v1_pre_topc(sK1) | ~v2_pre_topc(sK2)),
% 0.22/0.48    inference(subsumption_resolution,[],[f39,f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    l1_pre_topc(sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f23])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    v1_pre_topc(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2)),
% 0.22/0.48    inference(superposition,[],[f35,f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    sK1 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 0.22/0.48    inference(cnf_transformation,[],[f23])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ( ! [X0] : (v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.48    inference(flattening,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~l1_pre_topc(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 0.22/0.48    inference(flattening,[],[f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 0.22/0.48  fof(f145,plain,(
% 0.22/0.48    sK1 != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 0.22/0.48    inference(forward_demodulation,[],[f144,f57])).
% 0.22/0.48  fof(f57,plain,(
% 0.22/0.48    u1_struct_0(sK2) = u1_struct_0(sK1)),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f55])).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    sK1 != sK1 | u1_struct_0(sK2) = u1_struct_0(sK1)),
% 0.22/0.48    inference(superposition,[],[f53,f29])).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    ( ! [X2,X3] : (g1_pre_topc(X2,X3) != sK1 | u1_struct_0(sK1) = X2) )),
% 0.22/0.48    inference(forward_demodulation,[],[f51,f45])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    ( ! [X2,X3] : (u1_struct_0(sK1) = X2 | g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) )),
% 0.22/0.48    inference(resolution,[],[f48,f26])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | u1_struct_0(X0) = X1 | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(X1,X2)) )),
% 0.22/0.48    inference(resolution,[],[f37,f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X0 = X2) )),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).
% 0.22/0.48  fof(f144,plain,(
% 0.22/0.48    sK1 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK1))),
% 0.22/0.48    inference(forward_demodulation,[],[f143,f77])).
% 0.22/0.48  fof(f77,plain,(
% 0.22/0.48    u1_pre_topc(sK2) = u1_pre_topc(sK1)),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f75])).
% 0.22/0.48  fof(f75,plain,(
% 0.22/0.48    sK1 != sK1 | u1_pre_topc(sK2) = u1_pre_topc(sK1)),
% 0.22/0.48    inference(superposition,[],[f73,f45])).
% 0.22/0.48  fof(f73,plain,(
% 0.22/0.48    ( ! [X0,X1] : (g1_pre_topc(X0,X1) != sK1 | u1_pre_topc(sK2) = X1) )),
% 0.22/0.48    inference(forward_demodulation,[],[f71,f59])).
% 0.22/0.48  fof(f59,plain,(
% 0.22/0.48    sK1 = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))),
% 0.22/0.48    inference(backward_demodulation,[],[f29,f57])).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    ( ! [X0,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) | u1_pre_topc(sK2) = X1) )),
% 0.22/0.48    inference(resolution,[],[f69,f38])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X1 = X3) )),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f69,plain,(
% 0.22/0.48    m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.22/0.48    inference(subsumption_resolution,[],[f62,f28])).
% 0.22/0.48  fof(f62,plain,(
% 0.22/0.48    m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~l1_pre_topc(sK2)),
% 0.22/0.48    inference(superposition,[],[f32,f57])).
% 0.22/0.48  fof(f143,plain,(
% 0.22/0.48    sK1 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 0.22/0.48    inference(subsumption_resolution,[],[f142,f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    l1_pre_topc(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f23])).
% 0.22/0.48  fof(f142,plain,(
% 0.22/0.48    sK1 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | ~l1_pre_topc(sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f137,f28])).
% 0.22/0.48  fof(f137,plain,(
% 0.22/0.48    sK1 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | ~l1_pre_topc(sK2) | ~l1_pre_topc(sK0)),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f136])).
% 0.22/0.48  fof(f136,plain,(
% 0.22/0.48    sK1 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~l1_pre_topc(sK2) | ~l1_pre_topc(sK0)),
% 0.22/0.48    inference(resolution,[],[f134,f130])).
% 0.22/0.48  fof(f130,plain,(
% 0.22/0.48    ~m1_pre_topc(sK2,sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f31,f129])).
% 0.22/0.48  fof(f129,plain,(
% 0.22/0.48    m1_pre_topc(sK1,sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f128,f45])).
% 0.22/0.48  fof(f128,plain,(
% 0.22/0.48    m1_pre_topc(sK1,sK0) | sK1 != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f126])).
% 0.22/0.48  fof(f126,plain,(
% 0.22/0.48    m1_pre_topc(sK1,sK0) | sK1 != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) | m1_pre_topc(sK1,sK0)),
% 0.22/0.48    inference(resolution,[],[f120,f26])).
% 0.22/0.48  fof(f120,plain,(
% 0.22/0.48    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,sK0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK1 | m1_pre_topc(sK1,sK0)) )),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f117])).
% 0.22/0.48  fof(f117,plain,(
% 0.22/0.48    ( ! [X0] : (m1_pre_topc(X0,sK0) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK1 | m1_pre_topc(sK1,sK0)) )),
% 0.22/0.48    inference(resolution,[],[f86,f24])).
% 0.22/0.48  fof(f86,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~l1_pre_topc(X1) | m1_pre_topc(X0,X1) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK1 | m1_pre_topc(sK1,sK0)) )),
% 0.22/0.48    inference(forward_demodulation,[],[f85,f45])).
% 0.22/0.48  fof(f85,plain,(
% 0.22/0.48    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) | m1_pre_topc(X0,X1) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1) | m1_pre_topc(sK1,sK0)) )),
% 0.22/0.48    inference(forward_demodulation,[],[f84,f57])).
% 0.22/0.48  fof(f84,plain,(
% 0.22/0.48    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK1)) | m1_pre_topc(X0,X1) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1) | m1_pre_topc(sK1,sK0)) )),
% 0.22/0.48    inference(forward_demodulation,[],[f83,f77])).
% 0.22/0.48  fof(f83,plain,(
% 0.22/0.48    ( ! [X0,X1] : (m1_pre_topc(X0,X1) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1) | m1_pre_topc(sK1,sK0)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f82,f24])).
% 0.22/0.48  fof(f82,plain,(
% 0.22/0.48    ( ! [X0,X1] : (m1_pre_topc(X0,X1) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(sK0) | m1_pre_topc(sK1,sK0)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f81,f28])).
% 0.22/0.48  fof(f81,plain,(
% 0.22/0.48    ( ! [X0,X1] : (m1_pre_topc(X0,X1) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~l1_pre_topc(X0) | ~l1_pre_topc(sK2) | ~l1_pre_topc(X1) | ~l1_pre_topc(sK0) | m1_pre_topc(sK1,sK0)) )),
% 0.22/0.48    inference(resolution,[],[f34,f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    m1_pre_topc(sK2,sK0) | m1_pre_topc(sK1,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f23])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~m1_pre_topc(X2,X0) | m1_pre_topc(X3,X1) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~l1_pre_topc(X3) | ~l1_pre_topc(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (m1_pre_topc(X3,X1) | ~m1_pre_topc(X2,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~l1_pre_topc(X3)) | ~l1_pre_topc(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.48    inference(flattening,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_pre_topc(X3,X1) | (~m1_pre_topc(X2,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X3)) | ~l1_pre_topc(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (l1_pre_topc(X2) => ! [X3] : (l1_pre_topc(X3) => ((m1_pre_topc(X2,X0) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => m1_pre_topc(X3,X1))))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_pre_topc)).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ~m1_pre_topc(sK1,sK0) | ~m1_pre_topc(sK2,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f23])).
% 0.22/0.48  fof(f134,plain,(
% 0.22/0.48    ( ! [X0,X1] : (m1_pre_topc(X0,X1) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK1 | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1)) )),
% 0.22/0.48    inference(forward_demodulation,[],[f133,f45])).
% 0.22/0.48  fof(f133,plain,(
% 0.22/0.48    ( ! [X0,X1] : (m1_pre_topc(X0,X1) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f132,f24])).
% 0.22/0.48  fof(f132,plain,(
% 0.22/0.48    ( ! [X0,X1] : (m1_pre_topc(X0,X1) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(sK0)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f131,f26])).
% 0.22/0.48  fof(f131,plain,(
% 0.22/0.48    ( ! [X0,X1] : (m1_pre_topc(X0,X1) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~l1_pre_topc(X0) | ~l1_pre_topc(sK1) | ~l1_pre_topc(X1) | ~l1_pre_topc(sK0)) )),
% 0.22/0.48    inference(resolution,[],[f129,f34])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (2508)------------------------------
% 0.22/0.48  % (2508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (2508)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (2508)Memory used [KB]: 6268
% 0.22/0.48  % (2508)Time elapsed: 0.062 s
% 0.22/0.48  % (2508)------------------------------
% 0.22/0.48  % (2508)------------------------------
% 0.22/0.49  % (2500)Success in time 0.121 s
%------------------------------------------------------------------------------
