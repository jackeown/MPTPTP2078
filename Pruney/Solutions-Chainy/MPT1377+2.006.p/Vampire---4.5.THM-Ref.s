%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:54 EST 2020

% Result     : Theorem 1.27s
% Output     : Refutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :  122 (9385 expanded)
%              Number of leaves         :   13 (2263 expanded)
%              Depth                    :   47
%              Number of atoms          :  415 (45049 expanded)
%              Number of equality atoms :   46 (3324 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f592,plain,(
    $false ),
    inference(subsumption_resolution,[],[f590,f375])).

fof(f375,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f352])).

fof(f352,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f37,f350])).

fof(f350,plain,(
    u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(equality_resolution,[],[f309])).

fof(f309,plain,(
    ! [X10,X9] :
      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X9,X10)
      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X9 ) ),
    inference(subsumption_resolution,[],[f285,f308])).

fof(f308,plain,(
    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ),
    inference(subsumption_resolution,[],[f307,f33])).

fof(f33,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
      | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_compts_1(sK1,sK0) )
    & ( ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        & v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
      | ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        & v2_compts_1(sK1,sK0) ) )
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v2_compts_1(X1,X0) )
            & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
                & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
              | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                & v2_compts_1(X1,X0) ) ) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
            | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
            | ~ v2_compts_1(X1,sK0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
              & v2_compts_1(X1,sK0) ) ) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
          | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          | ~ v2_compts_1(X1,sK0) )
        & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
            & v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
          | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
            & v2_compts_1(X1,sK0) ) ) )
   => ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_compts_1(sK1,sK0) )
      & ( ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
          & v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
        | ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
          & v2_compts_1(sK1,sK0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v2_compts_1(X1,X0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) ) ) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v2_compts_1(X1,X0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) ) ) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_compts_1(X1,X0) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_compts_1(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_compts_1)).

fof(f307,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f295,f59])).

fof(f59,plain,(
    ! [X1] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f48,f41])).

fof(f41,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f295,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ),
    inference(superposition,[],[f41,f281])).

fof(f281,plain,(
    u1_pre_topc(sK0) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(trivial_inequality_removal,[],[f278])).

fof(f278,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
    | u1_pre_topc(sK0) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f275,f33])).

fof(f275,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(X1)
      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = u1_pre_topc(X1) ) ),
    inference(resolution,[],[f248,f41])).

fof(f248,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3)))
      | u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X4
      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X3,X4) ) ),
    inference(superposition,[],[f50,f237])).

fof(f237,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    inference(resolution,[],[f63,f33])).

fof(f63,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(X1)
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) ) ),
    inference(subsumption_resolution,[],[f61,f59])).

fof(f61,plain,(
    ! [X1] :
      ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f42,f57])).

fof(f57,plain,(
    ! [X1] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f47,f41])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X1 = X3
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f285,plain,(
    ! [X10,X9] :
      ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X9,X10)
      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X9 ) ),
    inference(backward_demodulation,[],[f251,f281])).

fof(f251,plain,(
    ! [X10,X9] :
      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X9,X10)
      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X9
      | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ) ),
    inference(superposition,[],[f49,f237])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f37,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f590,plain,(
    ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f576,f373])).

fof(f373,plain,(
    ! [X4] :
      ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X4),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(backward_demodulation,[],[f341,f350])).

fof(f341,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
      | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X4),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ) ),
    inference(forward_demodulation,[],[f340,f282])).

fof(f282,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(sK0)) ),
    inference(backward_demodulation,[],[f237,f281])).

fof(f340,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(sK0)))))
      | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X4),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ) ),
    inference(forward_demodulation,[],[f339,f281])).

fof(f339,plain,(
    ! [X4] :
      ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X4),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))) ) ),
    inference(forward_demodulation,[],[f338,f282])).

fof(f338,plain,(
    ! [X4] :
      ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(sK0)),X4),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))) ) ),
    inference(forward_demodulation,[],[f330,f281])).

fof(f330,plain,(
    ! [X4] :
      ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),X4),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))) ) ),
    inference(resolution,[],[f315,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) ) ),
    inference(subsumption_resolution,[],[f67,f59])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0),X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f52,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(f315,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(forward_demodulation,[],[f312,f282])).

fof(f312,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f308,f48])).

fof(f576,plain,(
    ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f575,f55])).

fof(f55,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f40,f39])).

fof(f39,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f40,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f575,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(forward_demodulation,[],[f574,f450])).

fof(f450,plain,(
    sK1 = u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) ),
    inference(resolution,[],[f417,f375])).

fof(f417,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f409,f315])).

fof(f409,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)) = X0
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ) ),
    inference(superposition,[],[f45,f350])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

fof(f574,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))))
    | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f573,f507])).

fof(f507,plain,(
    ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f377,f506])).

fof(f506,plain,(
    v2_compts_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f505,f375])).

fof(f505,plain,
    ( v2_compts_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f502,f354])).

fof(f354,plain,(
    ! [X0] :
      ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(backward_demodulation,[],[f103,f350])).

fof(f103,plain,(
    ! [X0] :
      ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ) ),
    inference(resolution,[],[f68,f33])).

fof(f502,plain,
    ( ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0)
    | v2_compts_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f501,f55])).

fof(f501,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | v2_compts_1(sK1,sK0)
    | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0) ),
    inference(forward_demodulation,[],[f500,f450])).

fof(f500,plain,
    ( v2_compts_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))))
    | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0) ),
    inference(duplicate_literal_removal,[],[f497])).

fof(f497,plain,
    ( v2_compts_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))))
    | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0)
    | v2_compts_1(sK1,sK0) ),
    inference(resolution,[],[f496,f389])).

fof(f389,plain,(
    ! [X0] :
      ( ~ v2_compts_1(sK1,X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X0,sK0)
      | v2_compts_1(sK1,sK0) ) ),
    inference(resolution,[],[f375,f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_compts_1(X0,X1)
      | ~ m1_pre_topc(X1,sK0)
      | v2_compts_1(X0,sK0) ) ),
    inference(resolution,[],[f53,f33])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_compts_1(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_compts_1(X3,X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_compts_1(X2,X0)
      | ~ v2_compts_1(X3,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v2_compts_1(X2,X0)
                      | ~ v2_compts_1(X3,X1) )
                    & ( v2_compts_1(X3,X1)
                      | ~ v2_compts_1(X2,X0) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v2_compts_1(X2,X0)
                  <=> v2_compts_1(X3,X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v2_compts_1(X2,X0)
                  <=> v2_compts_1(X3,X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( X2 = X3
                   => ( v2_compts_1(X2,X0)
                    <=> v2_compts_1(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_compts_1)).

fof(f496,plain,
    ( v2_compts_1(sK1,k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | v2_compts_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f495,f375])).

fof(f495,plain,
    ( v2_compts_1(sK1,k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | v2_compts_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f492,f55])).

fof(f492,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | v2_compts_1(sK1,k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | v2_compts_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f487,f450])).

fof(f487,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0))))
      | v2_compts_1(sK1,k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0))
      | v2_compts_1(sK1,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f486,f373])).

fof(f486,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_compts_1(sK1,X0)
      | v2_compts_1(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f485,f375])).

fof(f485,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | v2_compts_1(sK1,X0)
      | v2_compts_1(sK1,sK0) ) ),
    inference(resolution,[],[f372,f34])).

fof(f34,plain,
    ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f372,plain,(
    ! [X2,X3] :
      ( ~ v2_compts_1(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | v2_compts_1(X2,X3) ) ),
    inference(backward_demodulation,[],[f328,f350])).

fof(f328,plain,(
    ! [X2,X3] :
      ( ~ v2_compts_1(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
      | ~ m1_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | v2_compts_1(X2,X3) ) ),
    inference(resolution,[],[f315,f54])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_compts_1(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_compts_1(X3,X1) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_compts_1(X3,X1)
      | ~ v2_compts_1(X2,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f377,plain,
    ( ~ v2_compts_1(sK1,sK0)
    | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f374,f375])).

fof(f374,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_compts_1(sK1,sK0)
    | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(duplicate_literal_removal,[],[f353])).

fof(f353,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_compts_1(sK1,sK0)
    | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f38,f350])).

fof(f38,plain,
    ( ~ v2_compts_1(sK1,sK0)
    | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
    inference(cnf_transformation,[],[f31])).

fof(f573,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))))
    | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f569,f375])).

fof(f569,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))))
    | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f567,f371])).

fof(f371,plain,(
    ! [X0,X1] :
      ( ~ v2_compts_1(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ) ),
    inference(backward_demodulation,[],[f327,f350])).

fof(f327,plain,(
    ! [X0,X1] :
      ( ~ v2_compts_1(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ) ),
    inference(resolution,[],[f315,f53])).

fof(f567,plain,(
    v2_compts_1(sK1,k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) ),
    inference(subsumption_resolution,[],[f566,f375])).

fof(f566,plain,
    ( v2_compts_1(sK1,k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f563,f55])).

fof(f563,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | v2_compts_1(sK1,k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f516,f450])).

fof(f516,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0))))
      | v2_compts_1(sK1,k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f512,f354])).

fof(f512,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_compts_1(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f508,f375])).

fof(f508,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_pre_topc(X0,sK0)
      | v2_compts_1(sK1,X0) ) ),
    inference(resolution,[],[f506,f216])).

fof(f216,plain,(
    ! [X0,X1] :
      ( ~ v2_compts_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_pre_topc(X1,sK0)
      | v2_compts_1(X0,X1) ) ),
    inference(resolution,[],[f54,f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:10:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.49  % (3608)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.49  % (3608)Refutation not found, incomplete strategy% (3608)------------------------------
% 0.22/0.49  % (3608)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (3600)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (3608)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (3608)Memory used [KB]: 10618
% 0.22/0.51  % (3608)Time elapsed: 0.083 s
% 0.22/0.51  % (3608)------------------------------
% 0.22/0.51  % (3608)------------------------------
% 0.22/0.51  % (3610)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (3611)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (3610)Refutation not found, incomplete strategy% (3610)------------------------------
% 0.22/0.51  % (3610)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (3610)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (3610)Memory used [KB]: 6140
% 0.22/0.51  % (3610)Time elapsed: 0.074 s
% 0.22/0.51  % (3610)------------------------------
% 0.22/0.51  % (3610)------------------------------
% 0.22/0.51  % (3599)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.52  % (3620)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.52  % (3606)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.27/0.52  % (3600)Refutation found. Thanks to Tanya!
% 1.27/0.52  % SZS status Theorem for theBenchmark
% 1.27/0.52  % SZS output start Proof for theBenchmark
% 1.27/0.52  fof(f592,plain,(
% 1.27/0.52    $false),
% 1.27/0.52    inference(subsumption_resolution,[],[f590,f375])).
% 1.27/0.52  fof(f375,plain,(
% 1.27/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.27/0.52    inference(duplicate_literal_removal,[],[f352])).
% 1.27/0.52  fof(f352,plain,(
% 1.27/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.27/0.52    inference(backward_demodulation,[],[f37,f350])).
% 1.27/0.52  fof(f350,plain,(
% 1.27/0.52    u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.27/0.52    inference(equality_resolution,[],[f309])).
% 1.27/0.52  fof(f309,plain,(
% 1.27/0.52    ( ! [X10,X9] : (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X9,X10) | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X9) )),
% 1.27/0.52    inference(subsumption_resolution,[],[f285,f308])).
% 1.27/0.52  fof(f308,plain,(
% 1.27/0.52    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))),
% 1.27/0.52    inference(subsumption_resolution,[],[f307,f33])).
% 1.27/0.52  fof(f33,plain,(
% 1.27/0.52    l1_pre_topc(sK0)),
% 1.27/0.52    inference(cnf_transformation,[],[f31])).
% 1.27/0.52  fof(f31,plain,(
% 1.27/0.52    ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(sK1,sK0)) & ((m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) & v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v2_compts_1(sK1,sK0)))) & l1_pre_topc(sK0)),
% 1.27/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f30,f29])).
% 1.27/0.52  fof(f29,plain,(
% 1.27/0.52    ? [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(X1,sK0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v2_compts_1(X1,sK0)))) & l1_pre_topc(sK0))),
% 1.27/0.52    introduced(choice_axiom,[])).
% 1.27/0.52  fof(f30,plain,(
% 1.27/0.52    ? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(X1,sK0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v2_compts_1(X1,sK0)))) => ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(sK1,sK0)) & ((m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) & v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v2_compts_1(sK1,sK0))))),
% 1.27/0.52    introduced(choice_axiom,[])).
% 1.27/0.52  fof(f28,plain,(
% 1.27/0.52    ? [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)))) & l1_pre_topc(X0))),
% 1.27/0.52    inference(flattening,[],[f27])).
% 1.27/0.52  fof(f27,plain,(
% 1.27/0.52    ? [X0] : (? [X1] : (((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)))) & l1_pre_topc(X0))),
% 1.27/0.52    inference(nnf_transformation,[],[f15])).
% 1.27/0.52  fof(f15,plain,(
% 1.27/0.52    ? [X0] : (? [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <~> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & l1_pre_topc(X0))),
% 1.27/0.52    inference(ennf_transformation,[],[f14])).
% 1.27/0.52  fof(f14,plain,(
% 1.27/0.52    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 1.27/0.52    inference(pure_predicate_removal,[],[f13])).
% 1.27/0.52  fof(f13,plain,(
% 1.27/0.52    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 1.27/0.52    inference(pure_predicate_removal,[],[f12])).
% 1.27/0.52  fof(f12,negated_conjecture,(
% 1.27/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 1.27/0.52    inference(negated_conjecture,[],[f11])).
% 1.27/0.52  fof(f11,conjecture,(
% 1.27/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_compts_1)).
% 1.27/0.52  fof(f307,plain,(
% 1.27/0.52    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) | ~l1_pre_topc(sK0)),
% 1.27/0.52    inference(resolution,[],[f295,f59])).
% 1.27/0.52  fof(f59,plain,(
% 1.27/0.52    ( ! [X1] : (l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1)) )),
% 1.27/0.52    inference(resolution,[],[f48,f41])).
% 1.27/0.52  fof(f41,plain,(
% 1.27/0.52    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f16])).
% 1.27/0.52  fof(f16,plain,(
% 1.27/0.52    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.27/0.52    inference(ennf_transformation,[],[f6])).
% 1.27/0.52  fof(f6,axiom,(
% 1.27/0.52    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 1.27/0.52  fof(f48,plain,(
% 1.27/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | l1_pre_topc(g1_pre_topc(X0,X1))) )),
% 1.27/0.52    inference(cnf_transformation,[],[f23])).
% 1.27/0.52  fof(f23,plain,(
% 1.27/0.52    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.27/0.52    inference(ennf_transformation,[],[f4])).
% 1.27/0.52  fof(f4,axiom,(
% 1.27/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 1.27/0.52  fof(f295,plain,(
% 1.27/0.52    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))),
% 1.27/0.52    inference(superposition,[],[f41,f281])).
% 1.27/0.52  fof(f281,plain,(
% 1.27/0.52    u1_pre_topc(sK0) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.27/0.52    inference(trivial_inequality_removal,[],[f278])).
% 1.27/0.52  fof(f278,plain,(
% 1.27/0.52    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | u1_pre_topc(sK0) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.27/0.52    inference(resolution,[],[f275,f33])).
% 1.27/0.52  fof(f275,plain,(
% 1.27/0.52    ( ! [X1] : (~l1_pre_topc(X1) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = u1_pre_topc(X1)) )),
% 1.27/0.52    inference(resolution,[],[f248,f41])).
% 1.27/0.52  fof(f248,plain,(
% 1.27/0.52    ( ! [X4,X3] : (~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3))) | u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X4 | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X3,X4)) )),
% 1.27/0.52    inference(superposition,[],[f50,f237])).
% 1.27/0.52  fof(f237,plain,(
% 1.27/0.52    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 1.27/0.52    inference(resolution,[],[f63,f33])).
% 1.27/0.52  fof(f63,plain,(
% 1.27/0.52    ( ! [X1] : (~l1_pre_topc(X1) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) )),
% 1.27/0.52    inference(subsumption_resolution,[],[f61,f59])).
% 1.27/0.52  fof(f61,plain,(
% 1.27/0.52    ( ! [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1)) )),
% 1.27/0.52    inference(resolution,[],[f42,f57])).
% 1.27/0.52  fof(f57,plain,(
% 1.27/0.52    ( ! [X1] : (v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1)) )),
% 1.27/0.52    inference(resolution,[],[f47,f41])).
% 1.27/0.52  fof(f47,plain,(
% 1.27/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | v1_pre_topc(g1_pre_topc(X0,X1))) )),
% 1.27/0.52    inference(cnf_transformation,[],[f23])).
% 1.27/0.52  fof(f42,plain,(
% 1.27/0.52    ( ! [X0] : (~v1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~l1_pre_topc(X0)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f18])).
% 1.27/0.52  fof(f18,plain,(
% 1.27/0.52    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 1.27/0.52    inference(flattening,[],[f17])).
% 1.27/0.52  fof(f17,plain,(
% 1.27/0.52    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 1.27/0.52    inference(ennf_transformation,[],[f3])).
% 1.27/0.52  fof(f3,axiom,(
% 1.27/0.52    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 1.27/0.52  fof(f50,plain,(
% 1.27/0.52    ( ! [X2,X0,X3,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X1 = X3 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.27/0.52    inference(cnf_transformation,[],[f24])).
% 1.27/0.52  fof(f24,plain,(
% 1.27/0.52    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.27/0.52    inference(ennf_transformation,[],[f7])).
% 1.27/0.52  fof(f7,axiom,(
% 1.27/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).
% 1.27/0.52  fof(f285,plain,(
% 1.27/0.52    ( ! [X10,X9] : (~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X9,X10) | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X9) )),
% 1.27/0.52    inference(backward_demodulation,[],[f251,f281])).
% 1.27/0.52  fof(f251,plain,(
% 1.27/0.52    ( ! [X10,X9] : (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X9,X10) | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X9 | ~m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))) )),
% 1.27/0.52    inference(superposition,[],[f49,f237])).
% 1.27/0.52  fof(f49,plain,(
% 1.27/0.52    ( ! [X2,X0,X3,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X0 = X2 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.27/0.52    inference(cnf_transformation,[],[f24])).
% 1.27/0.52  fof(f37,plain,(
% 1.27/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.27/0.52    inference(cnf_transformation,[],[f31])).
% 1.27/0.52  fof(f590,plain,(
% 1.27/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.27/0.52    inference(resolution,[],[f576,f373])).
% 1.27/0.52  fof(f373,plain,(
% 1.27/0.52    ( ! [X4] : (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X4),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.27/0.52    inference(backward_demodulation,[],[f341,f350])).
% 1.27/0.52  fof(f341,plain,(
% 1.27/0.52    ( ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X4),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) )),
% 1.27/0.52    inference(forward_demodulation,[],[f340,f282])).
% 1.27/0.52  fof(f282,plain,(
% 1.27/0.52    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(sK0))),
% 1.27/0.52    inference(backward_demodulation,[],[f237,f281])).
% 1.27/0.52  fof(f340,plain,(
% 1.27/0.52    ( ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(sK0))))) | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X4),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) )),
% 1.27/0.52    inference(forward_demodulation,[],[f339,f281])).
% 1.27/0.52  fof(f339,plain,(
% 1.27/0.52    ( ! [X4] : (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X4),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))))) )),
% 1.27/0.52    inference(forward_demodulation,[],[f338,f282])).
% 1.27/0.52  fof(f338,plain,(
% 1.27/0.52    ( ! [X4] : (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(sK0)),X4),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))))) )),
% 1.27/0.52    inference(forward_demodulation,[],[f330,f281])).
% 1.27/0.52  fof(f330,plain,(
% 1.27/0.52    ( ! [X4] : (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),X4),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))))) )),
% 1.27/0.52    inference(resolution,[],[f315,f68])).
% 1.27/0.52  fof(f68,plain,(
% 1.27/0.52    ( ! [X0,X1] : (~l1_pre_topc(X1) | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) )),
% 1.27/0.52    inference(subsumption_resolution,[],[f67,f59])).
% 1.27/0.52  fof(f67,plain,(
% 1.27/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0),X1) | ~l1_pre_topc(X1)) )),
% 1.27/0.52    inference(resolution,[],[f52,f46])).
% 1.27/0.52  fof(f46,plain,(
% 1.27/0.52    ( ! [X0,X1] : (~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f22])).
% 1.27/0.52  fof(f22,plain,(
% 1.27/0.52    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 1.27/0.52    inference(ennf_transformation,[],[f9])).
% 1.27/0.52  fof(f9,axiom,(
% 1.27/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).
% 1.27/0.52  fof(f52,plain,(
% 1.27/0.52    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f26])).
% 1.27/0.52  fof(f26,plain,(
% 1.27/0.52    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.27/0.52    inference(flattening,[],[f25])).
% 1.27/0.52  fof(f25,plain,(
% 1.27/0.52    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.27/0.52    inference(ennf_transformation,[],[f5])).
% 1.27/0.52  fof(f5,axiom,(
% 1.27/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).
% 1.27/0.52  fof(f315,plain,(
% 1.27/0.52    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.27/0.52    inference(forward_demodulation,[],[f312,f282])).
% 1.27/0.52  fof(f312,plain,(
% 1.27/0.52    l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(sK0)))),
% 1.27/0.52    inference(resolution,[],[f308,f48])).
% 1.27/0.52  fof(f576,plain,(
% 1.27/0.52    ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.27/0.52    inference(subsumption_resolution,[],[f575,f55])).
% 1.27/0.52  fof(f55,plain,(
% 1.27/0.52    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.27/0.52    inference(forward_demodulation,[],[f40,f39])).
% 1.27/0.52  fof(f39,plain,(
% 1.27/0.52    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.27/0.52    inference(cnf_transformation,[],[f1])).
% 1.27/0.52  fof(f1,axiom,(
% 1.27/0.52    ! [X0] : k2_subset_1(X0) = X0),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.27/0.52  fof(f40,plain,(
% 1.27/0.52    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.27/0.52    inference(cnf_transformation,[],[f2])).
% 1.27/0.52  fof(f2,axiom,(
% 1.27/0.52    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.27/0.52  fof(f575,plain,(
% 1.27/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.27/0.52    inference(forward_demodulation,[],[f574,f450])).
% 1.27/0.52  fof(f450,plain,(
% 1.27/0.52    sK1 = u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))),
% 1.27/0.52    inference(resolution,[],[f417,f375])).
% 1.27/0.52  fof(f417,plain,(
% 1.27/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)) = X0) )),
% 1.27/0.52    inference(subsumption_resolution,[],[f409,f315])).
% 1.27/0.52  fof(f409,plain,(
% 1.27/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)) = X0 | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) )),
% 1.27/0.52    inference(superposition,[],[f45,f350])).
% 1.27/0.52  fof(f45,plain,(
% 1.27/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~l1_pre_topc(X0)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f21])).
% 1.27/0.52  fof(f21,plain,(
% 1.27/0.52    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.27/0.52    inference(ennf_transformation,[],[f8])).
% 1.27/0.52  fof(f8,axiom,(
% 1.27/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).
% 1.27/0.52  fof(f574,plain,(
% 1.27/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)))) | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.27/0.52    inference(subsumption_resolution,[],[f573,f507])).
% 1.27/0.52  fof(f507,plain,(
% 1.27/0.52    ~v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.27/0.52    inference(subsumption_resolution,[],[f377,f506])).
% 1.27/0.52  fof(f506,plain,(
% 1.27/0.52    v2_compts_1(sK1,sK0)),
% 1.27/0.52    inference(subsumption_resolution,[],[f505,f375])).
% 1.27/0.52  fof(f505,plain,(
% 1.27/0.52    v2_compts_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.27/0.52    inference(resolution,[],[f502,f354])).
% 1.27/0.52  fof(f354,plain,(
% 1.27/0.52    ( ! [X0] : (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.27/0.52    inference(backward_demodulation,[],[f103,f350])).
% 1.27/0.52  fof(f103,plain,(
% 1.27/0.52    ( ! [X0] : (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) )),
% 1.27/0.52    inference(resolution,[],[f68,f33])).
% 1.27/0.52  fof(f502,plain,(
% 1.27/0.52    ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0) | v2_compts_1(sK1,sK0)),
% 1.27/0.52    inference(subsumption_resolution,[],[f501,f55])).
% 1.27/0.52  fof(f501,plain,(
% 1.27/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | v2_compts_1(sK1,sK0) | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0)),
% 1.27/0.52    inference(forward_demodulation,[],[f500,f450])).
% 1.27/0.52  fof(f500,plain,(
% 1.27/0.52    v2_compts_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)))) | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0)),
% 1.27/0.52    inference(duplicate_literal_removal,[],[f497])).
% 1.27/0.52  fof(f497,plain,(
% 1.27/0.52    v2_compts_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)))) | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0) | v2_compts_1(sK1,sK0)),
% 1.27/0.52    inference(resolution,[],[f496,f389])).
% 1.27/0.52  fof(f389,plain,(
% 1.27/0.52    ( ! [X0] : (~v2_compts_1(sK1,X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X0,sK0) | v2_compts_1(sK1,sK0)) )),
% 1.27/0.52    inference(resolution,[],[f375,f134])).
% 1.27/0.52  fof(f134,plain,(
% 1.27/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_compts_1(X0,X1) | ~m1_pre_topc(X1,sK0) | v2_compts_1(X0,sK0)) )),
% 1.27/0.52    inference(resolution,[],[f53,f33])).
% 1.27/0.52  fof(f53,plain,(
% 1.27/0.52    ( ! [X0,X3,X1] : (~l1_pre_topc(X0) | ~v2_compts_1(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_compts_1(X3,X0)) )),
% 1.27/0.52    inference(equality_resolution,[],[f44])).
% 1.27/0.52  fof(f44,plain,(
% 1.27/0.52    ( ! [X2,X0,X3,X1] : (v2_compts_1(X2,X0) | ~v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f32])).
% 1.27/0.52  fof(f32,plain,(
% 1.27/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v2_compts_1(X2,X0) | ~v2_compts_1(X3,X1)) & (v2_compts_1(X3,X1) | ~v2_compts_1(X2,X0))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.27/0.52    inference(nnf_transformation,[],[f20])).
% 1.27/0.52  fof(f20,plain,(
% 1.27/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v2_compts_1(X2,X0) <=> v2_compts_1(X3,X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.27/0.52    inference(flattening,[],[f19])).
% 1.27/0.52  fof(f19,plain,(
% 1.27/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v2_compts_1(X2,X0) <=> v2_compts_1(X3,X1)) | X2 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.27/0.52    inference(ennf_transformation,[],[f10])).
% 1.27/0.52  fof(f10,axiom,(
% 1.27/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (X2 = X3 => (v2_compts_1(X2,X0) <=> v2_compts_1(X3,X1)))))))),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_compts_1)).
% 1.27/0.52  fof(f496,plain,(
% 1.27/0.52    v2_compts_1(sK1,k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | v2_compts_1(sK1,sK0)),
% 1.27/0.52    inference(subsumption_resolution,[],[f495,f375])).
% 1.27/0.52  fof(f495,plain,(
% 1.27/0.52    v2_compts_1(sK1,k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | v2_compts_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.27/0.52    inference(subsumption_resolution,[],[f492,f55])).
% 1.27/0.52  fof(f492,plain,(
% 1.27/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | v2_compts_1(sK1,k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | v2_compts_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.27/0.52    inference(superposition,[],[f487,f450])).
% 1.27/0.52  fof(f487,plain,(
% 1.27/0.52    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)))) | v2_compts_1(sK1,k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)) | v2_compts_1(sK1,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.27/0.52    inference(resolution,[],[f486,f373])).
% 1.27/0.52  fof(f486,plain,(
% 1.27/0.52    ( ! [X0] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | v2_compts_1(sK1,X0) | v2_compts_1(sK1,sK0)) )),
% 1.27/0.52    inference(subsumption_resolution,[],[f485,f375])).
% 1.27/0.52  fof(f485,plain,(
% 1.27/0.52    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v2_compts_1(sK1,X0) | v2_compts_1(sK1,sK0)) )),
% 1.27/0.52    inference(resolution,[],[f372,f34])).
% 1.27/0.52  fof(f34,plain,(
% 1.27/0.52    v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v2_compts_1(sK1,sK0)),
% 1.27/0.52    inference(cnf_transformation,[],[f31])).
% 1.27/0.52  fof(f372,plain,(
% 1.27/0.52    ( ! [X2,X3] : (~v2_compts_1(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v2_compts_1(X2,X3)) )),
% 1.27/0.52    inference(backward_demodulation,[],[f328,f350])).
% 1.27/0.52  fof(f328,plain,(
% 1.27/0.52    ( ! [X2,X3] : (~v2_compts_1(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~m1_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v2_compts_1(X2,X3)) )),
% 1.27/0.52    inference(resolution,[],[f315,f54])).
% 1.27/0.52  fof(f54,plain,(
% 1.27/0.52    ( ! [X0,X3,X1] : (~l1_pre_topc(X0) | ~v2_compts_1(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_compts_1(X3,X1)) )),
% 1.27/0.52    inference(equality_resolution,[],[f43])).
% 1.27/0.52  fof(f43,plain,(
% 1.27/0.52    ( ! [X2,X0,X3,X1] : (v2_compts_1(X3,X1) | ~v2_compts_1(X2,X0) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f32])).
% 1.27/0.52  fof(f377,plain,(
% 1.27/0.52    ~v2_compts_1(sK1,sK0) | ~v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.27/0.52    inference(subsumption_resolution,[],[f374,f375])).
% 1.27/0.52  fof(f374,plain,(
% 1.27/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(sK1,sK0) | ~v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.27/0.52    inference(duplicate_literal_removal,[],[f353])).
% 1.27/0.52  fof(f353,plain,(
% 1.27/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(sK1,sK0) | ~v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.27/0.52    inference(backward_demodulation,[],[f38,f350])).
% 1.27/0.52  fof(f38,plain,(
% 1.27/0.52    ~v2_compts_1(sK1,sK0) | ~v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))),
% 1.27/0.52    inference(cnf_transformation,[],[f31])).
% 1.27/0.52  fof(f573,plain,(
% 1.27/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)))) | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.27/0.52    inference(subsumption_resolution,[],[f569,f375])).
% 1.27/0.52  fof(f569,plain,(
% 1.27/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)))) | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.27/0.52    inference(resolution,[],[f567,f371])).
% 1.27/0.52  fof(f371,plain,(
% 1.27/0.52    ( ! [X0,X1] : (~v2_compts_1(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) )),
% 1.27/0.52    inference(backward_demodulation,[],[f327,f350])).
% 1.27/0.52  fof(f327,plain,(
% 1.27/0.52    ( ! [X0,X1] : (~v2_compts_1(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) )),
% 1.27/0.52    inference(resolution,[],[f315,f53])).
% 1.27/0.52  fof(f567,plain,(
% 1.27/0.52    v2_compts_1(sK1,k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))),
% 1.27/0.52    inference(subsumption_resolution,[],[f566,f375])).
% 1.27/0.52  fof(f566,plain,(
% 1.27/0.52    v2_compts_1(sK1,k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.27/0.52    inference(subsumption_resolution,[],[f563,f55])).
% 1.27/0.52  fof(f563,plain,(
% 1.27/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | v2_compts_1(sK1,k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.27/0.52    inference(superposition,[],[f516,f450])).
% 1.27/0.52  fof(f516,plain,(
% 1.27/0.52    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)))) | v2_compts_1(sK1,k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.27/0.52    inference(resolution,[],[f512,f354])).
% 1.27/0.52  fof(f512,plain,(
% 1.27/0.52    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | v2_compts_1(sK1,X0)) )),
% 1.27/0.52    inference(subsumption_resolution,[],[f508,f375])).
% 1.27/0.52  fof(f508,plain,(
% 1.27/0.52    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_pre_topc(X0,sK0) | v2_compts_1(sK1,X0)) )),
% 1.27/0.52    inference(resolution,[],[f506,f216])).
% 1.27/0.52  fof(f216,plain,(
% 1.27/0.52    ( ! [X0,X1] : (~v2_compts_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_pre_topc(X1,sK0) | v2_compts_1(X0,X1)) )),
% 1.27/0.52    inference(resolution,[],[f54,f33])).
% 1.27/0.52  % SZS output end Proof for theBenchmark
% 1.27/0.52  % (3600)------------------------------
% 1.27/0.52  % (3600)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.52  % (3600)Termination reason: Refutation
% 1.27/0.52  
% 1.27/0.52  % (3600)Memory used [KB]: 6652
% 1.27/0.52  % (3600)Time elapsed: 0.103 s
% 1.27/0.52  % (3600)------------------------------
% 1.27/0.52  % (3600)------------------------------
% 1.27/0.52  % (3609)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.27/0.52  % (3594)Success in time 0.161 s
%------------------------------------------------------------------------------
