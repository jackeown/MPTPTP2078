%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:53 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :  139 (77403 expanded)
%              Number of leaves         :   11 (18669 expanded)
%              Depth                    :   63
%              Number of atoms          :  500 (446147 expanded)
%              Number of equality atoms :   19 (15257 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f351,plain,(
    $false ),
    inference(subsumption_resolution,[],[f350,f126])).

fof(f126,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(duplicate_literal_removal,[],[f109])).

fof(f109,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(backward_demodulation,[],[f40,f107])).

fof(f107,plain,(
    u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X6,X7] :
      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X6,X7)
      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X6 ) ),
    inference(subsumption_resolution,[],[f85,f60])).

fof(f60,plain,(
    m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ),
    inference(resolution,[],[f58,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f58,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f57,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f57,plain,(
    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f51,f36])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
      | ~ v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ v1_tops_2(sK1,sK0) )
    & ( ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
        & v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
      | ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        & v1_tops_2(sK1,sK0) ) )
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
              | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
              | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              | ~ v1_tops_2(X1,X0) )
            & ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
                & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
              | ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                & v1_tops_2(X1,X0) ) ) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
            | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
            | ~ v1_tops_2(X1,sK0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
              & v1_tops_2(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
              & v1_tops_2(X1,sK0) ) ) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
          | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
          | ~ v1_tops_2(X1,sK0) )
        & ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
            & v1_tops_2(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
          | ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
            & v1_tops_2(X1,sK0) ) ) )
   => ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
        | ~ v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ v1_tops_2(sK1,sK0) )
      & ( ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
          & v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
        | ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
          & v1_tops_2(sK1,sK0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            | ~ v1_tops_2(X1,X0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
              & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              & v1_tops_2(X1,X0) ) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            | ~ v1_tops_2(X1,X0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
              & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              & v1_tops_2(X1,X0) ) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            & v1_tops_2(X1,X0) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            & v1_tops_2(X1,X0) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              & v1_tops_2(X1,X0) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
              & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              & v1_tops_2(X1,X0) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
              & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            & v1_tops_2(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_compts_1)).

fof(f85,plain,(
    ! [X6,X7] :
      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X6,X7)
      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X6
      | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ) ),
    inference(superposition,[],[f42,f62])).

fof(f62,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    inference(subsumption_resolution,[],[f61,f58])).

fof(f61,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f50,f59])).

fof(f59,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f57,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f50,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f40,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f28])).

fof(f350,plain,(
    ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f349,f107])).

fof(f349,plain,(
    ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ),
    inference(subsumption_resolution,[],[f348,f58])).

fof(f348,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f345,f285])).

fof(f285,plain,(
    ~ v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f127,f283])).

fof(f283,plain,(
    v1_tops_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f282,f36])).

fof(f282,plain,
    ( v1_tops_2(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f280,f126])).

fof(f280,plain,
    ( v1_tops_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f271,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(sK2(X0,X1),X0)
      | v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ( ~ v3_pre_topc(sK2(X0,X1),X0)
                & r2_hidden(sK2(X0,X1),X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK2(X0,X1),X0)
        & r2_hidden(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v3_pre_topc(X2,X0)
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_2)).

fof(f271,plain,(
    v3_pre_topc(sK2(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f269,f251])).

fof(f251,plain,(
    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f249,f126])).

fof(f249,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(X1))
      | m1_subset_1(sK2(sK0,sK1),X1) ) ),
    inference(resolution,[],[f247,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f247,plain,(
    r2_hidden(sK2(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f246,f126])).

fof(f246,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | r2_hidden(sK2(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f245,f107])).

fof(f245,plain,
    ( r2_hidden(sK2(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ),
    inference(subsumption_resolution,[],[f244,f142])).

fof(f142,plain,
    ( ~ v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | r2_hidden(sK2(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f141,f36])).

fof(f141,plain,
    ( ~ v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | r2_hidden(sK2(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f138,f126])).

fof(f138,plain,
    ( ~ v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | r2_hidden(sK2(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f127,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | r2_hidden(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f244,plain,
    ( r2_hidden(sK2(sK0,sK1),sK1)
    | v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ),
    inference(subsumption_resolution,[],[f241,f58])).

fof(f241,plain,
    ( r2_hidden(sK2(sK0,sK1),sK1)
    | v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f233,f55])).

fof(f233,plain,
    ( v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | r2_hidden(sK2(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f174,f232])).

fof(f232,plain,
    ( v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0)
    | r2_hidden(sK2(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f231,f144])).

fof(f144,plain,
    ( v1_tops_2(sK1,sK0)
    | r2_hidden(sK2(sK0,sK1),sK1) ),
    inference(resolution,[],[f142,f37])).

fof(f37,plain,
    ( v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f231,plain,
    ( ~ v1_tops_2(sK1,sK0)
    | v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0)
    | r2_hidden(sK2(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f228,f36])).

fof(f228,plain,
    ( ~ v1_tops_2(sK1,sK0)
    | v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | r2_hidden(sK2(sK0,sK1),sK1) ),
    inference(resolution,[],[f221,f126])).

fof(f221,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_tops_2(sK1,X0)
      | v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0)
      | ~ l1_pre_topc(X0)
      | r2_hidden(sK2(sK0,sK1),sK1) ) ),
    inference(subsumption_resolution,[],[f220,f171])).

fof(f171,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
      | r2_hidden(sK2(sK0,sK1),sK1)
      | m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0) ) ),
    inference(resolution,[],[f153,f56])).

fof(f153,plain,
    ( r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK1)
    | r2_hidden(sK2(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f152,f126])).

fof(f152,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | r2_hidden(sK2(sK0,sK1),sK1)
    | r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK1) ),
    inference(forward_demodulation,[],[f151,f107])).

fof(f151,plain,
    ( r2_hidden(sK2(sK0,sK1),sK1)
    | r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ),
    inference(subsumption_resolution,[],[f146,f58])).

fof(f146,plain,
    ( r2_hidden(sK2(sK0,sK1),sK1)
    | r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f142,f54])).

fof(f220,plain,(
    ! [X0] :
      ( v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0)
      | ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_2(sK1,X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | r2_hidden(sK2(sK0,sK1),sK1) ) ),
    inference(resolution,[],[f52,f153])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f174,plain,
    ( r2_hidden(sK2(sK0,sK1),sK1)
    | v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0) ),
    inference(subsumption_resolution,[],[f173,f35])).

fof(f35,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f173,plain,
    ( r2_hidden(sK2(sK0,sK1),sK1)
    | v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f172,f36])).

fof(f172,plain,
    ( r2_hidden(sK2(sK0,sK1),sK1)
    | v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f150,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v3_pre_topc(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v3_pre_topc(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v3_pre_topc(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v3_pre_topc(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_pre_topc)).

fof(f150,plain,
    ( m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK2(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f149,f126])).

fof(f149,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK2(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f148,f107])).

fof(f148,plain,
    ( m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK2(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ),
    inference(forward_demodulation,[],[f147,f107])).

fof(f147,plain,
    ( r2_hidden(sK2(sK0,sK1),sK1)
    | m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ),
    inference(subsumption_resolution,[],[f145,f58])).

fof(f145,plain,
    ( r2_hidden(sK2(sK0,sK1),sK1)
    | m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f142,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f269,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK2(sK0,sK1),sK0) ),
    inference(resolution,[],[f261,f224])).

fof(f224,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(X0,sK0) ) ),
    inference(forward_demodulation,[],[f223,f107])).

fof(f223,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
      | ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | v3_pre_topc(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f222,f36])).

fof(f222,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
      | ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ l1_pre_topc(sK0)
      | v3_pre_topc(X0,sK0) ) ),
    inference(resolution,[],[f48,f35])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f261,plain,(
    v3_pre_topc(sK2(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(global_subsumption,[],[f37,f254,f258,f260])).

fof(f260,plain,
    ( ~ v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v3_pre_topc(sK2(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f259,f58])).

fof(f259,plain,
    ( ~ v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v3_pre_topc(sK2(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f256,f126])).

fof(f256,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v3_pre_topc(sK2(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(superposition,[],[f250,f107])).

fof(f250,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_tops_2(sK1,X0)
      | v3_pre_topc(sK2(sK0,sK1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f248,f249])).

fof(f248,plain,(
    ! [X0] :
      ( v3_pre_topc(sK2(sK0,sK1),X0)
      | ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_2(sK1,X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f247,f52])).

fof(f258,plain,
    ( ~ v1_tops_2(sK1,sK0)
    | v3_pre_topc(sK2(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f255,f36])).

fof(f255,plain,
    ( ~ v1_tops_2(sK1,sK0)
    | v3_pre_topc(sK2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f250,f126])).

fof(f254,plain,
    ( ~ v3_pre_topc(sK2(sK0,sK1),sK0)
    | v3_pre_topc(sK2(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f253,f35])).

fof(f253,plain,
    ( v3_pre_topc(sK2(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v3_pre_topc(sK2(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f252,f36])).

fof(f252,plain,
    ( v3_pre_topc(sK2(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v3_pre_topc(sK2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f251,f46])).

fof(f127,plain,
    ( ~ v1_tops_2(sK1,sK0)
    | ~ v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f125,f126])).

fof(f125,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v1_tops_2(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f110])).

fof(f110,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v1_tops_2(sK1,sK0) ),
    inference(backward_demodulation,[],[f41,f107])).

fof(f41,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f345,plain,
    ( v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f336,f55])).

fof(f336,plain,(
    v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f306,f335])).

fof(f335,plain,(
    v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0) ),
    inference(subsumption_resolution,[],[f334,f36])).

fof(f334,plain,
    ( v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f331,f283])).

fof(f331,plain,
    ( ~ v1_tops_2(sK1,sK0)
    | v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f303,f126])).

fof(f303,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_tops_2(sK1,X0)
      | v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f301,f302])).

fof(f302,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(X1))
      | m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X1) ) ),
    inference(resolution,[],[f300,f56])).

fof(f300,plain,(
    r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK1) ),
    inference(subsumption_resolution,[],[f299,f126])).

fof(f299,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK1) ),
    inference(forward_demodulation,[],[f298,f107])).

fof(f298,plain,
    ( r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ),
    inference(subsumption_resolution,[],[f293,f58])).

fof(f293,plain,
    ( r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f285,f54])).

fof(f301,plain,(
    ! [X0] :
      ( v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0)
      | ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_2(sK1,X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f300,f52])).

fof(f306,plain,
    ( v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0) ),
    inference(subsumption_resolution,[],[f305,f35])).

fof(f305,plain,
    ( v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f304,f36])).

fof(f304,plain,
    ( v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f297,f46])).

fof(f297,plain,(
    m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f296,f126])).

fof(f296,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f295,f107])).

fof(f295,plain,
    ( m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ),
    inference(forward_demodulation,[],[f294,f107])).

fof(f294,plain,
    ( m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ),
    inference(subsumption_resolution,[],[f292,f58])).

fof(f292,plain,
    ( m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f285,f53])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:52:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (28461)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (28470)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.51  % (28478)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (28470)Refutation not found, incomplete strategy% (28470)------------------------------
% 0.21/0.52  % (28470)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (28456)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (28463)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (28470)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (28470)Memory used [KB]: 10746
% 0.21/0.53  % (28470)Time elapsed: 0.110 s
% 0.21/0.53  % (28470)------------------------------
% 0.21/0.53  % (28470)------------------------------
% 0.21/0.53  % (28458)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.30/0.53  % (28455)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.30/0.53  % (28459)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.30/0.54  % (28451)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.30/0.54  % (28475)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.30/0.54  % (28467)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.30/0.54  % (28460)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.30/0.54  % (28455)Refutation found. Thanks to Tanya!
% 1.30/0.54  % SZS status Theorem for theBenchmark
% 1.30/0.54  % (28450)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.30/0.54  % (28471)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.30/0.54  % (28467)Refutation not found, incomplete strategy% (28467)------------------------------
% 1.30/0.54  % (28467)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (28454)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.42/0.55  % (28467)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (28467)Memory used [KB]: 10618
% 1.42/0.55  % (28467)Time elapsed: 0.129 s
% 1.42/0.55  % (28467)------------------------------
% 1.42/0.55  % (28467)------------------------------
% 1.42/0.55  % (28468)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.42/0.55  % (28452)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.42/0.55  % (28474)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.42/0.55  % (28479)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.42/0.55  % (28457)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.42/0.55  % (28473)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.42/0.56  % SZS output start Proof for theBenchmark
% 1.42/0.56  fof(f351,plain,(
% 1.42/0.56    $false),
% 1.42/0.56    inference(subsumption_resolution,[],[f350,f126])).
% 1.42/0.56  fof(f126,plain,(
% 1.42/0.56    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.42/0.56    inference(duplicate_literal_removal,[],[f109])).
% 1.42/0.56  fof(f109,plain,(
% 1.42/0.56    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.42/0.56    inference(backward_demodulation,[],[f40,f107])).
% 1.42/0.56  fof(f107,plain,(
% 1.42/0.56    u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.42/0.56    inference(equality_resolution,[],[f87])).
% 1.42/0.56  fof(f87,plain,(
% 1.42/0.56    ( ! [X6,X7] : (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X6,X7) | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X6) )),
% 1.42/0.56    inference(subsumption_resolution,[],[f85,f60])).
% 1.42/0.56  fof(f60,plain,(
% 1.42/0.56    m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))),
% 1.42/0.56    inference(resolution,[],[f58,f51])).
% 1.42/0.56  fof(f51,plain,(
% 1.42/0.56    ( ! [X0] : (~l1_pre_topc(X0) | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.42/0.56    inference(cnf_transformation,[],[f19])).
% 1.42/0.56  fof(f19,plain,(
% 1.42/0.56    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.42/0.56    inference(ennf_transformation,[],[f4])).
% 1.42/0.56  fof(f4,axiom,(
% 1.42/0.56    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 1.42/0.56  fof(f58,plain,(
% 1.42/0.56    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.42/0.56    inference(resolution,[],[f57,f45])).
% 1.42/0.56  fof(f45,plain,(
% 1.42/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | l1_pre_topc(g1_pre_topc(X0,X1))) )),
% 1.42/0.56    inference(cnf_transformation,[],[f14])).
% 1.42/0.56  fof(f14,plain,(
% 1.42/0.56    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.42/0.56    inference(ennf_transformation,[],[f3])).
% 1.42/0.56  fof(f3,axiom,(
% 1.42/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 1.42/0.56  fof(f57,plain,(
% 1.42/0.56    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.42/0.56    inference(resolution,[],[f51,f36])).
% 1.42/0.56  fof(f36,plain,(
% 1.42/0.56    l1_pre_topc(sK0)),
% 1.42/0.56    inference(cnf_transformation,[],[f28])).
% 1.42/0.56  fof(f28,plain,(
% 1.42/0.56    ((~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) | ~v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v1_tops_2(sK1,sK0)) & ((m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) & v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) & v1_tops_2(sK1,sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.42/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f27,f26])).
% 1.42/0.56  fof(f26,plain,(
% 1.42/0.56    ? [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) | ~v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0)) & ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) | ~v1_tops_2(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v1_tops_2(X1,sK0)) & ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) & v1_tops_2(X1,sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.42/0.56    introduced(choice_axiom,[])).
% 1.42/0.56  fof(f27,plain,(
% 1.42/0.56    ? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) | ~v1_tops_2(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v1_tops_2(X1,sK0)) & ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) & v1_tops_2(X1,sK0)))) => ((~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) | ~v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v1_tops_2(sK1,sK0)) & ((m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) & v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) & v1_tops_2(sK1,sK0))))),
% 1.42/0.56    introduced(choice_axiom,[])).
% 1.42/0.56  fof(f25,plain,(
% 1.42/0.56    ? [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) | ~v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0)) & ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.42/0.56    inference(flattening,[],[f24])).
% 1.42/0.56  fof(f24,plain,(
% 1.42/0.56    ? [X0] : (? [X1] : (((~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) | ~v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) & ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.42/0.56    inference(nnf_transformation,[],[f12])).
% 1.42/0.56  fof(f12,plain,(
% 1.42/0.56    ? [X0] : (? [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)) <~> (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.42/0.56    inference(flattening,[],[f11])).
% 1.42/0.56  fof(f11,plain,(
% 1.42/0.56    ? [X0] : (? [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)) <~> (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.42/0.56    inference(ennf_transformation,[],[f10])).
% 1.42/0.56  fof(f10,plain,(
% 1.42/0.56    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 1.42/0.56    inference(pure_predicate_removal,[],[f9])).
% 1.42/0.56  fof(f9,negated_conjecture,(
% 1.42/0.56    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 1.42/0.56    inference(negated_conjecture,[],[f8])).
% 1.42/0.56  fof(f8,conjecture,(
% 1.42/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_compts_1)).
% 1.42/0.56  fof(f85,plain,(
% 1.42/0.56    ( ! [X6,X7] : (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X6,X7) | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X6 | ~m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))) )),
% 1.42/0.56    inference(superposition,[],[f42,f62])).
% 1.42/0.56  fof(f62,plain,(
% 1.42/0.56    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 1.42/0.56    inference(subsumption_resolution,[],[f61,f58])).
% 1.42/0.56  fof(f61,plain,(
% 1.42/0.56    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.42/0.56    inference(resolution,[],[f50,f59])).
% 1.42/0.56  fof(f59,plain,(
% 1.42/0.56    v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.42/0.56    inference(resolution,[],[f57,f44])).
% 1.42/0.56  fof(f44,plain,(
% 1.42/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | v1_pre_topc(g1_pre_topc(X0,X1))) )),
% 1.42/0.56    inference(cnf_transformation,[],[f14])).
% 1.42/0.56  fof(f50,plain,(
% 1.42/0.56    ( ! [X0] : (~v1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~l1_pre_topc(X0)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f18])).
% 1.42/0.56  fof(f18,plain,(
% 1.42/0.56    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 1.42/0.56    inference(flattening,[],[f17])).
% 1.42/0.56  fof(f17,plain,(
% 1.42/0.56    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 1.42/0.56    inference(ennf_transformation,[],[f2])).
% 1.42/0.56  fof(f2,axiom,(
% 1.42/0.56    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 1.42/0.56  fof(f42,plain,(
% 1.42/0.56    ( ! [X2,X0,X3,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X0 = X2 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.42/0.56    inference(cnf_transformation,[],[f13])).
% 1.42/0.56  fof(f13,plain,(
% 1.42/0.56    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.42/0.56    inference(ennf_transformation,[],[f5])).
% 1.42/0.56  fof(f5,axiom,(
% 1.42/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).
% 1.42/0.56  fof(f40,plain,(
% 1.42/0.56    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.42/0.56    inference(cnf_transformation,[],[f28])).
% 1.42/0.56  fof(f350,plain,(
% 1.42/0.56    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.42/0.56    inference(forward_demodulation,[],[f349,f107])).
% 1.42/0.56  fof(f349,plain,(
% 1.42/0.56    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))),
% 1.42/0.56    inference(subsumption_resolution,[],[f348,f58])).
% 1.42/0.56  fof(f348,plain,(
% 1.42/0.56    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.42/0.56    inference(subsumption_resolution,[],[f345,f285])).
% 1.42/0.56  fof(f285,plain,(
% 1.42/0.56    ~v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.42/0.56    inference(subsumption_resolution,[],[f127,f283])).
% 1.42/0.56  fof(f283,plain,(
% 1.42/0.56    v1_tops_2(sK1,sK0)),
% 1.42/0.56    inference(subsumption_resolution,[],[f282,f36])).
% 1.42/0.56  fof(f282,plain,(
% 1.42/0.56    v1_tops_2(sK1,sK0) | ~l1_pre_topc(sK0)),
% 1.42/0.56    inference(subsumption_resolution,[],[f280,f126])).
% 1.42/0.56  fof(f280,plain,(
% 1.42/0.56    v1_tops_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)),
% 1.42/0.56    inference(resolution,[],[f271,f55])).
% 1.42/0.56  fof(f55,plain,(
% 1.42/0.56    ( ! [X0,X1] : (~v3_pre_topc(sK2(X0,X1),X0) | v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f34])).
% 1.42/0.56  fof(f34,plain,(
% 1.42/0.56    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | (~v3_pre_topc(sK2(X0,X1),X0) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 1.42/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).
% 1.42/0.56  fof(f33,plain,(
% 1.42/0.56    ! [X1,X0] : (? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK2(X0,X1),X0) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.42/0.56    introduced(choice_axiom,[])).
% 1.42/0.56  fof(f32,plain,(
% 1.42/0.56    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 1.42/0.56    inference(rectify,[],[f31])).
% 1.42/0.56  fof(f31,plain,(
% 1.42/0.56    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 1.42/0.56    inference(nnf_transformation,[],[f21])).
% 1.42/0.56  fof(f21,plain,(
% 1.42/0.56    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 1.42/0.56    inference(flattening,[],[f20])).
% 1.42/0.56  fof(f20,plain,(
% 1.42/0.56    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 1.42/0.56    inference(ennf_transformation,[],[f7])).
% 1.42/0.56  fof(f7,axiom,(
% 1.42/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,X1) => v3_pre_topc(X2,X0))))))),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_2)).
% 1.42/0.56  fof(f271,plain,(
% 1.42/0.56    v3_pre_topc(sK2(sK0,sK1),sK0)),
% 1.42/0.56    inference(subsumption_resolution,[],[f269,f251])).
% 1.42/0.56  fof(f251,plain,(
% 1.42/0.56    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.42/0.56    inference(resolution,[],[f249,f126])).
% 1.42/0.56  fof(f249,plain,(
% 1.42/0.56    ( ! [X1] : (~m1_subset_1(sK1,k1_zfmisc_1(X1)) | m1_subset_1(sK2(sK0,sK1),X1)) )),
% 1.42/0.56    inference(resolution,[],[f247,f56])).
% 1.42/0.56  fof(f56,plain,(
% 1.42/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f23])).
% 1.42/0.56  fof(f23,plain,(
% 1.42/0.56    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.42/0.56    inference(flattening,[],[f22])).
% 1.42/0.56  fof(f22,plain,(
% 1.42/0.56    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.42/0.56    inference(ennf_transformation,[],[f1])).
% 1.42/0.56  fof(f1,axiom,(
% 1.42/0.56    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 1.42/0.56  fof(f247,plain,(
% 1.42/0.56    r2_hidden(sK2(sK0,sK1),sK1)),
% 1.42/0.56    inference(subsumption_resolution,[],[f246,f126])).
% 1.42/0.56  fof(f246,plain,(
% 1.42/0.56    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(sK2(sK0,sK1),sK1)),
% 1.42/0.56    inference(forward_demodulation,[],[f245,f107])).
% 1.42/0.56  fof(f245,plain,(
% 1.42/0.56    r2_hidden(sK2(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))),
% 1.42/0.56    inference(subsumption_resolution,[],[f244,f142])).
% 1.42/0.56  fof(f142,plain,(
% 1.42/0.56    ~v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | r2_hidden(sK2(sK0,sK1),sK1)),
% 1.42/0.56    inference(subsumption_resolution,[],[f141,f36])).
% 1.42/0.56  fof(f141,plain,(
% 1.42/0.56    ~v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | r2_hidden(sK2(sK0,sK1),sK1) | ~l1_pre_topc(sK0)),
% 1.42/0.56    inference(subsumption_resolution,[],[f138,f126])).
% 1.42/0.56  fof(f138,plain,(
% 1.42/0.56    ~v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | r2_hidden(sK2(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)),
% 1.42/0.56    inference(resolution,[],[f127,f54])).
% 1.42/0.56  fof(f54,plain,(
% 1.42/0.56    ( ! [X0,X1] : (v1_tops_2(X1,X0) | r2_hidden(sK2(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f34])).
% 1.42/0.56  fof(f244,plain,(
% 1.42/0.56    r2_hidden(sK2(sK0,sK1),sK1) | v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))),
% 1.42/0.56    inference(subsumption_resolution,[],[f241,f58])).
% 1.42/0.56  fof(f241,plain,(
% 1.42/0.56    r2_hidden(sK2(sK0,sK1),sK1) | v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.42/0.56    inference(resolution,[],[f233,f55])).
% 1.42/0.56  fof(f233,plain,(
% 1.42/0.56    v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | r2_hidden(sK2(sK0,sK1),sK1)),
% 1.42/0.56    inference(subsumption_resolution,[],[f174,f232])).
% 1.42/0.56  fof(f232,plain,(
% 1.42/0.56    v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0) | r2_hidden(sK2(sK0,sK1),sK1)),
% 1.42/0.56    inference(subsumption_resolution,[],[f231,f144])).
% 1.42/0.56  fof(f144,plain,(
% 1.42/0.56    v1_tops_2(sK1,sK0) | r2_hidden(sK2(sK0,sK1),sK1)),
% 1.42/0.56    inference(resolution,[],[f142,f37])).
% 1.42/0.56  fof(f37,plain,(
% 1.42/0.56    v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v1_tops_2(sK1,sK0)),
% 1.42/0.56    inference(cnf_transformation,[],[f28])).
% 1.42/0.56  fof(f231,plain,(
% 1.42/0.56    ~v1_tops_2(sK1,sK0) | v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0) | r2_hidden(sK2(sK0,sK1),sK1)),
% 1.42/0.56    inference(subsumption_resolution,[],[f228,f36])).
% 1.42/0.56  fof(f228,plain,(
% 1.42/0.56    ~v1_tops_2(sK1,sK0) | v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0) | ~l1_pre_topc(sK0) | r2_hidden(sK2(sK0,sK1),sK1)),
% 1.42/0.56    inference(resolution,[],[f221,f126])).
% 1.42/0.56  fof(f221,plain,(
% 1.42/0.56    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(sK1,X0) | v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0) | ~l1_pre_topc(X0) | r2_hidden(sK2(sK0,sK1),sK1)) )),
% 1.42/0.56    inference(subsumption_resolution,[],[f220,f171])).
% 1.42/0.56  fof(f171,plain,(
% 1.42/0.56    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(X0)) | r2_hidden(sK2(sK0,sK1),sK1) | m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0)) )),
% 1.42/0.56    inference(resolution,[],[f153,f56])).
% 1.42/0.56  fof(f153,plain,(
% 1.42/0.56    r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK1) | r2_hidden(sK2(sK0,sK1),sK1)),
% 1.42/0.56    inference(subsumption_resolution,[],[f152,f126])).
% 1.42/0.56  fof(f152,plain,(
% 1.42/0.56    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(sK2(sK0,sK1),sK1) | r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK1)),
% 1.42/0.56    inference(forward_demodulation,[],[f151,f107])).
% 1.42/0.56  fof(f151,plain,(
% 1.42/0.56    r2_hidden(sK2(sK0,sK1),sK1) | r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))),
% 1.42/0.56    inference(subsumption_resolution,[],[f146,f58])).
% 1.42/0.56  fof(f146,plain,(
% 1.42/0.56    r2_hidden(sK2(sK0,sK1),sK1) | r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.42/0.56    inference(resolution,[],[f142,f54])).
% 1.42/0.56  fof(f220,plain,(
% 1.42/0.56    ( ! [X0] : (v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0) | ~m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_2(sK1,X0) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | r2_hidden(sK2(sK0,sK1),sK1)) )),
% 1.42/0.56    inference(resolution,[],[f52,f153])).
% 1.42/0.56  fof(f52,plain,(
% 1.42/0.56    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f34])).
% 1.42/0.56  fof(f174,plain,(
% 1.42/0.56    r2_hidden(sK2(sK0,sK1),sK1) | v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0)),
% 1.42/0.56    inference(subsumption_resolution,[],[f173,f35])).
% 1.42/0.56  fof(f35,plain,(
% 1.42/0.56    v2_pre_topc(sK0)),
% 1.42/0.56    inference(cnf_transformation,[],[f28])).
% 1.42/0.56  fof(f173,plain,(
% 1.42/0.56    r2_hidden(sK2(sK0,sK1),sK1) | v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0) | ~v2_pre_topc(sK0)),
% 1.42/0.56    inference(subsumption_resolution,[],[f172,f36])).
% 1.42/0.56  fof(f172,plain,(
% 1.42/0.56    r2_hidden(sK2(sK0,sK1),sK1) | v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 1.42/0.56    inference(resolution,[],[f150,f46])).
% 1.42/0.56  fof(f46,plain,(
% 1.42/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f30])).
% 1.42/0.56  fof(f30,plain,(
% 1.42/0.56    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.42/0.56    inference(flattening,[],[f29])).
% 1.42/0.56  fof(f29,plain,(
% 1.42/0.56    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.42/0.56    inference(nnf_transformation,[],[f16])).
% 1.42/0.56  fof(f16,plain,(
% 1.42/0.56    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.42/0.56    inference(flattening,[],[f15])).
% 1.42/0.56  fof(f15,plain,(
% 1.42/0.56    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.42/0.56    inference(ennf_transformation,[],[f6])).
% 1.42/0.56  fof(f6,axiom,(
% 1.42/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_pre_topc)).
% 1.42/0.56  fof(f150,plain,(
% 1.42/0.56    m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK2(sK0,sK1),sK1)),
% 1.42/0.56    inference(subsumption_resolution,[],[f149,f126])).
% 1.42/0.56  fof(f149,plain,(
% 1.42/0.56    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK2(sK0,sK1),sK1)),
% 1.42/0.56    inference(forward_demodulation,[],[f148,f107])).
% 1.42/0.56  fof(f148,plain,(
% 1.42/0.56    m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK2(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))),
% 1.42/0.56    inference(forward_demodulation,[],[f147,f107])).
% 1.42/0.56  fof(f147,plain,(
% 1.42/0.56    r2_hidden(sK2(sK0,sK1),sK1) | m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))),
% 1.42/0.56    inference(subsumption_resolution,[],[f145,f58])).
% 1.42/0.56  fof(f145,plain,(
% 1.42/0.56    r2_hidden(sK2(sK0,sK1),sK1) | m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.42/0.56    inference(resolution,[],[f142,f53])).
% 1.42/0.56  fof(f53,plain,(
% 1.42/0.56    ( ! [X0,X1] : (v1_tops_2(X1,X0) | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f34])).
% 1.42/0.56  fof(f269,plain,(
% 1.42/0.56    ~m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK2(sK0,sK1),sK0)),
% 1.42/0.56    inference(resolution,[],[f261,f224])).
% 1.42/0.56  fof(f224,plain,(
% 1.42/0.56    ( ! [X0] : (~v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X0,sK0)) )),
% 1.42/0.56    inference(forward_demodulation,[],[f223,f107])).
% 1.42/0.56  fof(f223,plain,(
% 1.42/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v3_pre_topc(X0,sK0)) )),
% 1.42/0.56    inference(subsumption_resolution,[],[f222,f36])).
% 1.42/0.56  fof(f222,plain,(
% 1.42/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(sK0) | v3_pre_topc(X0,sK0)) )),
% 1.42/0.56    inference(resolution,[],[f48,f35])).
% 1.42/0.56  fof(f48,plain,(
% 1.42/0.56    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | v3_pre_topc(X1,X0)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f30])).
% 1.42/0.56  fof(f261,plain,(
% 1.42/0.56    v3_pre_topc(sK2(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.42/0.56    inference(global_subsumption,[],[f37,f254,f258,f260])).
% 1.42/0.56  fof(f260,plain,(
% 1.42/0.56    ~v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v3_pre_topc(sK2(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.42/0.56    inference(subsumption_resolution,[],[f259,f58])).
% 1.42/0.56  fof(f259,plain,(
% 1.42/0.56    ~v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v3_pre_topc(sK2(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.42/0.56    inference(subsumption_resolution,[],[f256,f126])).
% 1.42/0.56  fof(f256,plain,(
% 1.42/0.56    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v3_pre_topc(sK2(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.42/0.56    inference(superposition,[],[f250,f107])).
% 1.42/0.56  fof(f250,plain,(
% 1.42/0.56    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(sK1,X0) | v3_pre_topc(sK2(sK0,sK1),X0) | ~l1_pre_topc(X0)) )),
% 1.42/0.56    inference(subsumption_resolution,[],[f248,f249])).
% 1.42/0.56  fof(f248,plain,(
% 1.42/0.56    ( ! [X0] : (v3_pre_topc(sK2(sK0,sK1),X0) | ~m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_2(sK1,X0) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.42/0.56    inference(resolution,[],[f247,f52])).
% 1.42/0.56  fof(f258,plain,(
% 1.42/0.56    ~v1_tops_2(sK1,sK0) | v3_pre_topc(sK2(sK0,sK1),sK0)),
% 1.42/0.56    inference(subsumption_resolution,[],[f255,f36])).
% 1.42/0.56  fof(f255,plain,(
% 1.42/0.56    ~v1_tops_2(sK1,sK0) | v3_pre_topc(sK2(sK0,sK1),sK0) | ~l1_pre_topc(sK0)),
% 1.42/0.56    inference(resolution,[],[f250,f126])).
% 1.42/0.56  fof(f254,plain,(
% 1.42/0.56    ~v3_pre_topc(sK2(sK0,sK1),sK0) | v3_pre_topc(sK2(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.42/0.56    inference(subsumption_resolution,[],[f253,f35])).
% 1.42/0.56  fof(f253,plain,(
% 1.42/0.56    v3_pre_topc(sK2(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v3_pre_topc(sK2(sK0,sK1),sK0) | ~v2_pre_topc(sK0)),
% 1.42/0.56    inference(subsumption_resolution,[],[f252,f36])).
% 1.42/0.56  fof(f252,plain,(
% 1.42/0.56    v3_pre_topc(sK2(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v3_pre_topc(sK2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 1.42/0.56    inference(resolution,[],[f251,f46])).
% 1.42/0.56  fof(f127,plain,(
% 1.42/0.56    ~v1_tops_2(sK1,sK0) | ~v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.42/0.56    inference(subsumption_resolution,[],[f125,f126])).
% 1.42/0.56  fof(f125,plain,(
% 1.42/0.56    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v1_tops_2(sK1,sK0)),
% 1.42/0.56    inference(duplicate_literal_removal,[],[f110])).
% 1.42/0.56  fof(f110,plain,(
% 1.42/0.56    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v1_tops_2(sK1,sK0)),
% 1.42/0.56    inference(backward_demodulation,[],[f41,f107])).
% 1.42/0.56  fof(f41,plain,(
% 1.42/0.56    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) | ~v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v1_tops_2(sK1,sK0)),
% 1.42/0.56    inference(cnf_transformation,[],[f28])).
% 1.42/0.56  fof(f345,plain,(
% 1.42/0.56    v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.42/0.56    inference(resolution,[],[f336,f55])).
% 1.42/0.56  fof(f336,plain,(
% 1.42/0.56    v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.42/0.56    inference(subsumption_resolution,[],[f306,f335])).
% 1.42/0.56  fof(f335,plain,(
% 1.42/0.56    v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0)),
% 1.42/0.56    inference(subsumption_resolution,[],[f334,f36])).
% 1.42/0.56  fof(f334,plain,(
% 1.42/0.56    v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0) | ~l1_pre_topc(sK0)),
% 1.42/0.56    inference(subsumption_resolution,[],[f331,f283])).
% 1.42/0.56  fof(f331,plain,(
% 1.42/0.56    ~v1_tops_2(sK1,sK0) | v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0) | ~l1_pre_topc(sK0)),
% 1.42/0.56    inference(resolution,[],[f303,f126])).
% 1.42/0.56  fof(f303,plain,(
% 1.42/0.56    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(sK1,X0) | v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0) | ~l1_pre_topc(X0)) )),
% 1.42/0.56    inference(subsumption_resolution,[],[f301,f302])).
% 1.42/0.56  fof(f302,plain,(
% 1.42/0.56    ( ! [X1] : (~m1_subset_1(sK1,k1_zfmisc_1(X1)) | m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X1)) )),
% 1.42/0.56    inference(resolution,[],[f300,f56])).
% 1.42/0.56  fof(f300,plain,(
% 1.42/0.56    r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK1)),
% 1.42/0.56    inference(subsumption_resolution,[],[f299,f126])).
% 1.42/0.56  fof(f299,plain,(
% 1.42/0.56    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK1)),
% 1.42/0.56    inference(forward_demodulation,[],[f298,f107])).
% 1.42/0.56  fof(f298,plain,(
% 1.42/0.56    r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))),
% 1.42/0.56    inference(subsumption_resolution,[],[f293,f58])).
% 1.42/0.56  fof(f293,plain,(
% 1.42/0.56    r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.42/0.56    inference(resolution,[],[f285,f54])).
% 1.42/0.56  fof(f301,plain,(
% 1.42/0.56    ( ! [X0] : (v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0) | ~m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_2(sK1,X0) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.42/0.56    inference(resolution,[],[f300,f52])).
% 1.42/0.56  fof(f306,plain,(
% 1.42/0.56    v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0)),
% 1.42/0.56    inference(subsumption_resolution,[],[f305,f35])).
% 1.42/0.56  fof(f305,plain,(
% 1.42/0.56    v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0) | ~v2_pre_topc(sK0)),
% 1.42/0.56    inference(subsumption_resolution,[],[f304,f36])).
% 1.42/0.56  fof(f304,plain,(
% 1.42/0.56    v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 1.42/0.56    inference(resolution,[],[f297,f46])).
% 1.42/0.56  fof(f297,plain,(
% 1.42/0.56    m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.42/0.56    inference(subsumption_resolution,[],[f296,f126])).
% 1.42/0.56  fof(f296,plain,(
% 1.42/0.56    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.42/0.56    inference(forward_demodulation,[],[f295,f107])).
% 1.42/0.56  fof(f295,plain,(
% 1.42/0.56    m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))),
% 1.42/0.56    inference(forward_demodulation,[],[f294,f107])).
% 1.42/0.56  fof(f294,plain,(
% 1.42/0.56    m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))),
% 1.42/0.56    inference(subsumption_resolution,[],[f292,f58])).
% 1.42/0.56  fof(f292,plain,(
% 1.42/0.56    m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.42/0.56    inference(resolution,[],[f285,f53])).
% 1.42/0.56  % SZS output end Proof for theBenchmark
% 1.42/0.56  % (28455)------------------------------
% 1.42/0.56  % (28455)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (28455)Termination reason: Refutation
% 1.42/0.56  
% 1.42/0.56  % (28455)Memory used [KB]: 6396
% 1.42/0.56  % (28455)Time elapsed: 0.127 s
% 1.42/0.56  % (28455)------------------------------
% 1.42/0.56  % (28455)------------------------------
% 1.42/0.56  % (28464)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.42/0.56  % (28449)Success in time 0.191 s
%------------------------------------------------------------------------------
