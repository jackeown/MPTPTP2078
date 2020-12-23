%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:53 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   70 (1054 expanded)
%              Number of leaves         :    8 ( 268 expanded)
%              Depth                    :   26
%              Number of atoms          :  250 (6703 expanded)
%              Number of equality atoms :   29 ( 250 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f438,plain,(
    $false ),
    inference(subsumption_resolution,[],[f437,f24])).

fof(f24,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
      | ~ v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ v1_tops_2(sK1,sK0) )
    & ( ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
        & v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
      | ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        & v1_tops_2(sK1,sK0) ) )
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f19,f18])).

fof(f18,plain,
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
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
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
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
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

fof(f17,plain,(
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
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            & v1_tops_2(X1,X0) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            & v1_tops_2(X1,X0) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              & v1_tops_2(X1,X0) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
              & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
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

fof(f437,plain,(
    ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f436,f195])).

fof(f195,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(duplicate_literal_removal,[],[f170])).

fof(f170,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(backward_demodulation,[],[f28,f168])).

fof(f168,plain,(
    u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f167,f54])).

fof(f54,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f41,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f41,plain,(
    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f24,f30])).

fof(f30,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f167,plain,
    ( u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f165,f53])).

fof(f53,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f41,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f165,plain,
    ( u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != X0
      | u1_struct_0(X0) = u1_struct_0(sK0)
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f51,f31])).

fof(f31,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
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

fof(f51,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | u1_struct_0(sK0) = X0 ) ),
    inference(resolution,[],[f41,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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

fof(f28,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f20])).

fof(f436,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f435,f425])).

fof(f425,plain,(
    r1_tarski(sK1,u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f424,f205])).

fof(f205,plain,
    ( r1_tarski(sK1,u1_pre_topc(sK0))
    | ~ v1_tops_2(sK1,sK0) ),
    inference(resolution,[],[f195,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ v1_tops_2(X0,sK0)
      | r1_tarski(X0,u1_pre_topc(sK0)) ) ),
    inference(resolution,[],[f24,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,u1_pre_topc(X0))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ~ r1_tarski(X1,u1_pre_topc(X0)) )
            & ( r1_tarski(X1,u1_pre_topc(X0))
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).

fof(f424,plain,
    ( r1_tarski(sK1,u1_pre_topc(sK0))
    | v1_tops_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f412,f54])).

% (24941)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f412,plain,
    ( r1_tarski(sK1,u1_pre_topc(sK0))
    | v1_tops_2(sK1,sK0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(backward_demodulation,[],[f45,f410])).

fof(f410,plain,(
    u1_pre_topc(sK0) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(trivial_inequality_removal,[],[f407])).

fof(f407,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
    | u1_pre_topc(sK0) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(superposition,[],[f52,f172])).

fof(f172,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    inference(backward_demodulation,[],[f59,f168])).

fof(f59,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    inference(subsumption_resolution,[],[f57,f54])).

fof(f57,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f53,f31])).

fof(f52,plain,(
    ! [X2,X3] :
      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X3,X2)
      | u1_pre_topc(sK0) = X2 ) ),
    inference(resolution,[],[f41,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f45,plain,
    ( v1_tops_2(sK1,sK0)
    | r1_tarski(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f42,f27])).

fof(f27,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f42,plain,
    ( v1_tops_2(sK1,sK0)
    | r1_tarski(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f25,f32])).

% (24915)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
fof(f25,plain,
    ( v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f435,plain,
    ( ~ r1_tarski(sK1,u1_pre_topc(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f429,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ r1_tarski(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f429,plain,(
    ~ v1_tops_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f421,f425])).

fof(f421,plain,
    ( ~ r1_tarski(sK1,u1_pre_topc(sK0))
    | ~ v1_tops_2(sK1,sK0) ),
    inference(backward_demodulation,[],[f261,f410])).

fof(f261,plain,
    ( ~ r1_tarski(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_tops_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f260,f195])).

fof(f260,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v1_tops_2(sK1,sK0)
    | ~ r1_tarski(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    inference(forward_demodulation,[],[f259,f168])).

fof(f259,plain,
    ( ~ v1_tops_2(sK1,sK0)
    | ~ r1_tarski(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ),
    inference(subsumption_resolution,[],[f256,f54])).

fof(f256,plain,
    ( ~ v1_tops_2(sK1,sK0)
    | ~ r1_tarski(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f196,f33])).

fof(f196,plain,
    ( ~ v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v1_tops_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f194,f195])).

fof(f194,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v1_tops_2(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f171])).

fof(f171,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v1_tops_2(sK1,sK0) ),
    inference(backward_demodulation,[],[f29,f168])).

fof(f29,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:52:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (24935)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (24926)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (24920)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (24918)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (24919)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (24937)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.52  % (24917)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (24928)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.52  % (24928)Refutation not found, incomplete strategy% (24928)------------------------------
% 0.20/0.52  % (24928)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (24928)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (24928)Memory used [KB]: 10618
% 0.20/0.52  % (24928)Time elapsed: 0.104 s
% 0.20/0.52  % (24928)------------------------------
% 0.20/0.52  % (24928)------------------------------
% 0.20/0.52  % (24920)Refutation not found, incomplete strategy% (24920)------------------------------
% 0.20/0.52  % (24920)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (24920)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (24920)Memory used [KB]: 10618
% 0.20/0.52  % (24920)Time elapsed: 0.116 s
% 0.20/0.52  % (24920)------------------------------
% 0.20/0.52  % (24920)------------------------------
% 0.20/0.52  % (24913)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (24913)Refutation not found, incomplete strategy% (24913)------------------------------
% 0.20/0.53  % (24913)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (24913)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (24913)Memory used [KB]: 10874
% 0.20/0.53  % (24913)Time elapsed: 0.115 s
% 0.20/0.53  % (24913)------------------------------
% 0.20/0.53  % (24913)------------------------------
% 0.20/0.53  % (24912)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (24935)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % (24940)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f438,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(subsumption_resolution,[],[f437,f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    l1_pre_topc(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ((~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) | ~v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v1_tops_2(sK1,sK0)) & ((m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) & v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) & v1_tops_2(sK1,sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f19,f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) | ~v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0)) & ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) | ~v1_tops_2(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v1_tops_2(X1,sK0)) & ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) & v1_tops_2(X1,sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) | ~v1_tops_2(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v1_tops_2(X1,sK0)) & ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) & v1_tops_2(X1,sK0)))) => ((~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) | ~v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v1_tops_2(sK1,sK0)) & ((m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) & v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) & v1_tops_2(sK1,sK0))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) | ~v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0)) & ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f16])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (((~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) | ~v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) & ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.53    inference(nnf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)) <~> (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f8])).
% 0.20/0.53  fof(f8,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)) <~> (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,negated_conjecture,(
% 0.20/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 0.20/0.53    inference(negated_conjecture,[],[f6])).
% 0.20/0.53  fof(f6,conjecture,(
% 0.20/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_compts_1)).
% 0.20/0.53  fof(f437,plain,(
% 0.20/0.53    ~l1_pre_topc(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f436,f195])).
% 0.20/0.53  fof(f195,plain,(
% 0.20/0.53    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f170])).
% 0.20/0.53  fof(f170,plain,(
% 0.20/0.53    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.53    inference(backward_demodulation,[],[f28,f168])).
% 0.20/0.53  fof(f168,plain,(
% 0.20/0.53    u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.20/0.53    inference(subsumption_resolution,[],[f167,f54])).
% 0.20/0.53  fof(f54,plain,(
% 0.20/0.53    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.20/0.53    inference(resolution,[],[f41,f35])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.53    inference(ennf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.53    inference(resolution,[],[f24,f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,plain,(
% 0.20/0.53    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.20/0.53  fof(f167,plain,(
% 0.20/0.53    u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.20/0.53    inference(subsumption_resolution,[],[f165,f53])).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.20/0.53    inference(resolution,[],[f41,f34])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f14])).
% 0.20/0.53  fof(f165,plain,(
% 0.20/0.53    u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.20/0.53    inference(equality_resolution,[],[f91])).
% 0.20/0.53  fof(f91,plain,(
% 0.20/0.53    ( ! [X0] : (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != X0 | u1_struct_0(X0) = u1_struct_0(sK0) | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.53    inference(superposition,[],[f51,f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,plain,(
% 0.20/0.53    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(flattening,[],[f11])).
% 0.20/0.53  fof(f11,plain,(
% 0.20/0.53    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ( ! [X0,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | u1_struct_0(sK0) = X0) )),
% 0.20/0.53    inference(resolution,[],[f41,f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f15])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.53    inference(ennf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f436,plain,(
% 0.20/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f435,f425])).
% 0.20/0.53  fof(f425,plain,(
% 0.20/0.53    r1_tarski(sK1,u1_pre_topc(sK0))),
% 0.20/0.53    inference(subsumption_resolution,[],[f424,f205])).
% 0.20/0.53  fof(f205,plain,(
% 0.20/0.53    r1_tarski(sK1,u1_pre_topc(sK0)) | ~v1_tops_2(sK1,sK0)),
% 0.20/0.53    inference(resolution,[],[f195,f38])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v1_tops_2(X0,sK0) | r1_tarski(X0,u1_pre_topc(sK0))) )),
% 0.20/0.53    inference(resolution,[],[f24,f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ~r1_tarski(X1,u1_pre_topc(X0))) & (r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(nnf_transformation,[],[f13])).
% 0.20/0.53  fof(f13,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0)))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).
% 0.20/0.53  fof(f424,plain,(
% 0.20/0.53    r1_tarski(sK1,u1_pre_topc(sK0)) | v1_tops_2(sK1,sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f412,f54])).
% 0.20/0.53  % (24941)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  fof(f412,plain,(
% 0.20/0.53    r1_tarski(sK1,u1_pre_topc(sK0)) | v1_tops_2(sK1,sK0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.20/0.53    inference(backward_demodulation,[],[f45,f410])).
% 0.20/0.53  fof(f410,plain,(
% 0.20/0.53    u1_pre_topc(sK0) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f407])).
% 0.20/0.53  fof(f407,plain,(
% 0.20/0.53    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | u1_pre_topc(sK0) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.20/0.53    inference(superposition,[],[f52,f172])).
% 0.20/0.53  fof(f172,plain,(
% 0.20/0.53    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 0.20/0.53    inference(backward_demodulation,[],[f59,f168])).
% 0.20/0.53  fof(f59,plain,(
% 0.20/0.53    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 0.20/0.53    inference(subsumption_resolution,[],[f57,f54])).
% 0.20/0.53  fof(f57,plain,(
% 0.20/0.53    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.20/0.53    inference(resolution,[],[f53,f31])).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    ( ! [X2,X3] : (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X3,X2) | u1_pre_topc(sK0) = X2) )),
% 0.20/0.53    inference(resolution,[],[f41,f37])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (X1 = X3 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f15])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    v1_tops_2(sK1,sK0) | r1_tarski(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.20/0.53    inference(subsumption_resolution,[],[f42,f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) | v1_tops_2(sK1,sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    v1_tops_2(sK1,sK0) | r1_tarski(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.20/0.53    inference(resolution,[],[f25,f32])).
% 0.20/0.53  % (24915)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v1_tops_2(sK1,sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f435,plain,(
% 0.20/0.53    ~r1_tarski(sK1,u1_pre_topc(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)),
% 0.20/0.53    inference(resolution,[],[f429,f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v1_tops_2(X1,X0) | ~r1_tarski(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f21])).
% 0.20/0.53  fof(f429,plain,(
% 0.20/0.53    ~v1_tops_2(sK1,sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f421,f425])).
% 0.20/0.53  fof(f421,plain,(
% 0.20/0.53    ~r1_tarski(sK1,u1_pre_topc(sK0)) | ~v1_tops_2(sK1,sK0)),
% 0.20/0.53    inference(backward_demodulation,[],[f261,f410])).
% 0.20/0.53  fof(f261,plain,(
% 0.20/0.53    ~r1_tarski(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~v1_tops_2(sK1,sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f260,f195])).
% 0.20/0.53  fof(f260,plain,(
% 0.20/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v1_tops_2(sK1,sK0) | ~r1_tarski(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 0.20/0.53    inference(forward_demodulation,[],[f259,f168])).
% 0.20/0.53  fof(f259,plain,(
% 0.20/0.53    ~v1_tops_2(sK1,sK0) | ~r1_tarski(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))),
% 0.20/0.53    inference(subsumption_resolution,[],[f256,f54])).
% 0.20/0.53  fof(f256,plain,(
% 0.20/0.53    ~v1_tops_2(sK1,sK0) | ~r1_tarski(sK1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.20/0.53    inference(resolution,[],[f196,f33])).
% 0.20/0.53  fof(f196,plain,(
% 0.20/0.53    ~v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v1_tops_2(sK1,sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f194,f195])).
% 0.20/0.53  fof(f194,plain,(
% 0.20/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v1_tops_2(sK1,sK0)),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f171])).
% 0.20/0.53  fof(f171,plain,(
% 0.20/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v1_tops_2(sK1,sK0)),
% 0.20/0.53    inference(backward_demodulation,[],[f29,f168])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) | ~v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v1_tops_2(sK1,sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (24935)------------------------------
% 0.20/0.53  % (24935)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (24935)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (24935)Memory used [KB]: 1918
% 0.20/0.53  % (24911)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (24935)Time elapsed: 0.064 s
% 0.20/0.53  % (24935)------------------------------
% 0.20/0.53  % (24935)------------------------------
% 0.20/0.53  % (24911)Refutation not found, incomplete strategy% (24911)------------------------------
% 0.20/0.53  % (24911)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (24911)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (24911)Memory used [KB]: 1663
% 0.20/0.53  % (24911)Time elapsed: 0.123 s
% 0.20/0.53  % (24911)------------------------------
% 0.20/0.53  % (24911)------------------------------
% 0.20/0.53  % (24916)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.54  % (24907)Success in time 0.175 s
%------------------------------------------------------------------------------
