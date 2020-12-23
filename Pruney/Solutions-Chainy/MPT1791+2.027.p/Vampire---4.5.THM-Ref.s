%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:25 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   97 (1548 expanded)
%              Number of leaves         :    9 ( 408 expanded)
%              Depth                    :   33
%              Number of atoms          :  361 (10063 expanded)
%              Number of equality atoms :   85 (2250 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f139,plain,(
    $false ),
    inference(resolution,[],[f137,f28])).

fof(f28,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k6_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) )
            & ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( k6_tmap_1(sK0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
            | ~ v3_pre_topc(X1,sK0) )
          & ( k6_tmap_1(sK0,X1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( ( k6_tmap_1(sK0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
          | ~ v3_pre_topc(X1,sK0) )
        & ( k6_tmap_1(sK0,X1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
          | v3_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
        | ~ v3_pre_topc(sK1,sK0) )
      & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
        | v3_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k6_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
            | ~ v3_pre_topc(X1,X0) )
          & ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k6_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
            | ~ v3_pre_topc(X1,X0) )
          & ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).

fof(f137,plain,(
    v2_struct_0(sK0) ),
    inference(resolution,[],[f136,f125])).

fof(f125,plain,(
    ~ v3_pre_topc(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f124])).

fof(f124,plain,
    ( k6_tmap_1(sK0,sK1) != k6_tmap_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f97,f120])).

fof(f120,plain,(
    k6_tmap_1(sK0,sK1) = k6_tmap_1(sK0,sK2(sK0)) ),
    inference(backward_demodulation,[],[f95,f119])).

fof(f119,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(backward_demodulation,[],[f76,f117])).

fof(f117,plain,(
    u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f114])).

fof(f114,plain,
    ( u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) ),
    inference(superposition,[],[f111,f69])).

fof(f69,plain,(
    k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f66,f28])).

fof(f66,plain,
    ( v2_struct_0(sK0)
    | k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f65,f31])).

fof(f31,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f65,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k5_tmap_1(sK0,X0) = u1_pre_topc(k6_tmap_1(sK0,X0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f55,f30])).

fof(f30,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f55,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k5_tmap_1(sK0,X0) = u1_pre_topc(k6_tmap_1(sK0,X0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f38,f29])).

fof(f29,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

fof(f111,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(k6_tmap_1(sK0,sK1))
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) ),
    inference(superposition,[],[f94,f104])).

fof(f104,plain,
    ( k6_tmap_1(sK0,sK1) = k6_tmap_1(sK0,sK2(sK0))
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) ),
    inference(superposition,[],[f95,f84])).

fof(f84,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) ),
    inference(resolution,[],[f83,f28])).

fof(f83,plain,
    ( v2_struct_0(sK0)
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(resolution,[],[f79,f31])).

fof(f79,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)
    | v2_struct_0(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(resolution,[],[f77,f51])).

fof(f51,plain,
    ( r2_hidden(sK1,u1_pre_topc(sK0))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(resolution,[],[f45,f31])).

fof(f45,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,u1_pre_topc(sK0))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(resolution,[],[f43,f32])).

fof(f32,plain,
    ( v3_pre_topc(sK1,sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X0,u1_pre_topc(sK0)) ) ),
    inference(resolution,[],[f34,f30])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f77,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_pre_topc(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_pre_topc(sK0) = k5_tmap_1(sK0,X0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f68,f30])).

fof(f68,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,u1_pre_topc(sK0))
      | u1_pre_topc(sK0) = k5_tmap_1(sK0,X0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f39,f29])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | u1_pre_topc(X0) = k5_tmap_1(X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X1,u1_pre_topc(X0))
              | u1_pre_topc(X0) != k5_tmap_1(X0,X1) )
            & ( u1_pre_topc(X0) = k5_tmap_1(X0,X1)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).

fof(f94,plain,(
    u1_pre_topc(sK0) = u1_pre_topc(k6_tmap_1(sK0,sK2(sK0))) ),
    inference(backward_demodulation,[],[f72,f93])).

fof(f93,plain,(
    u1_pre_topc(sK0) = k5_tmap_1(sK0,sK2(sK0)) ),
    inference(resolution,[],[f92,f30])).

fof(f92,plain,
    ( ~ l1_pre_topc(sK0)
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK2(sK0)) ),
    inference(resolution,[],[f91,f29])).

fof(f91,plain,
    ( ~ v2_pre_topc(sK0)
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK2(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f90,f28])).

fof(f90,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK2(sK0))
    | ~ v2_pre_topc(sK0) ),
    inference(duplicate_literal_removal,[],[f89])).

fof(f89,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK2(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f88,f41])).

fof(f41,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v3_pre_topc(sK2(X0),X0)
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v3_pre_topc(sK2(X0),X0)
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ? [X1] :
          ( v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_tops_1)).

fof(f88,plain,
    ( ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK2(sK0)) ),
    inference(resolution,[],[f78,f29])).

fof(f78,plain,
    ( ~ v2_pre_topc(sK0)
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK2(sK0))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f77,f48])).

fof(f48,plain,
    ( r2_hidden(sK2(sK0),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(duplicate_literal_removal,[],[f47])).

fof(f47,plain,
    ( ~ l1_pre_topc(sK0)
    | r2_hidden(sK2(sK0),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f46,f41])).

fof(f46,plain,
    ( ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | r2_hidden(sK2(sK0),u1_pre_topc(sK0)) ),
    inference(resolution,[],[f44,f29])).

fof(f44,plain,
    ( ~ v2_pre_topc(sK0)
    | r2_hidden(sK2(sK0),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f43,f42])).

fof(f42,plain,(
    ! [X0] :
      ( v3_pre_topc(sK2(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f72,plain,(
    k5_tmap_1(sK0,sK2(sK0)) = u1_pre_topc(k6_tmap_1(sK0,sK2(sK0))) ),
    inference(resolution,[],[f71,f30])).

fof(f71,plain,
    ( ~ l1_pre_topc(sK0)
    | k5_tmap_1(sK0,sK2(sK0)) = u1_pre_topc(k6_tmap_1(sK0,sK2(sK0))) ),
    inference(resolution,[],[f70,f29])).

fof(f70,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | k5_tmap_1(sK0,sK2(sK0)) = u1_pre_topc(k6_tmap_1(sK0,sK2(sK0))) ),
    inference(resolution,[],[f67,f28])).

fof(f67,plain,
    ( v2_struct_0(sK0)
    | k5_tmap_1(sK0,sK2(sK0)) = u1_pre_topc(k6_tmap_1(sK0,sK2(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f65,f41])).

fof(f76,plain,(
    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f74,f28])).

fof(f74,plain,
    ( v2_struct_0(sK0)
    | k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f73,f31])).

fof(f73,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k6_tmap_1(sK0,X0) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f62,f30])).

fof(f62,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k6_tmap_1(sK0,X0) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f36,f29])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_tmap_1)).

fof(f95,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK2(sK0)) ),
    inference(backward_demodulation,[],[f82,f93])).

fof(f82,plain,(
    k6_tmap_1(sK0,sK2(sK0)) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK2(sK0))) ),
    inference(resolution,[],[f81,f30])).

fof(f81,plain,
    ( ~ l1_pre_topc(sK0)
    | k6_tmap_1(sK0,sK2(sK0)) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK2(sK0))) ),
    inference(resolution,[],[f80,f29])).

fof(f80,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | k6_tmap_1(sK0,sK2(sK0)) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK2(sK0))) ),
    inference(resolution,[],[f75,f28])).

fof(f75,plain,
    ( v2_struct_0(sK0)
    | k6_tmap_1(sK0,sK2(sK0)) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK2(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f73,f41])).

fof(f97,plain,
    ( k6_tmap_1(sK0,sK1) != k6_tmap_1(sK0,sK2(sK0))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f33,f95])).

fof(f33,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f136,plain,
    ( v3_pre_topc(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f134,f31])).

fof(f134,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | v3_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f132,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_pre_topc(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(X0,sK0) ) ),
    inference(resolution,[],[f35,f30])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f132,plain,
    ( r2_hidden(sK1,u1_pre_topc(sK0))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f131,f30])).

fof(f131,plain,
    ( ~ l1_pre_topc(sK0)
    | r2_hidden(sK1,u1_pre_topc(sK0))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f130,f31])).

fof(f130,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | r2_hidden(sK1,u1_pre_topc(sK0))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f129,f29])).

fof(f129,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | r2_hidden(sK1,u1_pre_topc(sK0))
    | v2_struct_0(sK0) ),
    inference(trivial_inequality_removal,[],[f128])).

fof(f128,plain,
    ( u1_pre_topc(sK0) != u1_pre_topc(sK0)
    | r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f40,f117])).

fof(f40,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(X0) != k5_tmap_1(X0,X1)
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:35:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.48  % (19196)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.49  % (19189)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.49  % (19192)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.49  % (19191)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.50  % (19211)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.50  % (19194)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.50  % (19196)Refutation not found, incomplete strategy% (19196)------------------------------
% 0.22/0.50  % (19196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (19196)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  % (19193)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.50  
% 0.22/0.50  % (19196)Memory used [KB]: 10618
% 0.22/0.50  % (19196)Time elapsed: 0.079 s
% 0.22/0.50  % (19196)------------------------------
% 0.22/0.50  % (19196)------------------------------
% 0.22/0.50  % (19203)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.50  % (19197)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.50  % (19191)Refutation not found, incomplete strategy% (19191)------------------------------
% 0.22/0.50  % (19191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (19191)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (19191)Memory used [KB]: 10618
% 0.22/0.50  % (19191)Time elapsed: 0.093 s
% 0.22/0.50  % (19191)------------------------------
% 0.22/0.50  % (19191)------------------------------
% 0.22/0.51  % (19197)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f139,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(resolution,[],[f137,f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ~v2_struct_0(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f22,f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : ((k6_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0)) & (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((k6_tmap_1(sK0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~v3_pre_topc(X1,sK0)) & (k6_tmap_1(sK0,X1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ? [X1] : ((k6_tmap_1(sK0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~v3_pre_topc(X1,sK0)) & (k6_tmap_1(sK0,X1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : ((k6_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0)) & (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (((k6_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0)) & (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f8])).
% 0.22/0.51  fof(f8,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,negated_conjecture,(
% 0.22/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.22/0.51    inference(negated_conjecture,[],[f6])).
% 0.22/0.51  fof(f6,conjecture,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).
% 0.22/0.51  fof(f137,plain,(
% 0.22/0.51    v2_struct_0(sK0)),
% 0.22/0.51    inference(resolution,[],[f136,f125])).
% 0.22/0.51  fof(f125,plain,(
% 0.22/0.51    ~v3_pre_topc(sK1,sK0)),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f124])).
% 0.22/0.51  fof(f124,plain,(
% 0.22/0.51    k6_tmap_1(sK0,sK1) != k6_tmap_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)),
% 0.22/0.51    inference(backward_demodulation,[],[f97,f120])).
% 0.22/0.51  fof(f120,plain,(
% 0.22/0.51    k6_tmap_1(sK0,sK1) = k6_tmap_1(sK0,sK2(sK0))),
% 0.22/0.51    inference(backward_demodulation,[],[f95,f119])).
% 0.22/0.51  fof(f119,plain,(
% 0.22/0.51    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)),
% 0.22/0.51    inference(backward_demodulation,[],[f76,f117])).
% 0.22/0.51  fof(f117,plain,(
% 0.22/0.51    u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f114])).
% 0.22/0.51  fof(f114,plain,(
% 0.22/0.51    u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)),
% 0.22/0.51    inference(superposition,[],[f111,f69])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.22/0.51    inference(resolution,[],[f66,f28])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    v2_struct_0(sK0) | k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.22/0.51    inference(resolution,[],[f65,f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.51    inference(cnf_transformation,[],[f23])).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k5_tmap_1(sK0,X0) = u1_pre_topc(k6_tmap_1(sK0,X0)) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(resolution,[],[f55,f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    l1_pre_topc(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f23])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k5_tmap_1(sK0,X0) = u1_pre_topc(k6_tmap_1(sK0,X0)) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(resolution,[],[f38,f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    v2_pre_topc(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f23])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).
% 0.22/0.51  fof(f111,plain,(
% 0.22/0.51    u1_pre_topc(sK0) = u1_pre_topc(k6_tmap_1(sK0,sK1)) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)),
% 0.22/0.51    inference(superposition,[],[f94,f104])).
% 0.22/0.51  fof(f104,plain,(
% 0.22/0.51    k6_tmap_1(sK0,sK1) = k6_tmap_1(sK0,sK2(sK0)) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)),
% 0.22/0.51    inference(superposition,[],[f95,f84])).
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)),
% 0.22/0.51    inference(resolution,[],[f83,f28])).
% 0.22/0.51  fof(f83,plain,(
% 0.22/0.51    v2_struct_0(sK0) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)),
% 0.22/0.51    inference(resolution,[],[f79,f31])).
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) | v2_struct_0(sK0) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)),
% 0.22/0.51    inference(resolution,[],[f77,f51])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    r2_hidden(sK1,u1_pre_topc(sK0)) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)),
% 0.22/0.51    inference(resolution,[],[f45,f31])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK1,u1_pre_topc(sK0)) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)),
% 0.22/0.51    inference(resolution,[],[f43,f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    v3_pre_topc(sK1,sK0) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f23])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ( ! [X0] : (~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X0,u1_pre_topc(sK0))) )),
% 0.22/0.51    inference(resolution,[],[f34,f30])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X1,u1_pre_topc(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(X0,u1_pre_topc(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_pre_topc(sK0) = k5_tmap_1(sK0,X0) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(resolution,[],[f68,f30])).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,u1_pre_topc(sK0)) | u1_pre_topc(sK0) = k5_tmap_1(sK0,X0) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(resolution,[],[f39,f29])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | u1_pre_topc(X0) = k5_tmap_1(X0,X1) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (((r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1)) & (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).
% 0.22/0.51  fof(f94,plain,(
% 0.22/0.51    u1_pre_topc(sK0) = u1_pre_topc(k6_tmap_1(sK0,sK2(sK0)))),
% 0.22/0.51    inference(backward_demodulation,[],[f72,f93])).
% 0.22/0.51  fof(f93,plain,(
% 0.22/0.51    u1_pre_topc(sK0) = k5_tmap_1(sK0,sK2(sK0))),
% 0.22/0.51    inference(resolution,[],[f92,f30])).
% 0.22/0.51  fof(f92,plain,(
% 0.22/0.51    ~l1_pre_topc(sK0) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK2(sK0))),
% 0.22/0.51    inference(resolution,[],[f91,f29])).
% 0.22/0.51  fof(f91,plain,(
% 0.22/0.51    ~v2_pre_topc(sK0) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK2(sK0)) | ~l1_pre_topc(sK0)),
% 0.22/0.51    inference(resolution,[],[f90,f28])).
% 0.22/0.51  fof(f90,plain,(
% 0.22/0.51    v2_struct_0(sK0) | ~l1_pre_topc(sK0) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK2(sK0)) | ~v2_pre_topc(sK0)),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f89])).
% 0.22/0.51  fof(f89,plain,(
% 0.22/0.51    v2_struct_0(sK0) | ~l1_pre_topc(sK0) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK2(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.22/0.51    inference(resolution,[],[f88,f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ( ! [X0] : (m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0] : ((v3_pre_topc(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X0] : (? [X1] : (v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (v3_pre_topc(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0] : (? [X1] : (v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0] : (? [X1] : (v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ? [X1] : (v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_tops_1)).
% 0.22/0.51  fof(f88,plain,(
% 0.22/0.51    ~m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK2(sK0))),
% 0.22/0.51    inference(resolution,[],[f78,f29])).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    ~v2_pre_topc(sK0) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK2(sK0)) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.51    inference(resolution,[],[f77,f48])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    r2_hidden(sK2(sK0),u1_pre_topc(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f47])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    ~l1_pre_topc(sK0) | r2_hidden(sK2(sK0),u1_pre_topc(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.22/0.51    inference(resolution,[],[f46,f41])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ~m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | r2_hidden(sK2(sK0),u1_pre_topc(sK0))),
% 0.22/0.51    inference(resolution,[],[f44,f29])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ~v2_pre_topc(sK0) | r2_hidden(sK2(sK0),u1_pre_topc(sK0)) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.51    inference(resolution,[],[f43,f42])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ( ! [X0] : (v3_pre_topc(sK2(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    k5_tmap_1(sK0,sK2(sK0)) = u1_pre_topc(k6_tmap_1(sK0,sK2(sK0)))),
% 0.22/0.51    inference(resolution,[],[f71,f30])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    ~l1_pre_topc(sK0) | k5_tmap_1(sK0,sK2(sK0)) = u1_pre_topc(k6_tmap_1(sK0,sK2(sK0)))),
% 0.22/0.51    inference(resolution,[],[f70,f29])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | k5_tmap_1(sK0,sK2(sK0)) = u1_pre_topc(k6_tmap_1(sK0,sK2(sK0)))),
% 0.22/0.51    inference(resolution,[],[f67,f28])).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    v2_struct_0(sK0) | k5_tmap_1(sK0,sK2(sK0)) = u1_pre_topc(k6_tmap_1(sK0,sK2(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.22/0.51    inference(resolution,[],[f65,f41])).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))),
% 0.22/0.51    inference(resolution,[],[f74,f28])).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    v2_struct_0(sK0) | k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))),
% 0.22/0.51    inference(resolution,[],[f73,f31])).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k6_tmap_1(sK0,X0) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0)) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(resolution,[],[f62,f30])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k6_tmap_1(sK0,X0) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0)) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(resolution,[],[f36,f29])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_tmap_1)).
% 0.22/0.51  fof(f95,plain,(
% 0.22/0.51    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK2(sK0))),
% 0.22/0.51    inference(backward_demodulation,[],[f82,f93])).
% 0.22/0.51  fof(f82,plain,(
% 0.22/0.51    k6_tmap_1(sK0,sK2(sK0)) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK2(sK0)))),
% 0.22/0.51    inference(resolution,[],[f81,f30])).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    ~l1_pre_topc(sK0) | k6_tmap_1(sK0,sK2(sK0)) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK2(sK0)))),
% 0.22/0.51    inference(resolution,[],[f80,f29])).
% 0.22/0.51  fof(f80,plain,(
% 0.22/0.51    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | k6_tmap_1(sK0,sK2(sK0)) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK2(sK0)))),
% 0.22/0.51    inference(resolution,[],[f75,f28])).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    v2_struct_0(sK0) | k6_tmap_1(sK0,sK2(sK0)) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK2(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.22/0.51    inference(resolution,[],[f73,f41])).
% 0.22/0.51  fof(f97,plain,(
% 0.22/0.51    k6_tmap_1(sK0,sK1) != k6_tmap_1(sK0,sK2(sK0)) | ~v3_pre_topc(sK1,sK0)),
% 0.22/0.51    inference(backward_demodulation,[],[f33,f95])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f23])).
% 0.22/0.51  fof(f136,plain,(
% 0.22/0.51    v3_pre_topc(sK1,sK0) | v2_struct_0(sK0)),
% 0.22/0.51    inference(resolution,[],[f134,f31])).
% 0.22/0.51  fof(f134,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | v3_pre_topc(sK1,sK0)),
% 0.22/0.51    inference(resolution,[],[f132,f49])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(X0,u1_pre_topc(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X0,sK0)) )),
% 0.22/0.51    inference(resolution,[],[f35,f30])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f132,plain,(
% 0.22/0.51    r2_hidden(sK1,u1_pre_topc(sK0)) | v2_struct_0(sK0)),
% 0.22/0.51    inference(resolution,[],[f131,f30])).
% 0.22/0.51  fof(f131,plain,(
% 0.22/0.51    ~l1_pre_topc(sK0) | r2_hidden(sK1,u1_pre_topc(sK0)) | v2_struct_0(sK0)),
% 0.22/0.51    inference(resolution,[],[f130,f31])).
% 0.22/0.51  fof(f130,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | r2_hidden(sK1,u1_pre_topc(sK0)) | v2_struct_0(sK0)),
% 0.22/0.51    inference(resolution,[],[f129,f29])).
% 0.22/0.51  fof(f129,plain,(
% 0.22/0.51    ~v2_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | r2_hidden(sK1,u1_pre_topc(sK0)) | v2_struct_0(sK0)),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f128])).
% 0.22/0.51  fof(f128,plain,(
% 0.22/0.51    u1_pre_topc(sK0) != u1_pre_topc(sK0) | r2_hidden(sK1,u1_pre_topc(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.51    inference(superposition,[],[f40,f117])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ( ! [X0,X1] : (u1_pre_topc(X0) != k5_tmap_1(X0,X1) | r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (19197)------------------------------
% 0.22/0.51  % (19197)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (19197)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (19197)Memory used [KB]: 1663
% 0.22/0.51  % (19197)Time elapsed: 0.094 s
% 0.22/0.51  % (19197)------------------------------
% 0.22/0.51  % (19197)------------------------------
% 0.22/0.51  % (19187)Success in time 0.147 s
%------------------------------------------------------------------------------
