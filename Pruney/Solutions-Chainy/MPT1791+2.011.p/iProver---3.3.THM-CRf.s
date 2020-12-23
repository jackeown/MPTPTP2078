%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:51 EST 2020

% Result     : Theorem 0.42s
% Output     : CNFRefutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :  151 (1377 expanded)
%              Number of clauses        :   99 ( 346 expanded)
%              Number of leaves         :   13 ( 303 expanded)
%              Depth                    :   22
%              Number of atoms          :  611 (8432 expanded)
%              Number of equality atoms :  144 (1997 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,sK1)
          | ~ v3_pre_topc(sK1,X0) )
        & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,sK1)
          | v3_pre_topc(sK1,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)
              | ~ v3_pre_topc(X1,X0) )
            & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,X1)
            | ~ v3_pre_topc(X1,sK0) )
          & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X1)
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f32,f31])).

fof(f53,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f52,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f44,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(X0) = k5_tmap_1(X0,X1)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f49,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f50,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f51,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))
             => ( X1 = X2
               => v3_pre_topc(X2,k6_tmap_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v3_pre_topc(X2,k6_tmap_1(X0,X1))
              | X1 != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v3_pre_topc(X2,k6_tmap_1(X0,X1))
              | X1 != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,k6_tmap_1(X0,X1))
      | X1 != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f55,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,k6_tmap_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X2))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f46,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f34,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f47,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | u1_pre_topc(X0) != k5_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f54,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_16,negated_conjecture,
    ( v3_pre_topc(sK1,sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_950,negated_conjecture,
    ( v3_pre_topc(sK1,sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1403,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_950])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_949,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1404,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_949])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,u1_pre_topc(X1))
    | ~ v3_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) = u1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_331,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) = u1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_2,c_11])).

cnf(c_20,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_369,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) = u1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_331,c_20])).

cnf(c_370,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(X0,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | k5_tmap_1(sK0,X0) = u1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_369])).

cnf(c_19,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_18,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_374,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(X0,sK0)
    | k5_tmap_1(sK0,X0) = u1_pre_topc(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_370,c_19,c_18])).

cnf(c_948,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(X0_43,sK0)
    | k5_tmap_1(sK0,X0_43) = u1_pre_topc(sK0) ),
    inference(subtyping,[status(esa)],[c_374])).

cnf(c_1405,plain,
    ( k5_tmap_1(sK0,X0_43) = u1_pre_topc(sK0)
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v3_pre_topc(X0_43,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_948])).

cnf(c_1614,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
    | v3_pre_topc(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1404,c_1405])).

cnf(c_1648,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1403,c_1614])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_570,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ v2_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_18])).

cnf(c_571,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v3_pre_topc(X0,sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_570])).

cnf(c_575,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_571,c_19])).

cnf(c_576,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v3_pre_topc(X0,sK0) ),
    inference(renaming,[status(thm)],[c_575])).

cnf(c_942,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(X0_43,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v3_pre_topc(X0_43,sK0) ),
    inference(subtyping,[status(esa)],[c_576])).

cnf(c_1411,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v3_pre_topc(X0_43,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
    | v3_pre_topc(X0_43,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_942])).

cnf(c_1776,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v3_pre_topc(X0_43,k6_tmap_1(sK0,sK1)) = iProver_top
    | v3_pre_topc(X0_43,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1648,c_1411])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X0))))
    | v3_pre_topc(X0,k6_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_411,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X0))))
    | v3_pre_topc(X0,k6_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_20])).

cnf(c_412,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X0))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(X0,k6_tmap_1(sK0,X0))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_411])).

cnf(c_416,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X0))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(X0,k6_tmap_1(sK0,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_412,c_19,c_18])).

cnf(c_946,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X0_43))))
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(X0_43,k6_tmap_1(sK0,X0_43)) ),
    inference(subtyping,[status(esa)],[c_416])).

cnf(c_991,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK1,k6_tmap_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_946])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_432,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_20])).

cnf(c_433,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | u1_struct_0(k6_tmap_1(sK0,X0)) = u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_432])).

cnf(c_437,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(k6_tmap_1(sK0,X0)) = u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_433,c_19,c_18])).

cnf(c_945,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(k6_tmap_1(sK0,X0_43)) = u1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_437])).

cnf(c_994,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(k6_tmap_1(sK0,sK1)) = u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_945])).

cnf(c_965,plain,
    ( ~ m1_subset_1(X0_43,X0_44)
    | m1_subset_1(X0_43,X1_44)
    | X1_44 != X0_44 ),
    theory(equality)).

cnf(c_1563,plain,
    ( m1_subset_1(sK1,X0_44)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | X0_44 != k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_965])).

cnf(c_1579,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(X0_45))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_zfmisc_1(X0_45) != k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1563])).

cnf(c_1593,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))) != k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1579])).

cnf(c_1615,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1614])).

cnf(c_964,plain,
    ( X0_45 != X1_45
    | k1_zfmisc_1(X0_45) = k1_zfmisc_1(X1_45) ),
    theory(equality)).

cnf(c_1580,plain,
    ( X0_45 != u1_struct_0(sK0)
    | k1_zfmisc_1(X0_45) = k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_964])).

cnf(c_1627,plain,
    ( u1_struct_0(k6_tmap_1(sK0,X0_43)) != u1_struct_0(sK0)
    | k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X0_43))) = k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1580])).

cnf(c_1628,plain,
    ( u1_struct_0(k6_tmap_1(sK0,sK1)) != u1_struct_0(sK0)
    | k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))) = k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1627])).

cnf(c_963,plain,
    ( ~ v3_pre_topc(X0_43,X0_46)
    | v3_pre_topc(X0_43,X1_46)
    | X1_46 != X0_46 ),
    theory(equality)).

cnf(c_1684,plain,
    ( v3_pre_topc(X0_43,X0_46)
    | ~ v3_pre_topc(X0_43,k6_tmap_1(sK0,X0_43))
    | X0_46 != k6_tmap_1(sK0,X0_43) ),
    inference(instantiation,[status(thm)],[c_963])).

cnf(c_1711,plain,
    ( ~ v3_pre_topc(sK1,k6_tmap_1(sK0,sK1))
    | v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_1684])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_612,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ v2_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_18])).

cnf(c_613,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v3_pre_topc(X0,sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_612])).

cnf(c_617,plain,
    ( v3_pre_topc(X0,sK0)
    | ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_613,c_19])).

cnf(c_618,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v3_pre_topc(X0,sK0) ),
    inference(renaming,[status(thm)],[c_617])).

cnf(c_940,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ v3_pre_topc(X0_43,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v3_pre_topc(X0_43,sK0) ),
    inference(subtyping,[status(esa)],[c_618])).

cnf(c_1413,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) != iProver_top
    | v3_pre_topc(X0_43,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | v3_pre_topc(X0_43,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_940])).

cnf(c_1902,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) != iProver_top
    | v3_pre_topc(X0_43,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | v3_pre_topc(X0_43,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1648,c_1413])).

cnf(c_1408,plain,
    ( u1_struct_0(k6_tmap_1(sK0,X0_43)) = u1_struct_0(sK0)
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_945])).

cnf(c_1562,plain,
    ( u1_struct_0(k6_tmap_1(sK0,sK1)) = u1_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_1404,c_1408])).

cnf(c_1907,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v3_pre_topc(X0_43,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | v3_pre_topc(X0_43,sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1902,c_1562])).

cnf(c_1912,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(X0_43,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v3_pre_topc(X0_43,sK0)
    | k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1907])).

cnf(c_1914,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v3_pre_topc(sK1,sK0)
    | k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1912])).

cnf(c_2095,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1776,c_17,c_991,c_994,c_1593,c_1615,c_1628,c_1648,c_1711,c_1914])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k6_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_468,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k6_tmap_1(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_20])).

cnf(c_469,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_pre_topc(k6_tmap_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_468])).

cnf(c_473,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_pre_topc(k6_tmap_1(sK0,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_469,c_19,c_18])).

cnf(c_549,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(sK0,X0) != X1
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_473])).

cnf(c_550,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(k6_tmap_1(sK0,X0))
    | g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X0)),u1_pre_topc(k6_tmap_1(sK0,X0))) = k6_tmap_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_549])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k6_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_504,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k6_tmap_1(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_20])).

cnf(c_505,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | l1_pre_topc(k6_tmap_1(sK0,X0))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_504])).

cnf(c_554,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X0)),u1_pre_topc(k6_tmap_1(sK0,X0))) = k6_tmap_1(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_550,c_19,c_18,c_505])).

cnf(c_943,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X0_43)),u1_pre_topc(k6_tmap_1(sK0,X0_43))) = k6_tmap_1(sK0,X0_43) ),
    inference(subtyping,[status(esa)],[c_554])).

cnf(c_1410,plain,
    ( g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X0_43)),u1_pre_topc(k6_tmap_1(sK0,X0_43))) = k6_tmap_1(sK0,X0_43)
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_943])).

cnf(c_1700,plain,
    ( g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_pre_topc(k6_tmap_1(sK0,sK1))) = k6_tmap_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1404,c_1410])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_450,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_20])).

cnf(c_451,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | u1_pre_topc(k6_tmap_1(sK0,X0)) = k5_tmap_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_450])).

cnf(c_455,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_pre_topc(k6_tmap_1(sK0,X0)) = k5_tmap_1(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_451,c_19,c_18])).

cnf(c_944,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_pre_topc(k6_tmap_1(sK0,X0_43)) = k5_tmap_1(sK0,X0_43) ),
    inference(subtyping,[status(esa)],[c_455])).

cnf(c_1409,plain,
    ( u1_pre_topc(k6_tmap_1(sK0,X0_43)) = k5_tmap_1(sK0,X0_43)
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_944])).

cnf(c_1577,plain,
    ( u1_pre_topc(k6_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1404,c_1409])).

cnf(c_1701,plain,
    ( g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) = k6_tmap_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_1700,c_1562,c_1577])).

cnf(c_2098,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_2095,c_1701])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,u1_pre_topc(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) != u1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | v3_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_308,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v3_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) != u1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_10,c_1])).

cnf(c_390,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v3_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) != u1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_308,c_20])).

cnf(c_391,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(X0,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | k5_tmap_1(sK0,X0) != u1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_390])).

cnf(c_395,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(X0,sK0)
    | k5_tmap_1(sK0,X0) != u1_pre_topc(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_391,c_19,c_18])).

cnf(c_947,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(X0_43,sK0)
    | k5_tmap_1(sK0,X0_43) != u1_pre_topc(sK0) ),
    inference(subtyping,[status(esa)],[c_395])).

cnf(c_988,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK1,sK0)
    | k5_tmap_1(sK0,sK1) != u1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_947])).

cnf(c_15,negated_conjecture,
    ( ~ v3_pre_topc(sK1,sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_951,negated_conjecture,
    ( ~ v3_pre_topc(sK1,sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2098,c_2095,c_988,c_951,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:58:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 0.42/1.04  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.42/1.04  
% 0.42/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.42/1.04  
% 0.42/1.04  ------  iProver source info
% 0.42/1.04  
% 0.42/1.04  git: date: 2020-06-30 10:37:57 +0100
% 0.42/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.42/1.04  git: non_committed_changes: false
% 0.42/1.04  git: last_make_outside_of_git: false
% 0.42/1.04  
% 0.42/1.04  ------ 
% 0.42/1.04  
% 0.42/1.04  ------ Input Options
% 0.42/1.04  
% 0.42/1.04  --out_options                           all
% 0.42/1.04  --tptp_safe_out                         true
% 0.42/1.04  --problem_path                          ""
% 0.42/1.04  --include_path                          ""
% 0.42/1.04  --clausifier                            res/vclausify_rel
% 0.42/1.04  --clausifier_options                    --mode clausify
% 0.42/1.04  --stdin                                 false
% 0.42/1.04  --stats_out                             all
% 0.42/1.04  
% 0.42/1.04  ------ General Options
% 0.42/1.04  
% 0.42/1.04  --fof                                   false
% 0.42/1.04  --time_out_real                         305.
% 0.42/1.04  --time_out_virtual                      -1.
% 0.42/1.04  --symbol_type_check                     false
% 0.42/1.04  --clausify_out                          false
% 0.42/1.04  --sig_cnt_out                           false
% 0.42/1.04  --trig_cnt_out                          false
% 0.42/1.04  --trig_cnt_out_tolerance                1.
% 0.42/1.04  --trig_cnt_out_sk_spl                   false
% 0.42/1.04  --abstr_cl_out                          false
% 0.42/1.04  
% 0.42/1.04  ------ Global Options
% 0.42/1.04  
% 0.42/1.04  --schedule                              default
% 0.42/1.04  --add_important_lit                     false
% 0.42/1.04  --prop_solver_per_cl                    1000
% 0.42/1.04  --min_unsat_core                        false
% 0.42/1.04  --soft_assumptions                      false
% 0.42/1.04  --soft_lemma_size                       3
% 0.42/1.04  --prop_impl_unit_size                   0
% 0.42/1.04  --prop_impl_unit                        []
% 0.42/1.04  --share_sel_clauses                     true
% 0.42/1.04  --reset_solvers                         false
% 0.42/1.04  --bc_imp_inh                            [conj_cone]
% 0.42/1.04  --conj_cone_tolerance                   3.
% 0.42/1.04  --extra_neg_conj                        none
% 0.42/1.04  --large_theory_mode                     true
% 0.42/1.04  --prolific_symb_bound                   200
% 0.42/1.04  --lt_threshold                          2000
% 0.42/1.04  --clause_weak_htbl                      true
% 0.42/1.04  --gc_record_bc_elim                     false
% 0.42/1.04  
% 0.42/1.04  ------ Preprocessing Options
% 0.42/1.04  
% 0.42/1.04  --preprocessing_flag                    true
% 0.42/1.04  --time_out_prep_mult                    0.1
% 0.42/1.04  --splitting_mode                        input
% 0.42/1.04  --splitting_grd                         true
% 0.42/1.04  --splitting_cvd                         false
% 0.42/1.04  --splitting_cvd_svl                     false
% 0.42/1.04  --splitting_nvd                         32
% 0.42/1.04  --sub_typing                            true
% 0.42/1.04  --prep_gs_sim                           true
% 0.42/1.04  --prep_unflatten                        true
% 0.42/1.04  --prep_res_sim                          true
% 0.42/1.04  --prep_upred                            true
% 0.42/1.04  --prep_sem_filter                       exhaustive
% 0.42/1.04  --prep_sem_filter_out                   false
% 0.42/1.04  --pred_elim                             true
% 0.42/1.04  --res_sim_input                         true
% 0.42/1.04  --eq_ax_congr_red                       true
% 0.42/1.04  --pure_diseq_elim                       true
% 0.42/1.04  --brand_transform                       false
% 0.42/1.04  --non_eq_to_eq                          false
% 0.42/1.04  --prep_def_merge                        true
% 0.42/1.04  --prep_def_merge_prop_impl              false
% 0.42/1.04  --prep_def_merge_mbd                    true
% 0.42/1.04  --prep_def_merge_tr_red                 false
% 0.42/1.04  --prep_def_merge_tr_cl                  false
% 0.42/1.04  --smt_preprocessing                     true
% 0.42/1.04  --smt_ac_axioms                         fast
% 0.42/1.04  --preprocessed_out                      false
% 0.42/1.04  --preprocessed_stats                    false
% 0.42/1.04  
% 0.42/1.04  ------ Abstraction refinement Options
% 0.42/1.04  
% 0.42/1.04  --abstr_ref                             []
% 0.42/1.04  --abstr_ref_prep                        false
% 0.42/1.04  --abstr_ref_until_sat                   false
% 0.42/1.04  --abstr_ref_sig_restrict                funpre
% 0.42/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 0.42/1.04  --abstr_ref_under                       []
% 0.42/1.04  
% 0.42/1.04  ------ SAT Options
% 0.42/1.04  
% 0.42/1.04  --sat_mode                              false
% 0.42/1.04  --sat_fm_restart_options                ""
% 0.42/1.04  --sat_gr_def                            false
% 0.42/1.04  --sat_epr_types                         true
% 0.42/1.04  --sat_non_cyclic_types                  false
% 0.42/1.04  --sat_finite_models                     false
% 0.42/1.04  --sat_fm_lemmas                         false
% 0.42/1.04  --sat_fm_prep                           false
% 0.42/1.04  --sat_fm_uc_incr                        true
% 0.42/1.04  --sat_out_model                         small
% 0.42/1.04  --sat_out_clauses                       false
% 0.42/1.04  
% 0.42/1.04  ------ QBF Options
% 0.42/1.04  
% 0.42/1.04  --qbf_mode                              false
% 0.42/1.04  --qbf_elim_univ                         false
% 0.42/1.04  --qbf_dom_inst                          none
% 0.42/1.04  --qbf_dom_pre_inst                      false
% 0.42/1.04  --qbf_sk_in                             false
% 0.42/1.04  --qbf_pred_elim                         true
% 0.42/1.04  --qbf_split                             512
% 0.42/1.04  
% 0.42/1.04  ------ BMC1 Options
% 0.42/1.04  
% 0.42/1.04  --bmc1_incremental                      false
% 0.42/1.04  --bmc1_axioms                           reachable_all
% 0.42/1.04  --bmc1_min_bound                        0
% 0.42/1.04  --bmc1_max_bound                        -1
% 0.42/1.04  --bmc1_max_bound_default                -1
% 0.42/1.04  --bmc1_symbol_reachability              true
% 0.42/1.04  --bmc1_property_lemmas                  false
% 0.42/1.04  --bmc1_k_induction                      false
% 0.42/1.04  --bmc1_non_equiv_states                 false
% 0.42/1.04  --bmc1_deadlock                         false
% 0.42/1.04  --bmc1_ucm                              false
% 0.42/1.04  --bmc1_add_unsat_core                   none
% 0.42/1.04  --bmc1_unsat_core_children              false
% 0.42/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 0.42/1.04  --bmc1_out_stat                         full
% 0.42/1.04  --bmc1_ground_init                      false
% 0.42/1.04  --bmc1_pre_inst_next_state              false
% 0.42/1.04  --bmc1_pre_inst_state                   false
% 0.42/1.04  --bmc1_pre_inst_reach_state             false
% 0.42/1.04  --bmc1_out_unsat_core                   false
% 0.42/1.04  --bmc1_aig_witness_out                  false
% 0.42/1.04  --bmc1_verbose                          false
% 0.42/1.04  --bmc1_dump_clauses_tptp                false
% 0.42/1.04  --bmc1_dump_unsat_core_tptp             false
% 0.42/1.04  --bmc1_dump_file                        -
% 0.42/1.04  --bmc1_ucm_expand_uc_limit              128
% 0.42/1.04  --bmc1_ucm_n_expand_iterations          6
% 0.42/1.04  --bmc1_ucm_extend_mode                  1
% 0.42/1.04  --bmc1_ucm_init_mode                    2
% 0.42/1.04  --bmc1_ucm_cone_mode                    none
% 0.42/1.04  --bmc1_ucm_reduced_relation_type        0
% 0.42/1.04  --bmc1_ucm_relax_model                  4
% 0.42/1.04  --bmc1_ucm_full_tr_after_sat            true
% 0.42/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 0.42/1.04  --bmc1_ucm_layered_model                none
% 0.42/1.04  --bmc1_ucm_max_lemma_size               10
% 0.42/1.04  
% 0.42/1.04  ------ AIG Options
% 0.42/1.04  
% 0.42/1.04  --aig_mode                              false
% 0.42/1.04  
% 0.42/1.04  ------ Instantiation Options
% 0.42/1.04  
% 0.42/1.04  --instantiation_flag                    true
% 0.42/1.04  --inst_sos_flag                         false
% 0.42/1.04  --inst_sos_phase                        true
% 0.42/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.42/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.42/1.04  --inst_lit_sel_side                     num_symb
% 0.42/1.04  --inst_solver_per_active                1400
% 0.42/1.04  --inst_solver_calls_frac                1.
% 0.42/1.04  --inst_passive_queue_type               priority_queues
% 0.42/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.42/1.04  --inst_passive_queues_freq              [25;2]
% 0.42/1.04  --inst_dismatching                      true
% 0.42/1.04  --inst_eager_unprocessed_to_passive     true
% 0.42/1.04  --inst_prop_sim_given                   true
% 0.42/1.04  --inst_prop_sim_new                     false
% 0.42/1.04  --inst_subs_new                         false
% 0.42/1.04  --inst_eq_res_simp                      false
% 0.42/1.04  --inst_subs_given                       false
% 0.42/1.04  --inst_orphan_elimination               true
% 0.42/1.04  --inst_learning_loop_flag               true
% 0.42/1.04  --inst_learning_start                   3000
% 0.42/1.04  --inst_learning_factor                  2
% 0.42/1.04  --inst_start_prop_sim_after_learn       3
% 0.42/1.04  --inst_sel_renew                        solver
% 0.42/1.04  --inst_lit_activity_flag                true
% 0.42/1.04  --inst_restr_to_given                   false
% 0.42/1.04  --inst_activity_threshold               500
% 0.42/1.04  --inst_out_proof                        true
% 0.42/1.04  
% 0.42/1.04  ------ Resolution Options
% 0.42/1.04  
% 0.42/1.04  --resolution_flag                       true
% 0.42/1.04  --res_lit_sel                           adaptive
% 0.42/1.04  --res_lit_sel_side                      none
% 0.42/1.04  --res_ordering                          kbo
% 0.42/1.04  --res_to_prop_solver                    active
% 0.42/1.04  --res_prop_simpl_new                    false
% 0.42/1.04  --res_prop_simpl_given                  true
% 0.42/1.04  --res_passive_queue_type                priority_queues
% 0.42/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.42/1.04  --res_passive_queues_freq               [15;5]
% 0.42/1.04  --res_forward_subs                      full
% 0.42/1.04  --res_backward_subs                     full
% 0.42/1.04  --res_forward_subs_resolution           true
% 0.42/1.04  --res_backward_subs_resolution          true
% 0.42/1.04  --res_orphan_elimination                true
% 0.42/1.04  --res_time_limit                        2.
% 0.42/1.04  --res_out_proof                         true
% 0.42/1.04  
% 0.42/1.04  ------ Superposition Options
% 0.42/1.04  
% 0.42/1.04  --superposition_flag                    true
% 0.42/1.04  --sup_passive_queue_type                priority_queues
% 0.42/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.42/1.04  --sup_passive_queues_freq               [8;1;4]
% 0.42/1.04  --demod_completeness_check              fast
% 0.42/1.04  --demod_use_ground                      true
% 0.42/1.04  --sup_to_prop_solver                    passive
% 0.42/1.04  --sup_prop_simpl_new                    true
% 0.42/1.04  --sup_prop_simpl_given                  true
% 0.42/1.04  --sup_fun_splitting                     false
% 0.42/1.04  --sup_smt_interval                      50000
% 0.42/1.04  
% 0.42/1.04  ------ Superposition Simplification Setup
% 0.42/1.04  
% 0.42/1.04  --sup_indices_passive                   []
% 0.42/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.42/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.42/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.42/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 0.42/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.42/1.04  --sup_full_bw                           [BwDemod]
% 0.42/1.04  --sup_immed_triv                        [TrivRules]
% 0.42/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.42/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.42/1.04  --sup_immed_bw_main                     []
% 0.42/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.42/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 0.42/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.42/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.42/1.04  
% 0.42/1.04  ------ Combination Options
% 0.42/1.04  
% 0.42/1.04  --comb_res_mult                         3
% 0.42/1.04  --comb_sup_mult                         2
% 0.42/1.04  --comb_inst_mult                        10
% 0.42/1.04  
% 0.42/1.04  ------ Debug Options
% 0.42/1.04  
% 0.42/1.04  --dbg_backtrace                         false
% 0.42/1.04  --dbg_dump_prop_clauses                 false
% 0.42/1.04  --dbg_dump_prop_clauses_file            -
% 0.42/1.04  --dbg_out_stat                          false
% 0.42/1.04  ------ Parsing...
% 0.42/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.42/1.04  
% 0.42/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 0.42/1.04  
% 0.42/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.42/1.04  
% 0.42/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.42/1.04  ------ Proving...
% 0.42/1.04  ------ Problem Properties 
% 0.42/1.04  
% 0.42/1.04  
% 0.42/1.04  clauses                                 17
% 0.42/1.04  conjectures                             3
% 0.42/1.04  EPR                                     0
% 0.42/1.04  Horn                                    16
% 0.42/1.04  unary                                   1
% 0.42/1.04  binary                                  5
% 0.42/1.04  lits                                    48
% 0.42/1.04  lits eq                                 7
% 0.42/1.04  fd_pure                                 0
% 0.42/1.04  fd_pseudo                               0
% 0.42/1.04  fd_cond                                 0
% 0.42/1.04  fd_pseudo_cond                          0
% 0.42/1.04  AC symbols                              0
% 0.42/1.04  
% 0.42/1.04  ------ Schedule dynamic 5 is on 
% 0.42/1.04  
% 0.42/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.42/1.04  
% 0.42/1.04  
% 0.42/1.04  ------ 
% 0.42/1.04  Current options:
% 0.42/1.04  ------ 
% 0.42/1.04  
% 0.42/1.04  ------ Input Options
% 0.42/1.04  
% 0.42/1.04  --out_options                           all
% 0.42/1.04  --tptp_safe_out                         true
% 0.42/1.04  --problem_path                          ""
% 0.42/1.04  --include_path                          ""
% 0.42/1.04  --clausifier                            res/vclausify_rel
% 0.42/1.04  --clausifier_options                    --mode clausify
% 0.42/1.04  --stdin                                 false
% 0.42/1.04  --stats_out                             all
% 0.42/1.04  
% 0.42/1.04  ------ General Options
% 0.42/1.04  
% 0.42/1.04  --fof                                   false
% 0.42/1.04  --time_out_real                         305.
% 0.42/1.04  --time_out_virtual                      -1.
% 0.42/1.04  --symbol_type_check                     false
% 0.42/1.04  --clausify_out                          false
% 0.42/1.04  --sig_cnt_out                           false
% 0.42/1.04  --trig_cnt_out                          false
% 0.42/1.04  --trig_cnt_out_tolerance                1.
% 0.42/1.04  --trig_cnt_out_sk_spl                   false
% 0.42/1.04  --abstr_cl_out                          false
% 0.42/1.04  
% 0.42/1.04  ------ Global Options
% 0.42/1.04  
% 0.42/1.04  --schedule                              default
% 0.42/1.04  --add_important_lit                     false
% 0.42/1.04  --prop_solver_per_cl                    1000
% 0.42/1.04  --min_unsat_core                        false
% 0.42/1.04  --soft_assumptions                      false
% 0.42/1.04  --soft_lemma_size                       3
% 0.42/1.04  --prop_impl_unit_size                   0
% 0.42/1.04  --prop_impl_unit                        []
% 0.42/1.04  --share_sel_clauses                     true
% 0.42/1.04  --reset_solvers                         false
% 0.42/1.04  --bc_imp_inh                            [conj_cone]
% 0.42/1.04  --conj_cone_tolerance                   3.
% 0.42/1.04  --extra_neg_conj                        none
% 0.42/1.04  --large_theory_mode                     true
% 0.42/1.04  --prolific_symb_bound                   200
% 0.42/1.04  --lt_threshold                          2000
% 0.42/1.04  --clause_weak_htbl                      true
% 0.42/1.04  --gc_record_bc_elim                     false
% 0.42/1.04  
% 0.42/1.04  ------ Preprocessing Options
% 0.42/1.04  
% 0.42/1.04  --preprocessing_flag                    true
% 0.42/1.04  --time_out_prep_mult                    0.1
% 0.42/1.04  --splitting_mode                        input
% 0.42/1.04  --splitting_grd                         true
% 0.42/1.04  --splitting_cvd                         false
% 0.42/1.04  --splitting_cvd_svl                     false
% 0.42/1.04  --splitting_nvd                         32
% 0.42/1.04  --sub_typing                            true
% 0.42/1.04  --prep_gs_sim                           true
% 0.42/1.04  --prep_unflatten                        true
% 0.42/1.04  --prep_res_sim                          true
% 0.42/1.04  --prep_upred                            true
% 0.42/1.04  --prep_sem_filter                       exhaustive
% 0.42/1.04  --prep_sem_filter_out                   false
% 0.42/1.04  --pred_elim                             true
% 0.42/1.04  --res_sim_input                         true
% 0.42/1.04  --eq_ax_congr_red                       true
% 0.42/1.04  --pure_diseq_elim                       true
% 0.42/1.04  --brand_transform                       false
% 0.42/1.04  --non_eq_to_eq                          false
% 0.42/1.04  --prep_def_merge                        true
% 0.42/1.04  --prep_def_merge_prop_impl              false
% 0.42/1.04  --prep_def_merge_mbd                    true
% 0.42/1.04  --prep_def_merge_tr_red                 false
% 0.42/1.04  --prep_def_merge_tr_cl                  false
% 0.42/1.04  --smt_preprocessing                     true
% 0.42/1.04  --smt_ac_axioms                         fast
% 0.42/1.04  --preprocessed_out                      false
% 0.42/1.04  --preprocessed_stats                    false
% 0.42/1.04  
% 0.42/1.04  ------ Abstraction refinement Options
% 0.42/1.04  
% 0.42/1.04  --abstr_ref                             []
% 0.42/1.04  --abstr_ref_prep                        false
% 0.42/1.04  --abstr_ref_until_sat                   false
% 0.42/1.04  --abstr_ref_sig_restrict                funpre
% 0.42/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 0.42/1.04  --abstr_ref_under                       []
% 0.42/1.04  
% 0.42/1.04  ------ SAT Options
% 0.42/1.04  
% 0.42/1.04  --sat_mode                              false
% 0.42/1.04  --sat_fm_restart_options                ""
% 0.42/1.04  --sat_gr_def                            false
% 0.42/1.04  --sat_epr_types                         true
% 0.42/1.04  --sat_non_cyclic_types                  false
% 0.42/1.04  --sat_finite_models                     false
% 0.42/1.04  --sat_fm_lemmas                         false
% 0.42/1.04  --sat_fm_prep                           false
% 0.42/1.04  --sat_fm_uc_incr                        true
% 0.42/1.04  --sat_out_model                         small
% 0.42/1.04  --sat_out_clauses                       false
% 0.42/1.04  
% 0.42/1.04  ------ QBF Options
% 0.42/1.04  
% 0.42/1.04  --qbf_mode                              false
% 0.42/1.04  --qbf_elim_univ                         false
% 0.42/1.04  --qbf_dom_inst                          none
% 0.42/1.04  --qbf_dom_pre_inst                      false
% 0.42/1.04  --qbf_sk_in                             false
% 0.42/1.04  --qbf_pred_elim                         true
% 0.42/1.04  --qbf_split                             512
% 0.42/1.04  
% 0.42/1.04  ------ BMC1 Options
% 0.42/1.04  
% 0.42/1.04  --bmc1_incremental                      false
% 0.42/1.04  --bmc1_axioms                           reachable_all
% 0.42/1.04  --bmc1_min_bound                        0
% 0.42/1.04  --bmc1_max_bound                        -1
% 0.42/1.04  --bmc1_max_bound_default                -1
% 0.42/1.04  --bmc1_symbol_reachability              true
% 0.42/1.04  --bmc1_property_lemmas                  false
% 0.42/1.04  --bmc1_k_induction                      false
% 0.42/1.04  --bmc1_non_equiv_states                 false
% 0.42/1.04  --bmc1_deadlock                         false
% 0.42/1.04  --bmc1_ucm                              false
% 0.42/1.04  --bmc1_add_unsat_core                   none
% 0.42/1.04  --bmc1_unsat_core_children              false
% 0.42/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 0.42/1.04  --bmc1_out_stat                         full
% 0.42/1.04  --bmc1_ground_init                      false
% 0.42/1.04  --bmc1_pre_inst_next_state              false
% 0.42/1.04  --bmc1_pre_inst_state                   false
% 0.42/1.04  --bmc1_pre_inst_reach_state             false
% 0.42/1.04  --bmc1_out_unsat_core                   false
% 0.42/1.04  --bmc1_aig_witness_out                  false
% 0.42/1.04  --bmc1_verbose                          false
% 0.42/1.04  --bmc1_dump_clauses_tptp                false
% 0.42/1.04  --bmc1_dump_unsat_core_tptp             false
% 0.42/1.04  --bmc1_dump_file                        -
% 0.42/1.04  --bmc1_ucm_expand_uc_limit              128
% 0.42/1.04  --bmc1_ucm_n_expand_iterations          6
% 0.42/1.04  --bmc1_ucm_extend_mode                  1
% 0.42/1.04  --bmc1_ucm_init_mode                    2
% 0.42/1.04  --bmc1_ucm_cone_mode                    none
% 0.42/1.04  --bmc1_ucm_reduced_relation_type        0
% 0.42/1.04  --bmc1_ucm_relax_model                  4
% 0.42/1.04  --bmc1_ucm_full_tr_after_sat            true
% 0.42/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 0.42/1.04  --bmc1_ucm_layered_model                none
% 0.42/1.04  --bmc1_ucm_max_lemma_size               10
% 0.42/1.04  
% 0.42/1.04  ------ AIG Options
% 0.42/1.04  
% 0.42/1.04  --aig_mode                              false
% 0.42/1.04  
% 0.42/1.04  ------ Instantiation Options
% 0.42/1.04  
% 0.42/1.04  --instantiation_flag                    true
% 0.42/1.04  --inst_sos_flag                         false
% 0.42/1.04  --inst_sos_phase                        true
% 0.42/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.42/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.42/1.04  --inst_lit_sel_side                     none
% 0.42/1.04  --inst_solver_per_active                1400
% 0.42/1.04  --inst_solver_calls_frac                1.
% 0.42/1.04  --inst_passive_queue_type               priority_queues
% 0.42/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.42/1.04  --inst_passive_queues_freq              [25;2]
% 0.42/1.04  --inst_dismatching                      true
% 0.42/1.04  --inst_eager_unprocessed_to_passive     true
% 0.42/1.04  --inst_prop_sim_given                   true
% 0.42/1.04  --inst_prop_sim_new                     false
% 0.42/1.04  --inst_subs_new                         false
% 0.42/1.04  --inst_eq_res_simp                      false
% 0.42/1.04  --inst_subs_given                       false
% 0.42/1.04  --inst_orphan_elimination               true
% 0.42/1.04  --inst_learning_loop_flag               true
% 0.42/1.04  --inst_learning_start                   3000
% 0.42/1.04  --inst_learning_factor                  2
% 0.42/1.04  --inst_start_prop_sim_after_learn       3
% 0.42/1.04  --inst_sel_renew                        solver
% 0.42/1.04  --inst_lit_activity_flag                true
% 0.42/1.04  --inst_restr_to_given                   false
% 0.42/1.04  --inst_activity_threshold               500
% 0.42/1.04  --inst_out_proof                        true
% 0.42/1.04  
% 0.42/1.04  ------ Resolution Options
% 0.42/1.04  
% 0.42/1.04  --resolution_flag                       false
% 0.42/1.04  --res_lit_sel                           adaptive
% 0.42/1.04  --res_lit_sel_side                      none
% 0.42/1.04  --res_ordering                          kbo
% 0.42/1.04  --res_to_prop_solver                    active
% 0.42/1.04  --res_prop_simpl_new                    false
% 0.42/1.04  --res_prop_simpl_given                  true
% 0.42/1.04  --res_passive_queue_type                priority_queues
% 0.42/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.42/1.04  --res_passive_queues_freq               [15;5]
% 0.42/1.04  --res_forward_subs                      full
% 0.42/1.04  --res_backward_subs                     full
% 0.42/1.04  --res_forward_subs_resolution           true
% 0.42/1.04  --res_backward_subs_resolution          true
% 0.42/1.04  --res_orphan_elimination                true
% 0.42/1.04  --res_time_limit                        2.
% 0.42/1.04  --res_out_proof                         true
% 0.42/1.04  
% 0.42/1.04  ------ Superposition Options
% 0.42/1.04  
% 0.42/1.04  --superposition_flag                    true
% 0.42/1.04  --sup_passive_queue_type                priority_queues
% 0.42/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.42/1.04  --sup_passive_queues_freq               [8;1;4]
% 0.42/1.04  --demod_completeness_check              fast
% 0.42/1.04  --demod_use_ground                      true
% 0.42/1.04  --sup_to_prop_solver                    passive
% 0.42/1.04  --sup_prop_simpl_new                    true
% 0.42/1.04  --sup_prop_simpl_given                  true
% 0.42/1.04  --sup_fun_splitting                     false
% 0.42/1.04  --sup_smt_interval                      50000
% 0.42/1.04  
% 0.42/1.04  ------ Superposition Simplification Setup
% 0.42/1.04  
% 0.42/1.04  --sup_indices_passive                   []
% 0.42/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.42/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.42/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.42/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 0.42/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.42/1.04  --sup_full_bw                           [BwDemod]
% 0.42/1.04  --sup_immed_triv                        [TrivRules]
% 0.42/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.42/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.42/1.04  --sup_immed_bw_main                     []
% 0.42/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.42/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 0.42/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.42/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.42/1.04  
% 0.42/1.04  ------ Combination Options
% 0.42/1.04  
% 0.42/1.04  --comb_res_mult                         3
% 0.42/1.04  --comb_sup_mult                         2
% 0.42/1.04  --comb_inst_mult                        10
% 0.42/1.04  
% 0.42/1.04  ------ Debug Options
% 0.42/1.04  
% 0.42/1.04  --dbg_backtrace                         false
% 0.42/1.04  --dbg_dump_prop_clauses                 false
% 0.42/1.04  --dbg_dump_prop_clauses_file            -
% 0.42/1.04  --dbg_out_stat                          false
% 0.42/1.04  
% 0.42/1.04  
% 0.42/1.04  
% 0.42/1.04  
% 0.42/1.04  ------ Proving...
% 0.42/1.04  
% 0.42/1.04  
% 0.42/1.04  % SZS status Theorem for theBenchmark.p
% 0.42/1.04  
% 0.42/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 0.42/1.04  
% 0.42/1.04  fof(f8,conjecture,(
% 0.42/1.04    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1))))),
% 0.42/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.42/1.04  
% 0.42/1.04  fof(f9,negated_conjecture,(
% 0.42/1.04    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1))))),
% 0.42/1.04    inference(negated_conjecture,[],[f8])).
% 0.42/1.04  
% 0.42/1.04  fof(f23,plain,(
% 0.42/1.04    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.42/1.04    inference(ennf_transformation,[],[f9])).
% 0.42/1.04  
% 0.42/1.04  fof(f24,plain,(
% 0.42/1.04    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.42/1.04    inference(flattening,[],[f23])).
% 0.42/1.04  
% 0.42/1.04  fof(f29,plain,(
% 0.42/1.04    ? [X0] : (? [X1] : (((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.42/1.04    inference(nnf_transformation,[],[f24])).
% 0.42/1.04  
% 0.42/1.04  fof(f30,plain,(
% 0.42/1.04    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.42/1.04    inference(flattening,[],[f29])).
% 0.42/1.04  
% 0.42/1.04  fof(f32,plain,(
% 0.42/1.04    ( ! [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,sK1) | ~v3_pre_topc(sK1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,sK1) | v3_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 0.42/1.04    introduced(choice_axiom,[])).
% 0.42/1.04  
% 0.42/1.04  fof(f31,plain,(
% 0.42/1.04    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,X1) | ~v3_pre_topc(X1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.42/1.04    introduced(choice_axiom,[])).
% 0.42/1.04  
% 0.42/1.04  fof(f33,plain,(
% 0.42/1.04    ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.42/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f32,f31])).
% 0.42/1.04  
% 0.42/1.04  fof(f53,plain,(
% 0.42/1.04    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | v3_pre_topc(sK1,sK0)),
% 0.42/1.04    inference(cnf_transformation,[],[f33])).
% 0.42/1.04  
% 0.42/1.04  fof(f52,plain,(
% 0.42/1.04    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.42/1.04    inference(cnf_transformation,[],[f33])).
% 0.42/1.04  
% 0.42/1.04  fof(f2,axiom,(
% 0.42/1.04    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 0.42/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.42/1.04  
% 0.42/1.04  fof(f12,plain,(
% 0.42/1.04    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.42/1.04    inference(ennf_transformation,[],[f2])).
% 0.42/1.04  
% 0.42/1.04  fof(f25,plain,(
% 0.42/1.04    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.42/1.04    inference(nnf_transformation,[],[f12])).
% 0.42/1.04  
% 0.42/1.04  fof(f35,plain,(
% 0.42/1.04    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.42/1.04    inference(cnf_transformation,[],[f25])).
% 0.42/1.04  
% 0.42/1.04  fof(f5,axiom,(
% 0.42/1.04    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1))))),
% 0.42/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.42/1.04  
% 0.42/1.04  fof(f17,plain,(
% 0.42/1.04    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.42/1.04    inference(ennf_transformation,[],[f5])).
% 0.42/1.04  
% 0.42/1.04  fof(f18,plain,(
% 0.42/1.04    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.42/1.04    inference(flattening,[],[f17])).
% 0.42/1.04  
% 0.42/1.04  fof(f28,plain,(
% 0.42/1.04    ! [X0] : (! [X1] : (((r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1)) & (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.42/1.04    inference(nnf_transformation,[],[f18])).
% 0.42/1.04  
% 0.42/1.04  fof(f44,plain,(
% 0.42/1.04    ( ! [X0,X1] : (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.42/1.04    inference(cnf_transformation,[],[f28])).
% 0.42/1.04  
% 0.42/1.04  fof(f49,plain,(
% 0.42/1.04    ~v2_struct_0(sK0)),
% 0.42/1.04    inference(cnf_transformation,[],[f33])).
% 0.42/1.04  
% 0.42/1.04  fof(f50,plain,(
% 0.42/1.04    v2_pre_topc(sK0)),
% 0.42/1.04    inference(cnf_transformation,[],[f33])).
% 0.42/1.04  
% 0.42/1.04  fof(f51,plain,(
% 0.42/1.04    l1_pre_topc(sK0)),
% 0.42/1.04    inference(cnf_transformation,[],[f33])).
% 0.42/1.04  
% 0.42/1.04  fof(f3,axiom,(
% 0.42/1.04    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 0.42/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.42/1.04  
% 0.42/1.04  fof(f13,plain,(
% 0.42/1.04    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.42/1.04    inference(ennf_transformation,[],[f3])).
% 0.42/1.04  
% 0.42/1.04  fof(f14,plain,(
% 0.42/1.04    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.42/1.04    inference(flattening,[],[f13])).
% 0.42/1.04  
% 0.42/1.04  fof(f26,plain,(
% 0.42/1.04    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.42/1.04    inference(nnf_transformation,[],[f14])).
% 0.42/1.04  
% 0.42/1.04  fof(f27,plain,(
% 0.42/1.04    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.42/1.04    inference(flattening,[],[f26])).
% 0.42/1.04  
% 0.42/1.04  fof(f37,plain,(
% 0.42/1.04    ( ! [X0,X1] : (v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.42/1.04    inference(cnf_transformation,[],[f27])).
% 0.42/1.04  
% 0.42/1.04  fof(f7,axiom,(
% 0.42/1.04    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) => (X1 = X2 => v3_pre_topc(X2,k6_tmap_1(X0,X1))))))),
% 0.42/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.42/1.04  
% 0.42/1.04  fof(f21,plain,(
% 0.42/1.04    ! [X0] : (! [X1] : (! [X2] : ((v3_pre_topc(X2,k6_tmap_1(X0,X1)) | X1 != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.42/1.04    inference(ennf_transformation,[],[f7])).
% 0.42/1.04  
% 0.42/1.04  fof(f22,plain,(
% 0.42/1.04    ! [X0] : (! [X1] : (! [X2] : (v3_pre_topc(X2,k6_tmap_1(X0,X1)) | X1 != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.42/1.04    inference(flattening,[],[f21])).
% 0.42/1.04  
% 0.42/1.04  fof(f48,plain,(
% 0.42/1.04    ( ! [X2,X0,X1] : (v3_pre_topc(X2,k6_tmap_1(X0,X1)) | X1 != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.42/1.04    inference(cnf_transformation,[],[f22])).
% 0.42/1.04  
% 0.42/1.04  fof(f55,plain,(
% 0.42/1.04    ( ! [X2,X0] : (v3_pre_topc(X2,k6_tmap_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.42/1.04    inference(equality_resolution,[],[f48])).
% 0.42/1.04  
% 0.42/1.04  fof(f6,axiom,(
% 0.42/1.04    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 0.42/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.42/1.04  
% 0.42/1.04  fof(f19,plain,(
% 0.42/1.04    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.42/1.04    inference(ennf_transformation,[],[f6])).
% 0.42/1.04  
% 0.42/1.04  fof(f20,plain,(
% 0.42/1.04    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.42/1.04    inference(flattening,[],[f19])).
% 0.42/1.04  
% 0.42/1.04  fof(f46,plain,(
% 0.42/1.04    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.42/1.04    inference(cnf_transformation,[],[f20])).
% 0.42/1.04  
% 0.42/1.04  fof(f39,plain,(
% 0.42/1.04    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.42/1.04    inference(cnf_transformation,[],[f27])).
% 0.42/1.04  
% 0.42/1.04  fof(f1,axiom,(
% 0.42/1.04    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 0.42/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.42/1.04  
% 0.42/1.04  fof(f10,plain,(
% 0.42/1.04    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 0.42/1.04    inference(ennf_transformation,[],[f1])).
% 0.42/1.04  
% 0.42/1.04  fof(f11,plain,(
% 0.42/1.04    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 0.42/1.04    inference(flattening,[],[f10])).
% 0.42/1.04  
% 0.42/1.04  fof(f34,plain,(
% 0.42/1.04    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 0.42/1.04    inference(cnf_transformation,[],[f11])).
% 0.42/1.04  
% 0.42/1.04  fof(f4,axiom,(
% 0.42/1.04    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))))),
% 0.42/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.42/1.04  
% 0.42/1.04  fof(f15,plain,(
% 0.42/1.04    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.42/1.04    inference(ennf_transformation,[],[f4])).
% 0.42/1.04  
% 0.42/1.04  fof(f16,plain,(
% 0.42/1.04    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.42/1.04    inference(flattening,[],[f15])).
% 0.42/1.04  
% 0.42/1.04  fof(f41,plain,(
% 0.42/1.04    ( ! [X0,X1] : (v1_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.42/1.04    inference(cnf_transformation,[],[f16])).
% 0.42/1.04  
% 0.42/1.04  fof(f43,plain,(
% 0.42/1.04    ( ! [X0,X1] : (l1_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.42/1.04    inference(cnf_transformation,[],[f16])).
% 0.42/1.04  
% 0.42/1.04  fof(f47,plain,(
% 0.42/1.04    ( ! [X0,X1] : (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.42/1.04    inference(cnf_transformation,[],[f20])).
% 0.42/1.04  
% 0.42/1.04  fof(f45,plain,(
% 0.42/1.04    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.42/1.04    inference(cnf_transformation,[],[f28])).
% 0.42/1.04  
% 0.42/1.04  fof(f36,plain,(
% 0.42/1.04    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.42/1.04    inference(cnf_transformation,[],[f25])).
% 0.42/1.04  
% 0.42/1.04  fof(f54,plain,(
% 0.42/1.04    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)),
% 0.42/1.04    inference(cnf_transformation,[],[f33])).
% 0.42/1.04  
% 0.42/1.04  cnf(c_16,negated_conjecture,
% 0.42/1.04      ( v3_pre_topc(sK1,sK0)
% 0.42/1.04      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
% 0.42/1.04      inference(cnf_transformation,[],[f53]) ).
% 0.42/1.04  
% 0.42/1.04  cnf(c_950,negated_conjecture,
% 0.42/1.04      ( v3_pre_topc(sK1,sK0)
% 0.42/1.04      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
% 0.42/1.04      inference(subtyping,[status(esa)],[c_16]) ).
% 0.42/1.04  
% 0.42/1.04  cnf(c_1403,plain,
% 0.42/1.04      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
% 0.42/1.04      | v3_pre_topc(sK1,sK0) = iProver_top ),
% 0.42/1.04      inference(predicate_to_equality,[status(thm)],[c_950]) ).
% 0.42/1.04  
% 0.42/1.04  cnf(c_17,negated_conjecture,
% 0.42/1.04      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 0.42/1.04      inference(cnf_transformation,[],[f52]) ).
% 0.42/1.04  
% 0.42/1.04  cnf(c_949,negated_conjecture,
% 0.42/1.04      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 0.42/1.04      inference(subtyping,[status(esa)],[c_17]) ).
% 0.42/1.04  
% 0.42/1.04  cnf(c_1404,plain,
% 0.42/1.04      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 0.42/1.04      inference(predicate_to_equality,[status(thm)],[c_949]) ).
% 0.42/1.04  
% 0.42/1.04  cnf(c_2,plain,
% 0.42/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.42/1.04      | r2_hidden(X0,u1_pre_topc(X1))
% 0.42/1.04      | ~ v3_pre_topc(X0,X1)
% 0.42/1.04      | ~ l1_pre_topc(X1) ),
% 0.42/1.04      inference(cnf_transformation,[],[f35]) ).
% 0.42/1.04  
% 0.42/1.04  cnf(c_11,plain,
% 0.42/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.42/1.04      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 0.42/1.04      | v2_struct_0(X1)
% 0.42/1.04      | ~ v2_pre_topc(X1)
% 0.42/1.04      | ~ l1_pre_topc(X1)
% 0.42/1.04      | k5_tmap_1(X1,X0) = u1_pre_topc(X1) ),
% 0.42/1.04      inference(cnf_transformation,[],[f44]) ).
% 0.42/1.04  
% 0.42/1.04  cnf(c_331,plain,
% 0.42/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.42/1.04      | ~ v3_pre_topc(X0,X1)
% 0.42/1.04      | v2_struct_0(X1)
% 0.42/1.04      | ~ v2_pre_topc(X1)
% 0.42/1.04      | ~ l1_pre_topc(X1)
% 0.42/1.04      | k5_tmap_1(X1,X0) = u1_pre_topc(X1) ),
% 0.42/1.04      inference(resolution,[status(thm)],[c_2,c_11]) ).
% 0.42/1.04  
% 0.42/1.04  cnf(c_20,negated_conjecture,
% 0.42/1.04      ( ~ v2_struct_0(sK0) ),
% 0.42/1.04      inference(cnf_transformation,[],[f49]) ).
% 0.42/1.04  
% 0.42/1.04  cnf(c_369,plain,
% 0.42/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.42/1.04      | ~ v3_pre_topc(X0,X1)
% 0.42/1.04      | ~ v2_pre_topc(X1)
% 0.42/1.04      | ~ l1_pre_topc(X1)
% 0.42/1.04      | k5_tmap_1(X1,X0) = u1_pre_topc(X1)
% 0.42/1.04      | sK0 != X1 ),
% 0.42/1.04      inference(resolution_lifted,[status(thm)],[c_331,c_20]) ).
% 0.42/1.04  
% 0.42/1.04  cnf(c_370,plain,
% 0.42/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.42/1.04      | ~ v3_pre_topc(X0,sK0)
% 0.42/1.04      | ~ v2_pre_topc(sK0)
% 0.42/1.04      | ~ l1_pre_topc(sK0)
% 0.42/1.04      | k5_tmap_1(sK0,X0) = u1_pre_topc(sK0) ),
% 0.42/1.04      inference(unflattening,[status(thm)],[c_369]) ).
% 0.42/1.04  
% 0.42/1.04  cnf(c_19,negated_conjecture,
% 0.42/1.04      ( v2_pre_topc(sK0) ),
% 0.42/1.04      inference(cnf_transformation,[],[f50]) ).
% 0.42/1.04  
% 0.42/1.04  cnf(c_18,negated_conjecture,
% 0.42/1.04      ( l1_pre_topc(sK0) ),
% 0.42/1.04      inference(cnf_transformation,[],[f51]) ).
% 0.42/1.04  
% 0.42/1.04  cnf(c_374,plain,
% 0.42/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.42/1.04      | ~ v3_pre_topc(X0,sK0)
% 0.42/1.04      | k5_tmap_1(sK0,X0) = u1_pre_topc(sK0) ),
% 0.42/1.04      inference(global_propositional_subsumption,
% 0.42/1.04                [status(thm)],
% 0.42/1.04                [c_370,c_19,c_18]) ).
% 0.42/1.04  
% 0.42/1.04  cnf(c_948,plain,
% 0.42/1.04      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.42/1.04      | ~ v3_pre_topc(X0_43,sK0)
% 0.42/1.04      | k5_tmap_1(sK0,X0_43) = u1_pre_topc(sK0) ),
% 0.42/1.04      inference(subtyping,[status(esa)],[c_374]) ).
% 0.42/1.04  
% 0.42/1.04  cnf(c_1405,plain,
% 0.42/1.04      ( k5_tmap_1(sK0,X0_43) = u1_pre_topc(sK0)
% 0.42/1.04      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 0.42/1.04      | v3_pre_topc(X0_43,sK0) != iProver_top ),
% 0.42/1.04      inference(predicate_to_equality,[status(thm)],[c_948]) ).
% 0.42/1.04  
% 0.42/1.04  cnf(c_1614,plain,
% 0.42/1.04      ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
% 0.42/1.04      | v3_pre_topc(sK1,sK0) != iProver_top ),
% 0.42/1.04      inference(superposition,[status(thm)],[c_1404,c_1405]) ).
% 0.42/1.04  
% 0.42/1.04  cnf(c_1648,plain,
% 0.42/1.04      ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
% 0.42/1.04      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
% 0.42/1.04      inference(superposition,[status(thm)],[c_1403,c_1614]) ).
% 0.42/1.04  
% 0.42/1.04  cnf(c_6,plain,
% 0.42/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.42/1.04      | ~ v3_pre_topc(X0,X1)
% 0.42/1.04      | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 0.42/1.04      | ~ v2_pre_topc(X1)
% 0.42/1.04      | ~ l1_pre_topc(X1) ),
% 0.42/1.04      inference(cnf_transformation,[],[f37]) ).
% 0.42/1.04  
% 0.42/1.04  cnf(c_570,plain,
% 0.42/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.30/1.04      | ~ v3_pre_topc(X0,X1)
% 1.30/1.04      | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 1.30/1.04      | ~ v2_pre_topc(X1)
% 1.30/1.04      | sK0 != X1 ),
% 1.30/1.04      inference(resolution_lifted,[status(thm)],[c_6,c_18]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_571,plain,
% 1.30/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.30/1.04      | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 1.30/1.04      | ~ v3_pre_topc(X0,sK0)
% 1.30/1.04      | ~ v2_pre_topc(sK0) ),
% 1.30/1.04      inference(unflattening,[status(thm)],[c_570]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_575,plain,
% 1.30/1.04      ( ~ v3_pre_topc(X0,sK0)
% 1.30/1.04      | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 1.30/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.30/1.04      inference(global_propositional_subsumption,
% 1.30/1.04                [status(thm)],
% 1.30/1.04                [c_571,c_19]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_576,plain,
% 1.30/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.30/1.04      | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 1.30/1.04      | ~ v3_pre_topc(X0,sK0) ),
% 1.30/1.04      inference(renaming,[status(thm)],[c_575]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_942,plain,
% 1.30/1.04      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.30/1.04      | v3_pre_topc(X0_43,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 1.30/1.04      | ~ v3_pre_topc(X0_43,sK0) ),
% 1.30/1.04      inference(subtyping,[status(esa)],[c_576]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_1411,plain,
% 1.30/1.04      ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.30/1.04      | v3_pre_topc(X0_43,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
% 1.30/1.04      | v3_pre_topc(X0_43,sK0) != iProver_top ),
% 1.30/1.04      inference(predicate_to_equality,[status(thm)],[c_942]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_1776,plain,
% 1.30/1.04      ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
% 1.30/1.04      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.30/1.04      | v3_pre_topc(X0_43,k6_tmap_1(sK0,sK1)) = iProver_top
% 1.30/1.04      | v3_pre_topc(X0_43,sK0) != iProver_top ),
% 1.30/1.04      inference(superposition,[status(thm)],[c_1648,c_1411]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_14,plain,
% 1.30/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.30/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X0))))
% 1.30/1.04      | v3_pre_topc(X0,k6_tmap_1(X1,X0))
% 1.30/1.04      | v2_struct_0(X1)
% 1.30/1.04      | ~ v2_pre_topc(X1)
% 1.30/1.04      | ~ l1_pre_topc(X1) ),
% 1.30/1.04      inference(cnf_transformation,[],[f55]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_411,plain,
% 1.30/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.30/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X0))))
% 1.30/1.04      | v3_pre_topc(X0,k6_tmap_1(X1,X0))
% 1.30/1.04      | ~ v2_pre_topc(X1)
% 1.30/1.04      | ~ l1_pre_topc(X1)
% 1.30/1.04      | sK0 != X1 ),
% 1.30/1.04      inference(resolution_lifted,[status(thm)],[c_14,c_20]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_412,plain,
% 1.30/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X0))))
% 1.30/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.30/1.04      | v3_pre_topc(X0,k6_tmap_1(sK0,X0))
% 1.30/1.04      | ~ v2_pre_topc(sK0)
% 1.30/1.04      | ~ l1_pre_topc(sK0) ),
% 1.30/1.04      inference(unflattening,[status(thm)],[c_411]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_416,plain,
% 1.30/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X0))))
% 1.30/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.30/1.04      | v3_pre_topc(X0,k6_tmap_1(sK0,X0)) ),
% 1.30/1.04      inference(global_propositional_subsumption,
% 1.30/1.04                [status(thm)],
% 1.30/1.04                [c_412,c_19,c_18]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_946,plain,
% 1.30/1.04      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X0_43))))
% 1.30/1.04      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.30/1.04      | v3_pre_topc(X0_43,k6_tmap_1(sK0,X0_43)) ),
% 1.30/1.04      inference(subtyping,[status(esa)],[c_416]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_991,plain,
% 1.30/1.04      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
% 1.30/1.04      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.30/1.04      | v3_pre_topc(sK1,k6_tmap_1(sK0,sK1)) ),
% 1.30/1.04      inference(instantiation,[status(thm)],[c_946]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_13,plain,
% 1.30/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.30/1.04      | v2_struct_0(X1)
% 1.30/1.04      | ~ v2_pre_topc(X1)
% 1.30/1.04      | ~ l1_pre_topc(X1)
% 1.30/1.04      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
% 1.30/1.04      inference(cnf_transformation,[],[f46]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_432,plain,
% 1.30/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.30/1.04      | ~ v2_pre_topc(X1)
% 1.30/1.04      | ~ l1_pre_topc(X1)
% 1.30/1.04      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1)
% 1.30/1.04      | sK0 != X1 ),
% 1.30/1.04      inference(resolution_lifted,[status(thm)],[c_13,c_20]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_433,plain,
% 1.30/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.30/1.04      | ~ v2_pre_topc(sK0)
% 1.30/1.04      | ~ l1_pre_topc(sK0)
% 1.30/1.04      | u1_struct_0(k6_tmap_1(sK0,X0)) = u1_struct_0(sK0) ),
% 1.30/1.04      inference(unflattening,[status(thm)],[c_432]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_437,plain,
% 1.30/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.30/1.04      | u1_struct_0(k6_tmap_1(sK0,X0)) = u1_struct_0(sK0) ),
% 1.30/1.04      inference(global_propositional_subsumption,
% 1.30/1.04                [status(thm)],
% 1.30/1.04                [c_433,c_19,c_18]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_945,plain,
% 1.30/1.04      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.30/1.04      | u1_struct_0(k6_tmap_1(sK0,X0_43)) = u1_struct_0(sK0) ),
% 1.30/1.04      inference(subtyping,[status(esa)],[c_437]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_994,plain,
% 1.30/1.04      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.30/1.04      | u1_struct_0(k6_tmap_1(sK0,sK1)) = u1_struct_0(sK0) ),
% 1.30/1.04      inference(instantiation,[status(thm)],[c_945]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_965,plain,
% 1.30/1.04      ( ~ m1_subset_1(X0_43,X0_44)
% 1.30/1.04      | m1_subset_1(X0_43,X1_44)
% 1.30/1.04      | X1_44 != X0_44 ),
% 1.30/1.04      theory(equality) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_1563,plain,
% 1.30/1.04      ( m1_subset_1(sK1,X0_44)
% 1.30/1.04      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.30/1.04      | X0_44 != k1_zfmisc_1(u1_struct_0(sK0)) ),
% 1.30/1.04      inference(instantiation,[status(thm)],[c_965]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_1579,plain,
% 1.30/1.04      ( m1_subset_1(sK1,k1_zfmisc_1(X0_45))
% 1.30/1.04      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.30/1.04      | k1_zfmisc_1(X0_45) != k1_zfmisc_1(u1_struct_0(sK0)) ),
% 1.30/1.04      inference(instantiation,[status(thm)],[c_1563]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_1593,plain,
% 1.30/1.04      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
% 1.30/1.04      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.30/1.04      | k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))) != k1_zfmisc_1(u1_struct_0(sK0)) ),
% 1.30/1.04      inference(instantiation,[status(thm)],[c_1579]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_1615,plain,
% 1.30/1.04      ( ~ v3_pre_topc(sK1,sK0) | k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0) ),
% 1.30/1.04      inference(predicate_to_equality_rev,[status(thm)],[c_1614]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_964,plain,
% 1.30/1.04      ( X0_45 != X1_45 | k1_zfmisc_1(X0_45) = k1_zfmisc_1(X1_45) ),
% 1.30/1.04      theory(equality) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_1580,plain,
% 1.30/1.04      ( X0_45 != u1_struct_0(sK0)
% 1.30/1.04      | k1_zfmisc_1(X0_45) = k1_zfmisc_1(u1_struct_0(sK0)) ),
% 1.30/1.04      inference(instantiation,[status(thm)],[c_964]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_1627,plain,
% 1.30/1.04      ( u1_struct_0(k6_tmap_1(sK0,X0_43)) != u1_struct_0(sK0)
% 1.30/1.04      | k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X0_43))) = k1_zfmisc_1(u1_struct_0(sK0)) ),
% 1.30/1.04      inference(instantiation,[status(thm)],[c_1580]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_1628,plain,
% 1.30/1.04      ( u1_struct_0(k6_tmap_1(sK0,sK1)) != u1_struct_0(sK0)
% 1.30/1.04      | k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))) = k1_zfmisc_1(u1_struct_0(sK0)) ),
% 1.30/1.04      inference(instantiation,[status(thm)],[c_1627]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_963,plain,
% 1.30/1.04      ( ~ v3_pre_topc(X0_43,X0_46)
% 1.30/1.04      | v3_pre_topc(X0_43,X1_46)
% 1.30/1.04      | X1_46 != X0_46 ),
% 1.30/1.04      theory(equality) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_1684,plain,
% 1.30/1.04      ( v3_pre_topc(X0_43,X0_46)
% 1.30/1.04      | ~ v3_pre_topc(X0_43,k6_tmap_1(sK0,X0_43))
% 1.30/1.04      | X0_46 != k6_tmap_1(sK0,X0_43) ),
% 1.30/1.04      inference(instantiation,[status(thm)],[c_963]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_1711,plain,
% 1.30/1.04      ( ~ v3_pre_topc(sK1,k6_tmap_1(sK0,sK1))
% 1.30/1.04      | v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 1.30/1.04      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
% 1.30/1.04      inference(instantiation,[status(thm)],[c_1684]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_4,plain,
% 1.30/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
% 1.30/1.04      | v3_pre_topc(X0,X1)
% 1.30/1.04      | ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 1.30/1.04      | ~ v2_pre_topc(X1)
% 1.30/1.04      | ~ l1_pre_topc(X1) ),
% 1.30/1.04      inference(cnf_transformation,[],[f39]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_612,plain,
% 1.30/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
% 1.30/1.04      | v3_pre_topc(X0,X1)
% 1.30/1.04      | ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 1.30/1.04      | ~ v2_pre_topc(X1)
% 1.30/1.04      | sK0 != X1 ),
% 1.30/1.04      inference(resolution_lifted,[status(thm)],[c_4,c_18]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_613,plain,
% 1.30/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
% 1.30/1.04      | ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 1.30/1.04      | v3_pre_topc(X0,sK0)
% 1.30/1.04      | ~ v2_pre_topc(sK0) ),
% 1.30/1.04      inference(unflattening,[status(thm)],[c_612]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_617,plain,
% 1.30/1.04      ( v3_pre_topc(X0,sK0)
% 1.30/1.04      | ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 1.30/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
% 1.30/1.04      inference(global_propositional_subsumption,
% 1.30/1.04                [status(thm)],
% 1.30/1.04                [c_613,c_19]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_618,plain,
% 1.30/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
% 1.30/1.04      | ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 1.30/1.04      | v3_pre_topc(X0,sK0) ),
% 1.30/1.04      inference(renaming,[status(thm)],[c_617]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_940,plain,
% 1.30/1.04      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
% 1.30/1.04      | ~ v3_pre_topc(X0_43,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 1.30/1.04      | v3_pre_topc(X0_43,sK0) ),
% 1.30/1.04      inference(subtyping,[status(esa)],[c_618]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_1413,plain,
% 1.30/1.04      ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) != iProver_top
% 1.30/1.04      | v3_pre_topc(X0_43,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 1.30/1.04      | v3_pre_topc(X0_43,sK0) = iProver_top ),
% 1.30/1.04      inference(predicate_to_equality,[status(thm)],[c_940]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_1902,plain,
% 1.30/1.04      ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
% 1.30/1.04      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) != iProver_top
% 1.30/1.04      | v3_pre_topc(X0_43,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 1.30/1.04      | v3_pre_topc(X0_43,sK0) = iProver_top ),
% 1.30/1.04      inference(superposition,[status(thm)],[c_1648,c_1413]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_1408,plain,
% 1.30/1.04      ( u1_struct_0(k6_tmap_1(sK0,X0_43)) = u1_struct_0(sK0)
% 1.30/1.04      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.30/1.04      inference(predicate_to_equality,[status(thm)],[c_945]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_1562,plain,
% 1.30/1.04      ( u1_struct_0(k6_tmap_1(sK0,sK1)) = u1_struct_0(sK0) ),
% 1.30/1.04      inference(superposition,[status(thm)],[c_1404,c_1408]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_1907,plain,
% 1.30/1.04      ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
% 1.30/1.04      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.30/1.04      | v3_pre_topc(X0_43,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 1.30/1.04      | v3_pre_topc(X0_43,sK0) = iProver_top ),
% 1.30/1.04      inference(light_normalisation,[status(thm)],[c_1902,c_1562]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_1912,plain,
% 1.30/1.04      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.30/1.04      | ~ v3_pre_topc(X0_43,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 1.30/1.04      | v3_pre_topc(X0_43,sK0)
% 1.30/1.04      | k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0) ),
% 1.30/1.04      inference(predicate_to_equality_rev,[status(thm)],[c_1907]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_1914,plain,
% 1.30/1.04      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.30/1.04      | ~ v3_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 1.30/1.04      | v3_pre_topc(sK1,sK0)
% 1.30/1.04      | k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0) ),
% 1.30/1.04      inference(instantiation,[status(thm)],[c_1912]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_2095,plain,
% 1.30/1.04      ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0) ),
% 1.30/1.04      inference(global_propositional_subsumption,
% 1.30/1.04                [status(thm)],
% 1.30/1.04                [c_1776,c_17,c_991,c_994,c_1593,c_1615,c_1628,c_1648,
% 1.30/1.04                 c_1711,c_1914]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_0,plain,
% 1.30/1.04      ( ~ l1_pre_topc(X0)
% 1.30/1.04      | ~ v1_pre_topc(X0)
% 1.30/1.04      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 1.30/1.04      inference(cnf_transformation,[],[f34]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_9,plain,
% 1.30/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.30/1.04      | v2_struct_0(X1)
% 1.30/1.04      | ~ v2_pre_topc(X1)
% 1.30/1.04      | ~ l1_pre_topc(X1)
% 1.30/1.04      | v1_pre_topc(k6_tmap_1(X1,X0)) ),
% 1.30/1.04      inference(cnf_transformation,[],[f41]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_468,plain,
% 1.30/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.30/1.04      | ~ v2_pre_topc(X1)
% 1.30/1.04      | ~ l1_pre_topc(X1)
% 1.30/1.04      | v1_pre_topc(k6_tmap_1(X1,X0))
% 1.30/1.04      | sK0 != X1 ),
% 1.30/1.04      inference(resolution_lifted,[status(thm)],[c_9,c_20]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_469,plain,
% 1.30/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.30/1.04      | ~ v2_pre_topc(sK0)
% 1.30/1.04      | ~ l1_pre_topc(sK0)
% 1.30/1.04      | v1_pre_topc(k6_tmap_1(sK0,X0)) ),
% 1.30/1.04      inference(unflattening,[status(thm)],[c_468]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_473,plain,
% 1.30/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.30/1.04      | v1_pre_topc(k6_tmap_1(sK0,X0)) ),
% 1.30/1.04      inference(global_propositional_subsumption,
% 1.30/1.04                [status(thm)],
% 1.30/1.04                [c_469,c_19,c_18]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_549,plain,
% 1.30/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.30/1.04      | ~ l1_pre_topc(X1)
% 1.30/1.04      | k6_tmap_1(sK0,X0) != X1
% 1.30/1.04      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X1 ),
% 1.30/1.04      inference(resolution_lifted,[status(thm)],[c_0,c_473]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_550,plain,
% 1.30/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.30/1.04      | ~ l1_pre_topc(k6_tmap_1(sK0,X0))
% 1.30/1.04      | g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X0)),u1_pre_topc(k6_tmap_1(sK0,X0))) = k6_tmap_1(sK0,X0) ),
% 1.30/1.04      inference(unflattening,[status(thm)],[c_549]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_7,plain,
% 1.30/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.30/1.04      | v2_struct_0(X1)
% 1.30/1.04      | ~ v2_pre_topc(X1)
% 1.30/1.04      | ~ l1_pre_topc(X1)
% 1.30/1.04      | l1_pre_topc(k6_tmap_1(X1,X0)) ),
% 1.30/1.04      inference(cnf_transformation,[],[f43]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_504,plain,
% 1.30/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.30/1.04      | ~ v2_pre_topc(X1)
% 1.30/1.04      | ~ l1_pre_topc(X1)
% 1.30/1.04      | l1_pre_topc(k6_tmap_1(X1,X0))
% 1.30/1.04      | sK0 != X1 ),
% 1.30/1.04      inference(resolution_lifted,[status(thm)],[c_7,c_20]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_505,plain,
% 1.30/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.30/1.04      | ~ v2_pre_topc(sK0)
% 1.30/1.04      | l1_pre_topc(k6_tmap_1(sK0,X0))
% 1.30/1.04      | ~ l1_pre_topc(sK0) ),
% 1.30/1.04      inference(unflattening,[status(thm)],[c_504]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_554,plain,
% 1.30/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.30/1.04      | g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X0)),u1_pre_topc(k6_tmap_1(sK0,X0))) = k6_tmap_1(sK0,X0) ),
% 1.30/1.04      inference(global_propositional_subsumption,
% 1.30/1.04                [status(thm)],
% 1.30/1.04                [c_550,c_19,c_18,c_505]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_943,plain,
% 1.30/1.04      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.30/1.04      | g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X0_43)),u1_pre_topc(k6_tmap_1(sK0,X0_43))) = k6_tmap_1(sK0,X0_43) ),
% 1.30/1.04      inference(subtyping,[status(esa)],[c_554]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_1410,plain,
% 1.30/1.04      ( g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X0_43)),u1_pre_topc(k6_tmap_1(sK0,X0_43))) = k6_tmap_1(sK0,X0_43)
% 1.30/1.04      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.30/1.04      inference(predicate_to_equality,[status(thm)],[c_943]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_1700,plain,
% 1.30/1.04      ( g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_pre_topc(k6_tmap_1(sK0,sK1))) = k6_tmap_1(sK0,sK1) ),
% 1.30/1.04      inference(superposition,[status(thm)],[c_1404,c_1410]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_12,plain,
% 1.30/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.30/1.04      | v2_struct_0(X1)
% 1.30/1.04      | ~ v2_pre_topc(X1)
% 1.30/1.04      | ~ l1_pre_topc(X1)
% 1.30/1.04      | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0) ),
% 1.30/1.04      inference(cnf_transformation,[],[f47]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_450,plain,
% 1.30/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.30/1.04      | ~ v2_pre_topc(X1)
% 1.30/1.04      | ~ l1_pre_topc(X1)
% 1.30/1.04      | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0)
% 1.30/1.04      | sK0 != X1 ),
% 1.30/1.04      inference(resolution_lifted,[status(thm)],[c_12,c_20]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_451,plain,
% 1.30/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.30/1.04      | ~ v2_pre_topc(sK0)
% 1.30/1.04      | ~ l1_pre_topc(sK0)
% 1.30/1.04      | u1_pre_topc(k6_tmap_1(sK0,X0)) = k5_tmap_1(sK0,X0) ),
% 1.30/1.04      inference(unflattening,[status(thm)],[c_450]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_455,plain,
% 1.30/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.30/1.04      | u1_pre_topc(k6_tmap_1(sK0,X0)) = k5_tmap_1(sK0,X0) ),
% 1.30/1.04      inference(global_propositional_subsumption,
% 1.30/1.04                [status(thm)],
% 1.30/1.04                [c_451,c_19,c_18]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_944,plain,
% 1.30/1.04      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.30/1.04      | u1_pre_topc(k6_tmap_1(sK0,X0_43)) = k5_tmap_1(sK0,X0_43) ),
% 1.30/1.04      inference(subtyping,[status(esa)],[c_455]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_1409,plain,
% 1.30/1.04      ( u1_pre_topc(k6_tmap_1(sK0,X0_43)) = k5_tmap_1(sK0,X0_43)
% 1.30/1.04      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.30/1.04      inference(predicate_to_equality,[status(thm)],[c_944]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_1577,plain,
% 1.30/1.04      ( u1_pre_topc(k6_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,sK1) ),
% 1.30/1.04      inference(superposition,[status(thm)],[c_1404,c_1409]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_1701,plain,
% 1.30/1.04      ( g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) = k6_tmap_1(sK0,sK1) ),
% 1.30/1.04      inference(light_normalisation,[status(thm)],[c_1700,c_1562,c_1577]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_2098,plain,
% 1.30/1.04      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
% 1.30/1.04      inference(demodulation,[status(thm)],[c_2095,c_1701]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_10,plain,
% 1.30/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.30/1.04      | r2_hidden(X0,u1_pre_topc(X1))
% 1.30/1.04      | v2_struct_0(X1)
% 1.30/1.04      | ~ v2_pre_topc(X1)
% 1.30/1.04      | ~ l1_pre_topc(X1)
% 1.30/1.04      | k5_tmap_1(X1,X0) != u1_pre_topc(X1) ),
% 1.30/1.04      inference(cnf_transformation,[],[f45]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_1,plain,
% 1.30/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.30/1.04      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 1.30/1.04      | v3_pre_topc(X0,X1)
% 1.30/1.04      | ~ l1_pre_topc(X1) ),
% 1.30/1.04      inference(cnf_transformation,[],[f36]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_308,plain,
% 1.30/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.30/1.04      | v3_pre_topc(X0,X1)
% 1.30/1.04      | v2_struct_0(X1)
% 1.30/1.04      | ~ v2_pre_topc(X1)
% 1.30/1.04      | ~ l1_pre_topc(X1)
% 1.30/1.04      | k5_tmap_1(X1,X0) != u1_pre_topc(X1) ),
% 1.30/1.04      inference(resolution,[status(thm)],[c_10,c_1]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_390,plain,
% 1.30/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.30/1.04      | v3_pre_topc(X0,X1)
% 1.30/1.04      | ~ v2_pre_topc(X1)
% 1.30/1.04      | ~ l1_pre_topc(X1)
% 1.30/1.04      | k5_tmap_1(X1,X0) != u1_pre_topc(X1)
% 1.30/1.04      | sK0 != X1 ),
% 1.30/1.04      inference(resolution_lifted,[status(thm)],[c_308,c_20]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_391,plain,
% 1.30/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.30/1.04      | v3_pre_topc(X0,sK0)
% 1.30/1.04      | ~ v2_pre_topc(sK0)
% 1.30/1.04      | ~ l1_pre_topc(sK0)
% 1.30/1.04      | k5_tmap_1(sK0,X0) != u1_pre_topc(sK0) ),
% 1.30/1.04      inference(unflattening,[status(thm)],[c_390]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_395,plain,
% 1.30/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.30/1.04      | v3_pre_topc(X0,sK0)
% 1.30/1.04      | k5_tmap_1(sK0,X0) != u1_pre_topc(sK0) ),
% 1.30/1.04      inference(global_propositional_subsumption,
% 1.30/1.04                [status(thm)],
% 1.30/1.04                [c_391,c_19,c_18]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_947,plain,
% 1.30/1.04      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.30/1.04      | v3_pre_topc(X0_43,sK0)
% 1.30/1.04      | k5_tmap_1(sK0,X0_43) != u1_pre_topc(sK0) ),
% 1.30/1.04      inference(subtyping,[status(esa)],[c_395]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_988,plain,
% 1.30/1.04      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.30/1.04      | v3_pre_topc(sK1,sK0)
% 1.30/1.04      | k5_tmap_1(sK0,sK1) != u1_pre_topc(sK0) ),
% 1.30/1.04      inference(instantiation,[status(thm)],[c_947]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_15,negated_conjecture,
% 1.30/1.04      ( ~ v3_pre_topc(sK1,sK0)
% 1.30/1.04      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
% 1.30/1.04      inference(cnf_transformation,[],[f54]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(c_951,negated_conjecture,
% 1.30/1.04      ( ~ v3_pre_topc(sK1,sK0)
% 1.30/1.04      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
% 1.30/1.04      inference(subtyping,[status(esa)],[c_15]) ).
% 1.30/1.04  
% 1.30/1.04  cnf(contradiction,plain,
% 1.30/1.04      ( $false ),
% 1.30/1.04      inference(minisat,[status(thm)],[c_2098,c_2095,c_988,c_951,c_17]) ).
% 1.30/1.04  
% 1.30/1.04  
% 1.30/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 1.30/1.04  
% 1.30/1.04  ------                               Statistics
% 1.30/1.04  
% 1.30/1.04  ------ General
% 1.30/1.04  
% 1.30/1.04  abstr_ref_over_cycles:                  0
% 1.30/1.04  abstr_ref_under_cycles:                 0
% 1.30/1.04  gc_basic_clause_elim:                   0
% 1.30/1.04  forced_gc_time:                         0
% 1.30/1.04  parsing_time:                           0.008
% 1.30/1.04  unif_index_cands_time:                  0.
% 1.30/1.04  unif_index_add_time:                    0.
% 1.30/1.04  orderings_time:                         0.
% 1.30/1.04  out_proof_time:                         0.01
% 1.30/1.04  total_time:                             0.067
% 1.30/1.04  num_of_symbols:                         48
% 1.30/1.04  num_of_terms:                           1188
% 1.30/1.04  
% 1.30/1.04  ------ Preprocessing
% 1.30/1.04  
% 1.30/1.04  num_of_splits:                          0
% 1.30/1.04  num_of_split_atoms:                     0
% 1.30/1.04  num_of_reused_defs:                     0
% 1.30/1.04  num_eq_ax_congr_red:                    8
% 1.30/1.04  num_of_sem_filtered_clauses:            1
% 1.30/1.04  num_of_subtypes:                        5
% 1.30/1.04  monotx_restored_types:                  0
% 1.30/1.04  sat_num_of_epr_types:                   0
% 1.30/1.04  sat_num_of_non_cyclic_types:            0
% 1.30/1.04  sat_guarded_non_collapsed_types:        0
% 1.30/1.04  num_pure_diseq_elim:                    0
% 1.30/1.04  simp_replaced_by:                       0
% 1.30/1.04  res_preprocessed:                       103
% 1.30/1.04  prep_upred:                             0
% 1.30/1.04  prep_unflattend:                        18
% 1.30/1.04  smt_new_axioms:                         0
% 1.30/1.04  pred_elim_cands:                        2
% 1.30/1.04  pred_elim:                              5
% 1.30/1.04  pred_elim_cl:                           4
% 1.30/1.04  pred_elim_cycles:                       8
% 1.30/1.04  merged_defs:                            8
% 1.30/1.04  merged_defs_ncl:                        0
% 1.30/1.04  bin_hyper_res:                          8
% 1.30/1.04  prep_cycles:                            4
% 1.30/1.04  pred_elim_time:                         0.006
% 1.30/1.04  splitting_time:                         0.
% 1.30/1.04  sem_filter_time:                        0.
% 1.30/1.04  monotx_time:                            0.
% 1.30/1.04  subtype_inf_time:                       0.
% 1.30/1.04  
% 1.30/1.04  ------ Problem properties
% 1.30/1.04  
% 1.30/1.04  clauses:                                17
% 1.30/1.04  conjectures:                            3
% 1.30/1.04  epr:                                    0
% 1.30/1.04  horn:                                   16
% 1.30/1.04  ground:                                 3
% 1.30/1.04  unary:                                  1
% 1.30/1.04  binary:                                 5
% 1.30/1.04  lits:                                   48
% 1.30/1.04  lits_eq:                                7
% 1.30/1.04  fd_pure:                                0
% 1.30/1.04  fd_pseudo:                              0
% 1.30/1.04  fd_cond:                                0
% 1.30/1.04  fd_pseudo_cond:                         0
% 1.30/1.04  ac_symbols:                             0
% 1.30/1.04  
% 1.30/1.04  ------ Propositional Solver
% 1.30/1.04  
% 1.30/1.04  prop_solver_calls:                      28
% 1.30/1.04  prop_fast_solver_calls:                 771
% 1.30/1.04  smt_solver_calls:                       0
% 1.30/1.04  smt_fast_solver_calls:                  0
% 1.30/1.04  prop_num_of_clauses:                    518
% 1.30/1.04  prop_preprocess_simplified:             3120
% 1.30/1.04  prop_fo_subsumed:                       26
% 1.30/1.04  prop_solver_time:                       0.
% 1.30/1.04  smt_solver_time:                        0.
% 1.30/1.04  smt_fast_solver_time:                   0.
% 1.30/1.04  prop_fast_solver_time:                  0.
% 1.30/1.04  prop_unsat_core_time:                   0.
% 1.30/1.04  
% 1.30/1.04  ------ QBF
% 1.30/1.04  
% 1.30/1.04  qbf_q_res:                              0
% 1.30/1.04  qbf_num_tautologies:                    0
% 1.30/1.04  qbf_prep_cycles:                        0
% 1.30/1.04  
% 1.30/1.04  ------ BMC1
% 1.30/1.04  
% 1.30/1.04  bmc1_current_bound:                     -1
% 1.30/1.04  bmc1_last_solved_bound:                 -1
% 1.30/1.04  bmc1_unsat_core_size:                   -1
% 1.30/1.04  bmc1_unsat_core_parents_size:           -1
% 1.30/1.04  bmc1_merge_next_fun:                    0
% 1.30/1.04  bmc1_unsat_core_clauses_time:           0.
% 1.30/1.04  
% 1.30/1.04  ------ Instantiation
% 1.30/1.04  
% 1.30/1.04  inst_num_of_clauses:                    138
% 1.30/1.04  inst_num_in_passive:                    42
% 1.30/1.04  inst_num_in_active:                     95
% 1.30/1.04  inst_num_in_unprocessed:                1
% 1.30/1.04  inst_num_of_loops:                      120
% 1.30/1.04  inst_num_of_learning_restarts:          0
% 1.30/1.04  inst_num_moves_active_passive:          20
% 1.30/1.04  inst_lit_activity:                      0
% 1.30/1.04  inst_lit_activity_moves:                0
% 1.30/1.04  inst_num_tautologies:                   0
% 1.30/1.04  inst_num_prop_implied:                  0
% 1.30/1.04  inst_num_existing_simplified:           0
% 1.30/1.04  inst_num_eq_res_simplified:             0
% 1.30/1.04  inst_num_child_elim:                    0
% 1.30/1.04  inst_num_of_dismatching_blockings:      24
% 1.30/1.04  inst_num_of_non_proper_insts:           117
% 1.30/1.04  inst_num_of_duplicates:                 0
% 1.30/1.04  inst_inst_num_from_inst_to_res:         0
% 1.30/1.04  inst_dismatching_checking_time:         0.
% 1.30/1.04  
% 1.30/1.04  ------ Resolution
% 1.30/1.04  
% 1.30/1.04  res_num_of_clauses:                     0
% 1.30/1.04  res_num_in_passive:                     0
% 1.30/1.04  res_num_in_active:                      0
% 1.30/1.04  res_num_of_loops:                       107
% 1.30/1.04  res_forward_subset_subsumed:            18
% 1.30/1.04  res_backward_subset_subsumed:           0
% 1.30/1.04  res_forward_subsumed:                   0
% 1.30/1.04  res_backward_subsumed:                  0
% 1.30/1.04  res_forward_subsumption_resolution:     4
% 1.30/1.04  res_backward_subsumption_resolution:    0
% 1.30/1.04  res_clause_to_clause_subsumption:       38
% 1.30/1.04  res_orphan_elimination:                 0
% 1.30/1.04  res_tautology_del:                      54
% 1.30/1.04  res_num_eq_res_simplified:              0
% 1.30/1.04  res_num_sel_changes:                    0
% 1.30/1.04  res_moves_from_active_to_pass:          0
% 1.30/1.04  
% 1.30/1.04  ------ Superposition
% 1.30/1.04  
% 1.30/1.04  sup_time_total:                         0.
% 1.30/1.04  sup_time_generating:                    0.
% 1.30/1.04  sup_time_sim_full:                      0.
% 1.30/1.04  sup_time_sim_immed:                     0.
% 1.30/1.04  
% 1.30/1.04  sup_num_of_clauses:                     20
% 1.30/1.04  sup_num_in_active:                      17
% 1.30/1.04  sup_num_in_passive:                     3
% 1.30/1.04  sup_num_of_loops:                       22
% 1.30/1.04  sup_fw_superposition:                   19
% 1.30/1.04  sup_bw_superposition:                   1
% 1.30/1.04  sup_immediate_simplified:               10
% 1.30/1.04  sup_given_eliminated:                   0
% 1.30/1.04  comparisons_done:                       0
% 1.30/1.04  comparisons_avoided:                    3
% 1.30/1.04  
% 1.30/1.04  ------ Simplifications
% 1.30/1.04  
% 1.30/1.04  
% 1.30/1.04  sim_fw_subset_subsumed:                 0
% 1.30/1.04  sim_bw_subset_subsumed:                 4
% 1.30/1.04  sim_fw_subsumed:                        0
% 1.30/1.04  sim_bw_subsumed:                        0
% 1.30/1.04  sim_fw_subsumption_res:                 0
% 1.30/1.04  sim_bw_subsumption_res:                 0
% 1.30/1.04  sim_tautology_del:                      11
% 1.30/1.04  sim_eq_tautology_del:                   0
% 1.30/1.04  sim_eq_res_simp:                        0
% 1.30/1.04  sim_fw_demodulated:                     0
% 1.30/1.04  sim_bw_demodulated:                     2
% 1.30/1.04  sim_light_normalised:                   10
% 1.30/1.04  sim_joinable_taut:                      0
% 1.30/1.04  sim_joinable_simp:                      0
% 1.30/1.04  sim_ac_normalised:                      0
% 1.30/1.04  sim_smt_subsumption:                    0
% 1.30/1.04  
%------------------------------------------------------------------------------
