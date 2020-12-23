%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:53 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :  185 (1682 expanded)
%              Number of clauses        :  118 ( 456 expanded)
%              Number of leaves         :   18 ( 363 expanded)
%              Depth                    :   22
%              Number of atoms          :  716 (9932 expanded)
%              Number of equality atoms :  194 (2439 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,sK2)
          | ~ v3_pre_topc(sK2,X0) )
        & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,sK2)
          | v3_pre_topc(sK2,X0) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
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
          ( ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k6_tmap_1(sK1,X1)
            | ~ v3_pre_topc(X1,sK1) )
          & ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,X1)
            | v3_pre_topc(X1,sK1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k6_tmap_1(sK1,sK2)
      | ~ v3_pre_topc(sK2,sK1) )
    & ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,sK2)
      | v3_pre_topc(sK2,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f45,f47,f46])).

fof(f74,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,sK2)
    | v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f73,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f48])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f72,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f66,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(X0) = k5_tmap_1(X0,X1)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f70,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f71,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            & v1_tops_2(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            & v1_tops_2(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            & v1_tops_2(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              & v1_tops_2(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
              & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            | ~ v1_tops_2(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              & v1_tops_2(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
              & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            | ~ v1_tops_2(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_tops_2(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r2_hidden(X1,k5_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k5_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f68,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f52,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f64,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f69,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

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
    inference(flattening,[],[f19])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK0(X0,X1),X0)
        & r2_hidden(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ( ~ v3_pre_topc(sK0(X0,X1),X0)
                & r2_hidden(sK0(X0,X1),X1)
                & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(X3,X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
      | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => v1_tops_2(u1_pre_topc(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( v1_tops_2(u1_pre_topc(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f57,plain,(
    ! [X0] :
      ( v1_tops_2(u1_pre_topc(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f62,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f75,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k6_tmap_1(sK1,sK2)
    | ~ v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_22,negated_conjecture,
    ( v3_pre_topc(sK2,sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2495,negated_conjecture,
    ( v3_pre_topc(sK2,sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_3163,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,sK2)
    | v3_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2495])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2494,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_3164,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2494])).

cnf(c_2,plain,
    ( ~ v3_pre_topc(X0,X1)
    | r2_hidden(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2503,plain,
    ( ~ v3_pre_topc(X0_44,X0_45)
    | r2_hidden(X0_44,u1_pre_topc(X0_45))
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(X0_45)))
    | ~ l1_pre_topc(X0_45) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_3155,plain,
    ( v3_pre_topc(X0_44,X0_45) != iProver_top
    | r2_hidden(X0_44,u1_pre_topc(X0_45)) = iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(X0_45))) != iProver_top
    | l1_pre_topc(X0_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2503])).

cnf(c_3696,plain,
    ( v3_pre_topc(sK2,sK1) != iProver_top
    | r2_hidden(sK2,u1_pre_topc(sK1)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3164,c_3155])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_29,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3990,plain,
    ( r2_hidden(sK2,u1_pre_topc(sK1)) = iProver_top
    | v3_pre_topc(sK2,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3696,c_29])).

cnf(c_3991,plain,
    ( v3_pre_topc(sK2,sK1) != iProver_top
    | r2_hidden(sK2,u1_pre_topc(sK1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3990])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) = u1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_570,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) = u1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_26])).

cnf(c_571,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | k5_tmap_1(sK1,X0) = u1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_570])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_575,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k5_tmap_1(sK1,X0) = u1_pre_topc(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_571,c_25,c_24])).

cnf(c_2490,plain,
    ( ~ r2_hidden(X0_44,u1_pre_topc(sK1))
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | k5_tmap_1(sK1,X0_44) = u1_pre_topc(sK1) ),
    inference(subtyping,[status(esa)],[c_575])).

cnf(c_3168,plain,
    ( k5_tmap_1(sK1,X0_44) = u1_pre_topc(sK1)
    | r2_hidden(X0_44,u1_pre_topc(sK1)) != iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2490])).

cnf(c_4389,plain,
    ( k5_tmap_1(sK1,sK2) = u1_pre_topc(sK1)
    | r2_hidden(sK2,u1_pre_topc(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3164,c_3168])).

cnf(c_4412,plain,
    ( k5_tmap_1(sK1,sK2) = u1_pre_topc(sK1)
    | v3_pre_topc(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3991,c_4389])).

cnf(c_4692,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,sK2)
    | k5_tmap_1(sK1,sK2) = u1_pre_topc(sK1) ),
    inference(superposition,[status(thm)],[c_3163,c_4412])).

cnf(c_12,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_684,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_26])).

cnf(c_685,plain,
    ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_tops_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_684])).

cnf(c_689,plain,
    ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_tops_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_685,c_25,c_24])).

cnf(c_2485,plain,
    ( v1_tops_2(X0_44,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_tops_2(X0_44,sK1)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_689])).

cnf(c_3173,plain,
    ( v1_tops_2(X0_44,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v1_tops_2(X0_44,sK1) != iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2485])).

cnf(c_4932,plain,
    ( k5_tmap_1(sK1,sK2) = u1_pre_topc(sK1)
    | v1_tops_2(X0_44,k6_tmap_1(sK1,sK2)) = iProver_top
    | v1_tops_2(X0_44,sK1) != iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4692,c_3173])).

cnf(c_30,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_16,plain,
    ( r2_hidden(X0,k5_tmap_1(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_612,plain,
    ( r2_hidden(X0,k5_tmap_1(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_26])).

cnf(c_613,plain,
    ( r2_hidden(X0,k5_tmap_1(sK1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_612])).

cnf(c_617,plain,
    ( r2_hidden(X0,k5_tmap_1(sK1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_613,c_25,c_24])).

cnf(c_2488,plain,
    ( r2_hidden(X0_44,k5_tmap_1(sK1,X0_44))
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_617])).

cnf(c_2578,plain,
    ( r2_hidden(X0_44,k5_tmap_1(sK1,X0_44)) = iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2488])).

cnf(c_2580,plain,
    ( r2_hidden(sK2,k5_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2578])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_534,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_26])).

cnf(c_535,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(k6_tmap_1(sK1,X0)) = u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_534])).

cnf(c_539,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | u1_struct_0(k6_tmap_1(sK1,X0)) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_535,c_25,c_24])).

cnf(c_2492,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | u1_struct_0(k6_tmap_1(sK1,X0_44)) = u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_539])).

cnf(c_3166,plain,
    ( u1_struct_0(k6_tmap_1(sK1,X0_44)) = u1_struct_0(sK1)
    | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2492])).

cnf(c_3440,plain,
    ( u1_struct_0(k6_tmap_1(sK1,sK2)) = u1_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_3164,c_3166])).

cnf(c_3,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2502,plain,
    ( m1_subset_1(u1_pre_topc(X0_45),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0_45))))
    | ~ l1_pre_topc(X0_45) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_3156,plain,
    ( m1_subset_1(u1_pre_topc(X0_45),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0_45)))) = iProver_top
    | l1_pre_topc(X0_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2502])).

cnf(c_3613,plain,
    ( m1_subset_1(u1_pre_topc(k6_tmap_1(sK1,sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3440,c_3156])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k6_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_648,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k6_tmap_1(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_26])).

cnf(c_649,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | l1_pre_topc(k6_tmap_1(sK1,X0))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_648])).

cnf(c_653,plain,
    ( l1_pre_topc(k6_tmap_1(sK1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_649,c_25,c_24])).

cnf(c_654,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | l1_pre_topc(k6_tmap_1(sK1,X0)) ),
    inference(renaming,[status(thm)],[c_653])).

cnf(c_2487,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | l1_pre_topc(k6_tmap_1(sK1,X0_44)) ),
    inference(subtyping,[status(esa)],[c_654])).

cnf(c_2581,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,X0_44)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2487])).

cnf(c_2583,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2581])).

cnf(c_4331,plain,
    ( m1_subset_1(u1_pre_topc(k6_tmap_1(sK1,sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3613,c_30,c_2583])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_552,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_26])).

cnf(c_553,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | u1_pre_topc(k6_tmap_1(sK1,X0)) = k5_tmap_1(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_552])).

cnf(c_557,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | u1_pre_topc(k6_tmap_1(sK1,X0)) = k5_tmap_1(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_553,c_25,c_24])).

cnf(c_2491,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | u1_pre_topc(k6_tmap_1(sK1,X0_44)) = k5_tmap_1(sK1,X0_44) ),
    inference(subtyping,[status(esa)],[c_557])).

cnf(c_3167,plain,
    ( u1_pre_topc(k6_tmap_1(sK1,X0_44)) = k5_tmap_1(sK1,X0_44)
    | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2491])).

cnf(c_3856,plain,
    ( u1_pre_topc(k6_tmap_1(sK1,sK2)) = k5_tmap_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_3164,c_3167])).

cnf(c_4335,plain,
    ( m1_subset_1(k5_tmap_1(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4331,c_3856])).

cnf(c_7,plain,
    ( ~ v1_tops_2(X0,X1)
    | v3_pre_topc(X2,X1)
    | ~ r2_hidden(X2,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2498,plain,
    ( ~ v1_tops_2(X0_44,X0_45)
    | v3_pre_topc(X1_44,X0_45)
    | ~ r2_hidden(X1_44,X0_44)
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(X0_45)))
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0_45))))
    | ~ l1_pre_topc(X0_45) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_3160,plain,
    ( v1_tops_2(X0_44,X0_45) != iProver_top
    | v3_pre_topc(X1_44,X0_45) = iProver_top
    | r2_hidden(X1_44,X0_44) != iProver_top
    | m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(X0_45))) != iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0_45)))) != iProver_top
    | l1_pre_topc(X0_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2498])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2505,plain,
    ( ~ r2_hidden(X0_44,X1_44)
    | m1_subset_1(X0_44,X0_46)
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(X0_46)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_3153,plain,
    ( r2_hidden(X0_44,X1_44) != iProver_top
    | m1_subset_1(X0_44,X0_46) = iProver_top
    | m1_subset_1(X1_44,k1_zfmisc_1(X0_46)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2505])).

cnf(c_3305,plain,
    ( v1_tops_2(X0_44,X0_45) != iProver_top
    | v3_pre_topc(X1_44,X0_45) = iProver_top
    | r2_hidden(X1_44,X0_44) != iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0_45)))) != iProver_top
    | l1_pre_topc(X0_45) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3160,c_3153])).

cnf(c_4773,plain,
    ( v1_tops_2(k5_tmap_1(sK1,sK2),sK1) != iProver_top
    | v3_pre_topc(X0_44,sK1) = iProver_top
    | r2_hidden(X0_44,k5_tmap_1(sK1,sK2)) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4335,c_3305])).

cnf(c_4809,plain,
    ( v1_tops_2(k5_tmap_1(sK1,sK2),sK1) != iProver_top
    | v3_pre_topc(sK2,sK1) = iProver_top
    | r2_hidden(sK2,k5_tmap_1(sK1,sK2)) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4773])).

cnf(c_10,plain,
    ( v1_tops_2(X0,X1)
    | ~ v1_tops_2(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_726,plain,
    ( v1_tops_2(X0,X1)
    | ~ v1_tops_2(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_26])).

cnf(c_727,plain,
    ( ~ v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v1_tops_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_726])).

cnf(c_731,plain,
    ( ~ v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v1_tops_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_727,c_25,c_24])).

cnf(c_2483,plain,
    ( ~ v1_tops_2(X0_44,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v1_tops_2(X0_44,sK1)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(subtyping,[status(esa)],[c_731])).

cnf(c_3175,plain,
    ( v1_tops_2(X0_44,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v1_tops_2(X0_44,sK1) = iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2483])).

cnf(c_4602,plain,
    ( v1_tops_2(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v1_tops_2(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK1) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3156,c_3175])).

cnf(c_8,plain,
    ( v1_tops_2(u1_pre_topc(X0),X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2497,plain,
    ( v1_tops_2(u1_pre_topc(X0_45),X0_45)
    | ~ l1_pre_topc(X0_45) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_3370,plain,
    ( v1_tops_2(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(instantiation,[status(thm)],[c_2497])).

cnf(c_3373,plain,
    ( v1_tops_2(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3370])).

cnf(c_6109,plain,
    ( v1_tops_2(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK1) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4602,c_3373])).

cnf(c_6115,plain,
    ( k5_tmap_1(sK1,sK2) = u1_pre_topc(sK1)
    | v1_tops_2(u1_pre_topc(k6_tmap_1(sK1,sK2)),sK1) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4692,c_6109])).

cnf(c_6116,plain,
    ( k5_tmap_1(sK1,sK2) = u1_pre_topc(sK1)
    | v1_tops_2(k5_tmap_1(sK1,sK2),sK1) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6115,c_3856])).

cnf(c_69,plain,
    ( v1_tops_2(u1_pre_topc(X0),X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_71,plain,
    ( v1_tops_2(u1_pre_topc(sK1),sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_69])).

cnf(c_2508,plain,
    ( X0_45 = X0_45 ),
    theory(equality)).

cnf(c_2537,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_2508])).

cnf(c_2519,plain,
    ( ~ l1_pre_topc(X0_45)
    | l1_pre_topc(X1_45)
    | X1_45 != X0_45 ),
    theory(equality)).

cnf(c_3460,plain,
    ( ~ l1_pre_topc(X0_45)
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != X0_45 ),
    inference(instantiation,[status(thm)],[c_2519])).

cnf(c_3676,plain,
    ( ~ l1_pre_topc(k6_tmap_1(sK1,sK2))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k6_tmap_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_3460])).

cnf(c_3677,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k6_tmap_1(sK1,sK2)
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3676])).

cnf(c_2520,plain,
    ( ~ v1_tops_2(X0_44,X0_45)
    | v1_tops_2(X1_44,X1_45)
    | X1_45 != X0_45
    | X1_44 != X0_44 ),
    theory(equality)).

cnf(c_3432,plain,
    ( v1_tops_2(X0_44,X0_45)
    | ~ v1_tops_2(u1_pre_topc(X1_45),X1_45)
    | X0_45 != X1_45
    | X0_44 != u1_pre_topc(X1_45) ),
    inference(instantiation,[status(thm)],[c_2520])).

cnf(c_4024,plain,
    ( v1_tops_2(k5_tmap_1(sK1,X0_44),X0_45)
    | ~ v1_tops_2(u1_pre_topc(sK1),sK1)
    | X0_45 != sK1
    | k5_tmap_1(sK1,X0_44) != u1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_3432])).

cnf(c_4025,plain,
    ( X0_45 != sK1
    | k5_tmap_1(sK1,X0_44) != u1_pre_topc(sK1)
    | v1_tops_2(k5_tmap_1(sK1,X0_44),X0_45) = iProver_top
    | v1_tops_2(u1_pre_topc(sK1),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4024])).

cnf(c_4027,plain,
    ( sK1 != sK1
    | k5_tmap_1(sK1,sK2) != u1_pre_topc(sK1)
    | v1_tops_2(k5_tmap_1(sK1,sK2),sK1) = iProver_top
    | v1_tops_2(u1_pre_topc(sK1),sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4025])).

cnf(c_6972,plain,
    ( v1_tops_2(k5_tmap_1(sK1,sK2),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6116,c_29,c_30,c_71,c_2537,c_2583,c_3677,c_4027,c_4692])).

cnf(c_7089,plain,
    ( k5_tmap_1(sK1,sK2) = u1_pre_topc(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4932,c_29,c_30,c_71,c_2537,c_2580,c_2583,c_3677,c_4027,c_4412,c_4692,c_4809,c_6116])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X0)) = k6_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_666,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X0)) = k6_tmap_1(X1,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_26])).

cnf(c_667,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | g1_pre_topc(u1_struct_0(sK1),k5_tmap_1(sK1,X0)) = k6_tmap_1(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_666])).

cnf(c_671,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | g1_pre_topc(u1_struct_0(sK1),k5_tmap_1(sK1,X0)) = k6_tmap_1(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_667,c_25,c_24])).

cnf(c_2486,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | g1_pre_topc(u1_struct_0(sK1),k5_tmap_1(sK1,X0_44)) = k6_tmap_1(sK1,X0_44) ),
    inference(subtyping,[status(esa)],[c_671])).

cnf(c_3172,plain,
    ( g1_pre_topc(u1_struct_0(sK1),k5_tmap_1(sK1,X0_44)) = k6_tmap_1(sK1,X0_44)
    | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2486])).

cnf(c_3946,plain,
    ( g1_pre_topc(u1_struct_0(sK1),k5_tmap_1(sK1,sK2)) = k6_tmap_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_3164,c_3172])).

cnf(c_7099,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_7089,c_3946])).

cnf(c_21,negated_conjecture,
    ( ~ v3_pre_topc(sK2,sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k6_tmap_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2496,negated_conjecture,
    ( ~ v3_pre_topc(sK2,sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k6_tmap_1(sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_2562,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k6_tmap_1(sK1,sK2)
    | v3_pre_topc(sK2,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2496])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7099,c_6972,c_4809,c_2580,c_2562,c_30,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:59:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.52/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.00  
% 2.52/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.52/1.00  
% 2.52/1.00  ------  iProver source info
% 2.52/1.00  
% 2.52/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.52/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.52/1.00  git: non_committed_changes: false
% 2.52/1.00  git: last_make_outside_of_git: false
% 2.52/1.00  
% 2.52/1.00  ------ 
% 2.52/1.00  
% 2.52/1.00  ------ Input Options
% 2.52/1.00  
% 2.52/1.00  --out_options                           all
% 2.52/1.00  --tptp_safe_out                         true
% 2.52/1.00  --problem_path                          ""
% 2.52/1.00  --include_path                          ""
% 2.52/1.00  --clausifier                            res/vclausify_rel
% 2.52/1.00  --clausifier_options                    --mode clausify
% 2.52/1.00  --stdin                                 false
% 2.52/1.00  --stats_out                             all
% 2.52/1.00  
% 2.52/1.00  ------ General Options
% 2.52/1.00  
% 2.52/1.00  --fof                                   false
% 2.52/1.00  --time_out_real                         305.
% 2.52/1.00  --time_out_virtual                      -1.
% 2.52/1.00  --symbol_type_check                     false
% 2.52/1.00  --clausify_out                          false
% 2.52/1.00  --sig_cnt_out                           false
% 2.52/1.00  --trig_cnt_out                          false
% 2.52/1.00  --trig_cnt_out_tolerance                1.
% 2.52/1.00  --trig_cnt_out_sk_spl                   false
% 2.52/1.00  --abstr_cl_out                          false
% 2.52/1.00  
% 2.52/1.00  ------ Global Options
% 2.52/1.00  
% 2.52/1.00  --schedule                              default
% 2.52/1.00  --add_important_lit                     false
% 2.52/1.00  --prop_solver_per_cl                    1000
% 2.52/1.00  --min_unsat_core                        false
% 2.52/1.00  --soft_assumptions                      false
% 2.52/1.00  --soft_lemma_size                       3
% 2.52/1.00  --prop_impl_unit_size                   0
% 2.52/1.00  --prop_impl_unit                        []
% 2.52/1.00  --share_sel_clauses                     true
% 2.52/1.00  --reset_solvers                         false
% 2.52/1.00  --bc_imp_inh                            [conj_cone]
% 2.52/1.00  --conj_cone_tolerance                   3.
% 2.52/1.00  --extra_neg_conj                        none
% 2.52/1.00  --large_theory_mode                     true
% 2.52/1.00  --prolific_symb_bound                   200
% 2.52/1.00  --lt_threshold                          2000
% 2.52/1.00  --clause_weak_htbl                      true
% 2.52/1.00  --gc_record_bc_elim                     false
% 2.52/1.00  
% 2.52/1.00  ------ Preprocessing Options
% 2.52/1.00  
% 2.52/1.00  --preprocessing_flag                    true
% 2.52/1.00  --time_out_prep_mult                    0.1
% 2.52/1.00  --splitting_mode                        input
% 2.52/1.00  --splitting_grd                         true
% 2.52/1.00  --splitting_cvd                         false
% 2.52/1.00  --splitting_cvd_svl                     false
% 2.52/1.00  --splitting_nvd                         32
% 2.52/1.00  --sub_typing                            true
% 2.52/1.00  --prep_gs_sim                           true
% 2.52/1.00  --prep_unflatten                        true
% 2.52/1.00  --prep_res_sim                          true
% 2.52/1.00  --prep_upred                            true
% 2.52/1.00  --prep_sem_filter                       exhaustive
% 2.52/1.00  --prep_sem_filter_out                   false
% 2.52/1.00  --pred_elim                             true
% 2.52/1.00  --res_sim_input                         true
% 2.52/1.00  --eq_ax_congr_red                       true
% 2.52/1.00  --pure_diseq_elim                       true
% 2.52/1.00  --brand_transform                       false
% 2.52/1.00  --non_eq_to_eq                          false
% 2.52/1.00  --prep_def_merge                        true
% 2.52/1.00  --prep_def_merge_prop_impl              false
% 2.52/1.00  --prep_def_merge_mbd                    true
% 2.52/1.00  --prep_def_merge_tr_red                 false
% 2.52/1.00  --prep_def_merge_tr_cl                  false
% 2.52/1.00  --smt_preprocessing                     true
% 2.52/1.00  --smt_ac_axioms                         fast
% 2.52/1.00  --preprocessed_out                      false
% 2.52/1.00  --preprocessed_stats                    false
% 2.52/1.00  
% 2.52/1.00  ------ Abstraction refinement Options
% 2.52/1.00  
% 2.52/1.00  --abstr_ref                             []
% 2.52/1.00  --abstr_ref_prep                        false
% 2.52/1.00  --abstr_ref_until_sat                   false
% 2.52/1.00  --abstr_ref_sig_restrict                funpre
% 2.52/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.52/1.00  --abstr_ref_under                       []
% 2.52/1.00  
% 2.52/1.00  ------ SAT Options
% 2.52/1.00  
% 2.52/1.00  --sat_mode                              false
% 2.52/1.00  --sat_fm_restart_options                ""
% 2.52/1.00  --sat_gr_def                            false
% 2.52/1.00  --sat_epr_types                         true
% 2.52/1.00  --sat_non_cyclic_types                  false
% 2.52/1.00  --sat_finite_models                     false
% 2.52/1.00  --sat_fm_lemmas                         false
% 2.52/1.00  --sat_fm_prep                           false
% 2.52/1.00  --sat_fm_uc_incr                        true
% 2.52/1.00  --sat_out_model                         small
% 2.52/1.00  --sat_out_clauses                       false
% 2.52/1.00  
% 2.52/1.00  ------ QBF Options
% 2.52/1.00  
% 2.52/1.00  --qbf_mode                              false
% 2.52/1.00  --qbf_elim_univ                         false
% 2.52/1.00  --qbf_dom_inst                          none
% 2.52/1.00  --qbf_dom_pre_inst                      false
% 2.52/1.00  --qbf_sk_in                             false
% 2.52/1.00  --qbf_pred_elim                         true
% 2.52/1.00  --qbf_split                             512
% 2.52/1.00  
% 2.52/1.00  ------ BMC1 Options
% 2.52/1.00  
% 2.52/1.00  --bmc1_incremental                      false
% 2.52/1.00  --bmc1_axioms                           reachable_all
% 2.52/1.00  --bmc1_min_bound                        0
% 2.52/1.00  --bmc1_max_bound                        -1
% 2.52/1.00  --bmc1_max_bound_default                -1
% 2.52/1.00  --bmc1_symbol_reachability              true
% 2.52/1.00  --bmc1_property_lemmas                  false
% 2.52/1.00  --bmc1_k_induction                      false
% 2.52/1.00  --bmc1_non_equiv_states                 false
% 2.52/1.00  --bmc1_deadlock                         false
% 2.52/1.00  --bmc1_ucm                              false
% 2.52/1.00  --bmc1_add_unsat_core                   none
% 2.52/1.00  --bmc1_unsat_core_children              false
% 2.52/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.52/1.00  --bmc1_out_stat                         full
% 2.52/1.00  --bmc1_ground_init                      false
% 2.52/1.00  --bmc1_pre_inst_next_state              false
% 2.52/1.00  --bmc1_pre_inst_state                   false
% 2.52/1.00  --bmc1_pre_inst_reach_state             false
% 2.52/1.00  --bmc1_out_unsat_core                   false
% 2.52/1.00  --bmc1_aig_witness_out                  false
% 2.52/1.00  --bmc1_verbose                          false
% 2.52/1.00  --bmc1_dump_clauses_tptp                false
% 2.52/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.52/1.00  --bmc1_dump_file                        -
% 2.52/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.52/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.52/1.00  --bmc1_ucm_extend_mode                  1
% 2.52/1.00  --bmc1_ucm_init_mode                    2
% 2.52/1.00  --bmc1_ucm_cone_mode                    none
% 2.52/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.52/1.00  --bmc1_ucm_relax_model                  4
% 2.52/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.52/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.52/1.00  --bmc1_ucm_layered_model                none
% 2.52/1.00  --bmc1_ucm_max_lemma_size               10
% 2.52/1.00  
% 2.52/1.00  ------ AIG Options
% 2.52/1.00  
% 2.52/1.00  --aig_mode                              false
% 2.52/1.00  
% 2.52/1.00  ------ Instantiation Options
% 2.52/1.00  
% 2.52/1.00  --instantiation_flag                    true
% 2.52/1.00  --inst_sos_flag                         false
% 2.52/1.00  --inst_sos_phase                        true
% 2.52/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.52/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.52/1.00  --inst_lit_sel_side                     num_symb
% 2.52/1.00  --inst_solver_per_active                1400
% 2.52/1.00  --inst_solver_calls_frac                1.
% 2.52/1.00  --inst_passive_queue_type               priority_queues
% 2.52/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.52/1.00  --inst_passive_queues_freq              [25;2]
% 2.52/1.00  --inst_dismatching                      true
% 2.52/1.00  --inst_eager_unprocessed_to_passive     true
% 2.52/1.00  --inst_prop_sim_given                   true
% 2.52/1.00  --inst_prop_sim_new                     false
% 2.52/1.00  --inst_subs_new                         false
% 2.52/1.00  --inst_eq_res_simp                      false
% 2.52/1.00  --inst_subs_given                       false
% 2.52/1.00  --inst_orphan_elimination               true
% 2.52/1.00  --inst_learning_loop_flag               true
% 2.52/1.00  --inst_learning_start                   3000
% 2.52/1.00  --inst_learning_factor                  2
% 2.52/1.00  --inst_start_prop_sim_after_learn       3
% 2.52/1.00  --inst_sel_renew                        solver
% 2.52/1.00  --inst_lit_activity_flag                true
% 2.52/1.00  --inst_restr_to_given                   false
% 2.52/1.00  --inst_activity_threshold               500
% 2.52/1.00  --inst_out_proof                        true
% 2.52/1.00  
% 2.52/1.00  ------ Resolution Options
% 2.52/1.00  
% 2.52/1.00  --resolution_flag                       true
% 2.52/1.00  --res_lit_sel                           adaptive
% 2.52/1.00  --res_lit_sel_side                      none
% 2.52/1.00  --res_ordering                          kbo
% 2.52/1.00  --res_to_prop_solver                    active
% 2.52/1.00  --res_prop_simpl_new                    false
% 2.52/1.00  --res_prop_simpl_given                  true
% 2.52/1.00  --res_passive_queue_type                priority_queues
% 2.52/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.52/1.00  --res_passive_queues_freq               [15;5]
% 2.52/1.00  --res_forward_subs                      full
% 2.52/1.00  --res_backward_subs                     full
% 2.52/1.00  --res_forward_subs_resolution           true
% 2.52/1.00  --res_backward_subs_resolution          true
% 2.52/1.00  --res_orphan_elimination                true
% 2.52/1.00  --res_time_limit                        2.
% 2.52/1.00  --res_out_proof                         true
% 2.52/1.00  
% 2.52/1.00  ------ Superposition Options
% 2.52/1.00  
% 2.52/1.00  --superposition_flag                    true
% 2.52/1.00  --sup_passive_queue_type                priority_queues
% 2.52/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.52/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.52/1.00  --demod_completeness_check              fast
% 2.52/1.00  --demod_use_ground                      true
% 2.52/1.00  --sup_to_prop_solver                    passive
% 2.52/1.00  --sup_prop_simpl_new                    true
% 2.52/1.00  --sup_prop_simpl_given                  true
% 2.52/1.00  --sup_fun_splitting                     false
% 2.52/1.00  --sup_smt_interval                      50000
% 2.52/1.00  
% 2.52/1.00  ------ Superposition Simplification Setup
% 2.52/1.00  
% 2.52/1.00  --sup_indices_passive                   []
% 2.52/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.52/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/1.00  --sup_full_bw                           [BwDemod]
% 2.52/1.00  --sup_immed_triv                        [TrivRules]
% 2.52/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.52/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/1.00  --sup_immed_bw_main                     []
% 2.52/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.52/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.52/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.52/1.00  
% 2.52/1.00  ------ Combination Options
% 2.52/1.00  
% 2.52/1.00  --comb_res_mult                         3
% 2.52/1.00  --comb_sup_mult                         2
% 2.52/1.00  --comb_inst_mult                        10
% 2.52/1.00  
% 2.52/1.00  ------ Debug Options
% 2.52/1.00  
% 2.52/1.00  --dbg_backtrace                         false
% 2.52/1.00  --dbg_dump_prop_clauses                 false
% 2.52/1.00  --dbg_dump_prop_clauses_file            -
% 2.52/1.00  --dbg_out_stat                          false
% 2.52/1.00  ------ Parsing...
% 2.52/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.52/1.00  
% 2.52/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.52/1.00  
% 2.52/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.52/1.00  
% 2.52/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.52/1.00  ------ Proving...
% 2.52/1.00  ------ Problem Properties 
% 2.52/1.00  
% 2.52/1.00  
% 2.52/1.00  clauses                                 24
% 2.52/1.00  conjectures                             4
% 2.52/1.00  EPR                                     1
% 2.52/1.00  Horn                                    21
% 2.52/1.00  unary                                   2
% 2.52/1.00  binary                                  9
% 2.52/1.00  lits                                    67
% 2.52/1.00  lits eq                                 7
% 2.52/1.00  fd_pure                                 0
% 2.52/1.00  fd_pseudo                               0
% 2.52/1.00  fd_cond                                 0
% 2.52/1.00  fd_pseudo_cond                          0
% 2.52/1.00  AC symbols                              0
% 2.52/1.00  
% 2.52/1.00  ------ Schedule dynamic 5 is on 
% 2.52/1.00  
% 2.52/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.52/1.00  
% 2.52/1.00  
% 2.52/1.00  ------ 
% 2.52/1.00  Current options:
% 2.52/1.00  ------ 
% 2.52/1.00  
% 2.52/1.00  ------ Input Options
% 2.52/1.00  
% 2.52/1.00  --out_options                           all
% 2.52/1.00  --tptp_safe_out                         true
% 2.52/1.00  --problem_path                          ""
% 2.52/1.00  --include_path                          ""
% 2.52/1.00  --clausifier                            res/vclausify_rel
% 2.52/1.00  --clausifier_options                    --mode clausify
% 2.52/1.00  --stdin                                 false
% 2.52/1.00  --stats_out                             all
% 2.52/1.00  
% 2.52/1.00  ------ General Options
% 2.52/1.00  
% 2.52/1.00  --fof                                   false
% 2.52/1.00  --time_out_real                         305.
% 2.52/1.00  --time_out_virtual                      -1.
% 2.52/1.00  --symbol_type_check                     false
% 2.52/1.00  --clausify_out                          false
% 2.52/1.00  --sig_cnt_out                           false
% 2.52/1.00  --trig_cnt_out                          false
% 2.52/1.00  --trig_cnt_out_tolerance                1.
% 2.52/1.00  --trig_cnt_out_sk_spl                   false
% 2.52/1.00  --abstr_cl_out                          false
% 2.52/1.00  
% 2.52/1.00  ------ Global Options
% 2.52/1.00  
% 2.52/1.00  --schedule                              default
% 2.52/1.00  --add_important_lit                     false
% 2.52/1.00  --prop_solver_per_cl                    1000
% 2.52/1.00  --min_unsat_core                        false
% 2.52/1.00  --soft_assumptions                      false
% 2.52/1.00  --soft_lemma_size                       3
% 2.52/1.00  --prop_impl_unit_size                   0
% 2.52/1.00  --prop_impl_unit                        []
% 2.52/1.00  --share_sel_clauses                     true
% 2.52/1.00  --reset_solvers                         false
% 2.52/1.00  --bc_imp_inh                            [conj_cone]
% 2.52/1.00  --conj_cone_tolerance                   3.
% 2.52/1.00  --extra_neg_conj                        none
% 2.52/1.00  --large_theory_mode                     true
% 2.52/1.00  --prolific_symb_bound                   200
% 2.52/1.00  --lt_threshold                          2000
% 2.52/1.00  --clause_weak_htbl                      true
% 2.52/1.00  --gc_record_bc_elim                     false
% 2.52/1.00  
% 2.52/1.00  ------ Preprocessing Options
% 2.52/1.00  
% 2.52/1.00  --preprocessing_flag                    true
% 2.52/1.00  --time_out_prep_mult                    0.1
% 2.52/1.00  --splitting_mode                        input
% 2.52/1.00  --splitting_grd                         true
% 2.52/1.00  --splitting_cvd                         false
% 2.52/1.00  --splitting_cvd_svl                     false
% 2.52/1.00  --splitting_nvd                         32
% 2.52/1.00  --sub_typing                            true
% 2.52/1.00  --prep_gs_sim                           true
% 2.52/1.00  --prep_unflatten                        true
% 2.52/1.00  --prep_res_sim                          true
% 2.52/1.00  --prep_upred                            true
% 2.52/1.00  --prep_sem_filter                       exhaustive
% 2.52/1.00  --prep_sem_filter_out                   false
% 2.52/1.00  --pred_elim                             true
% 2.52/1.00  --res_sim_input                         true
% 2.52/1.00  --eq_ax_congr_red                       true
% 2.52/1.00  --pure_diseq_elim                       true
% 2.52/1.00  --brand_transform                       false
% 2.52/1.00  --non_eq_to_eq                          false
% 2.52/1.00  --prep_def_merge                        true
% 2.52/1.00  --prep_def_merge_prop_impl              false
% 2.52/1.00  --prep_def_merge_mbd                    true
% 2.52/1.00  --prep_def_merge_tr_red                 false
% 2.52/1.00  --prep_def_merge_tr_cl                  false
% 2.52/1.00  --smt_preprocessing                     true
% 2.52/1.00  --smt_ac_axioms                         fast
% 2.52/1.00  --preprocessed_out                      false
% 2.52/1.00  --preprocessed_stats                    false
% 2.52/1.00  
% 2.52/1.00  ------ Abstraction refinement Options
% 2.52/1.00  
% 2.52/1.00  --abstr_ref                             []
% 2.52/1.00  --abstr_ref_prep                        false
% 2.52/1.00  --abstr_ref_until_sat                   false
% 2.52/1.00  --abstr_ref_sig_restrict                funpre
% 2.52/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.52/1.00  --abstr_ref_under                       []
% 2.52/1.00  
% 2.52/1.00  ------ SAT Options
% 2.52/1.00  
% 2.52/1.00  --sat_mode                              false
% 2.52/1.00  --sat_fm_restart_options                ""
% 2.52/1.00  --sat_gr_def                            false
% 2.52/1.00  --sat_epr_types                         true
% 2.52/1.00  --sat_non_cyclic_types                  false
% 2.52/1.00  --sat_finite_models                     false
% 2.52/1.00  --sat_fm_lemmas                         false
% 2.52/1.00  --sat_fm_prep                           false
% 2.52/1.00  --sat_fm_uc_incr                        true
% 2.52/1.00  --sat_out_model                         small
% 2.52/1.00  --sat_out_clauses                       false
% 2.52/1.00  
% 2.52/1.00  ------ QBF Options
% 2.52/1.00  
% 2.52/1.00  --qbf_mode                              false
% 2.52/1.00  --qbf_elim_univ                         false
% 2.52/1.00  --qbf_dom_inst                          none
% 2.52/1.00  --qbf_dom_pre_inst                      false
% 2.52/1.00  --qbf_sk_in                             false
% 2.52/1.00  --qbf_pred_elim                         true
% 2.52/1.00  --qbf_split                             512
% 2.52/1.00  
% 2.52/1.00  ------ BMC1 Options
% 2.52/1.00  
% 2.52/1.00  --bmc1_incremental                      false
% 2.52/1.00  --bmc1_axioms                           reachable_all
% 2.52/1.00  --bmc1_min_bound                        0
% 2.52/1.00  --bmc1_max_bound                        -1
% 2.52/1.00  --bmc1_max_bound_default                -1
% 2.52/1.00  --bmc1_symbol_reachability              true
% 2.52/1.00  --bmc1_property_lemmas                  false
% 2.52/1.00  --bmc1_k_induction                      false
% 2.52/1.00  --bmc1_non_equiv_states                 false
% 2.52/1.00  --bmc1_deadlock                         false
% 2.52/1.00  --bmc1_ucm                              false
% 2.52/1.00  --bmc1_add_unsat_core                   none
% 2.52/1.00  --bmc1_unsat_core_children              false
% 2.52/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.52/1.00  --bmc1_out_stat                         full
% 2.52/1.00  --bmc1_ground_init                      false
% 2.52/1.00  --bmc1_pre_inst_next_state              false
% 2.52/1.00  --bmc1_pre_inst_state                   false
% 2.52/1.00  --bmc1_pre_inst_reach_state             false
% 2.52/1.00  --bmc1_out_unsat_core                   false
% 2.52/1.00  --bmc1_aig_witness_out                  false
% 2.52/1.00  --bmc1_verbose                          false
% 2.52/1.00  --bmc1_dump_clauses_tptp                false
% 2.52/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.52/1.00  --bmc1_dump_file                        -
% 2.52/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.52/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.52/1.00  --bmc1_ucm_extend_mode                  1
% 2.52/1.00  --bmc1_ucm_init_mode                    2
% 2.52/1.00  --bmc1_ucm_cone_mode                    none
% 2.52/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.52/1.00  --bmc1_ucm_relax_model                  4
% 2.52/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.52/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.52/1.00  --bmc1_ucm_layered_model                none
% 2.52/1.00  --bmc1_ucm_max_lemma_size               10
% 2.52/1.00  
% 2.52/1.00  ------ AIG Options
% 2.52/1.00  
% 2.52/1.00  --aig_mode                              false
% 2.52/1.00  
% 2.52/1.00  ------ Instantiation Options
% 2.52/1.00  
% 2.52/1.00  --instantiation_flag                    true
% 2.52/1.00  --inst_sos_flag                         false
% 2.52/1.00  --inst_sos_phase                        true
% 2.52/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.52/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.52/1.00  --inst_lit_sel_side                     none
% 2.52/1.00  --inst_solver_per_active                1400
% 2.52/1.00  --inst_solver_calls_frac                1.
% 2.52/1.00  --inst_passive_queue_type               priority_queues
% 2.52/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.52/1.00  --inst_passive_queues_freq              [25;2]
% 2.52/1.00  --inst_dismatching                      true
% 2.52/1.00  --inst_eager_unprocessed_to_passive     true
% 2.52/1.00  --inst_prop_sim_given                   true
% 2.52/1.00  --inst_prop_sim_new                     false
% 2.52/1.00  --inst_subs_new                         false
% 2.52/1.00  --inst_eq_res_simp                      false
% 2.52/1.00  --inst_subs_given                       false
% 2.52/1.00  --inst_orphan_elimination               true
% 2.52/1.00  --inst_learning_loop_flag               true
% 2.52/1.00  --inst_learning_start                   3000
% 2.52/1.00  --inst_learning_factor                  2
% 2.52/1.00  --inst_start_prop_sim_after_learn       3
% 2.52/1.00  --inst_sel_renew                        solver
% 2.52/1.00  --inst_lit_activity_flag                true
% 2.52/1.00  --inst_restr_to_given                   false
% 2.52/1.00  --inst_activity_threshold               500
% 2.52/1.00  --inst_out_proof                        true
% 2.52/1.00  
% 2.52/1.00  ------ Resolution Options
% 2.52/1.00  
% 2.52/1.00  --resolution_flag                       false
% 2.52/1.00  --res_lit_sel                           adaptive
% 2.52/1.00  --res_lit_sel_side                      none
% 2.52/1.00  --res_ordering                          kbo
% 2.52/1.00  --res_to_prop_solver                    active
% 2.52/1.00  --res_prop_simpl_new                    false
% 2.52/1.00  --res_prop_simpl_given                  true
% 2.52/1.00  --res_passive_queue_type                priority_queues
% 2.52/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.52/1.00  --res_passive_queues_freq               [15;5]
% 2.52/1.00  --res_forward_subs                      full
% 2.52/1.00  --res_backward_subs                     full
% 2.52/1.00  --res_forward_subs_resolution           true
% 2.52/1.00  --res_backward_subs_resolution          true
% 2.52/1.00  --res_orphan_elimination                true
% 2.52/1.00  --res_time_limit                        2.
% 2.52/1.00  --res_out_proof                         true
% 2.52/1.00  
% 2.52/1.00  ------ Superposition Options
% 2.52/1.00  
% 2.52/1.00  --superposition_flag                    true
% 2.52/1.00  --sup_passive_queue_type                priority_queues
% 2.52/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.52/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.52/1.00  --demod_completeness_check              fast
% 2.52/1.00  --demod_use_ground                      true
% 2.52/1.00  --sup_to_prop_solver                    passive
% 2.52/1.00  --sup_prop_simpl_new                    true
% 2.52/1.00  --sup_prop_simpl_given                  true
% 2.52/1.00  --sup_fun_splitting                     false
% 2.52/1.00  --sup_smt_interval                      50000
% 2.52/1.00  
% 2.52/1.00  ------ Superposition Simplification Setup
% 2.52/1.00  
% 2.52/1.00  --sup_indices_passive                   []
% 2.52/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.52/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/1.00  --sup_full_bw                           [BwDemod]
% 2.52/1.00  --sup_immed_triv                        [TrivRules]
% 2.52/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.52/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/1.00  --sup_immed_bw_main                     []
% 2.52/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.52/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.52/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.52/1.00  
% 2.52/1.00  ------ Combination Options
% 2.52/1.00  
% 2.52/1.00  --comb_res_mult                         3
% 2.52/1.00  --comb_sup_mult                         2
% 2.52/1.00  --comb_inst_mult                        10
% 2.52/1.00  
% 2.52/1.00  ------ Debug Options
% 2.52/1.00  
% 2.52/1.00  --dbg_backtrace                         false
% 2.52/1.00  --dbg_dump_prop_clauses                 false
% 2.52/1.00  --dbg_dump_prop_clauses_file            -
% 2.52/1.00  --dbg_out_stat                          false
% 2.52/1.00  
% 2.52/1.00  
% 2.52/1.00  
% 2.52/1.00  
% 2.52/1.00  ------ Proving...
% 2.52/1.00  
% 2.52/1.00  
% 2.52/1.00  % SZS status Theorem for theBenchmark.p
% 2.52/1.00  
% 2.52/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.52/1.00  
% 2.52/1.00  fof(f12,conjecture,(
% 2.52/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1))))),
% 2.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/1.00  
% 2.52/1.00  fof(f13,negated_conjecture,(
% 2.52/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1))))),
% 2.52/1.00    inference(negated_conjecture,[],[f12])).
% 2.52/1.00  
% 2.52/1.00  fof(f34,plain,(
% 2.52/1.00    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.52/1.00    inference(ennf_transformation,[],[f13])).
% 2.52/1.00  
% 2.52/1.00  fof(f35,plain,(
% 2.52/1.00    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.52/1.00    inference(flattening,[],[f34])).
% 2.52/1.00  
% 2.52/1.00  fof(f44,plain,(
% 2.52/1.00    ? [X0] : (? [X1] : (((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.52/1.00    inference(nnf_transformation,[],[f35])).
% 2.52/1.00  
% 2.52/1.00  fof(f45,plain,(
% 2.52/1.00    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.52/1.00    inference(flattening,[],[f44])).
% 2.52/1.00  
% 2.52/1.00  fof(f47,plain,(
% 2.52/1.00    ( ! [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,sK2) | ~v3_pre_topc(sK2,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,sK2) | v3_pre_topc(sK2,X0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.52/1.00    introduced(choice_axiom,[])).
% 2.52/1.00  
% 2.52/1.00  fof(f46,plain,(
% 2.52/1.00    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k6_tmap_1(sK1,X1) | ~v3_pre_topc(X1,sK1)) & (g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,X1) | v3_pre_topc(X1,sK1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.52/1.00    introduced(choice_axiom,[])).
% 2.52/1.00  
% 2.52/1.00  fof(f48,plain,(
% 2.52/1.00    ((g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k6_tmap_1(sK1,sK2) | ~v3_pre_topc(sK2,sK1)) & (g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,sK2) | v3_pre_topc(sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.52/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f45,f47,f46])).
% 2.52/1.00  
% 2.52/1.00  fof(f74,plain,(
% 2.52/1.00    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,sK2) | v3_pre_topc(sK2,sK1)),
% 2.52/1.00    inference(cnf_transformation,[],[f48])).
% 2.52/1.00  
% 2.52/1.00  fof(f73,plain,(
% 2.52/1.00    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 2.52/1.00    inference(cnf_transformation,[],[f48])).
% 2.52/1.00  
% 2.52/1.00  fof(f2,axiom,(
% 2.52/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 2.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/1.00  
% 2.52/1.00  fof(f17,plain,(
% 2.52/1.00    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.52/1.00    inference(ennf_transformation,[],[f2])).
% 2.52/1.00  
% 2.52/1.00  fof(f36,plain,(
% 2.52/1.00    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.52/1.00    inference(nnf_transformation,[],[f17])).
% 2.52/1.00  
% 2.52/1.00  fof(f50,plain,(
% 2.52/1.00    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.52/1.00    inference(cnf_transformation,[],[f36])).
% 2.52/1.00  
% 2.52/1.00  fof(f72,plain,(
% 2.52/1.00    l1_pre_topc(sK1)),
% 2.52/1.00    inference(cnf_transformation,[],[f48])).
% 2.52/1.00  
% 2.52/1.00  fof(f10,axiom,(
% 2.52/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1))))),
% 2.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/1.00  
% 2.52/1.00  fof(f30,plain,(
% 2.52/1.00    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.52/1.00    inference(ennf_transformation,[],[f10])).
% 2.52/1.00  
% 2.52/1.00  fof(f31,plain,(
% 2.52/1.00    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.52/1.00    inference(flattening,[],[f30])).
% 2.52/1.00  
% 2.52/1.00  fof(f43,plain,(
% 2.52/1.00    ! [X0] : (! [X1] : (((r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1)) & (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.52/1.00    inference(nnf_transformation,[],[f31])).
% 2.52/1.00  
% 2.52/1.00  fof(f66,plain,(
% 2.52/1.00    ( ! [X0,X1] : (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.52/1.00    inference(cnf_transformation,[],[f43])).
% 2.52/1.00  
% 2.52/1.00  fof(f70,plain,(
% 2.52/1.00    ~v2_struct_0(sK1)),
% 2.52/1.00    inference(cnf_transformation,[],[f48])).
% 2.52/1.00  
% 2.52/1.00  fof(f71,plain,(
% 2.52/1.00    v2_pre_topc(sK1)),
% 2.52/1.00    inference(cnf_transformation,[],[f48])).
% 2.52/1.00  
% 2.52/1.00  fof(f6,axiom,(
% 2.52/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 2.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/1.00  
% 2.52/1.00  fof(f22,plain,(
% 2.52/1.00    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.52/1.00    inference(ennf_transformation,[],[f6])).
% 2.52/1.00  
% 2.52/1.00  fof(f23,plain,(
% 2.52/1.00    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.52/1.00    inference(flattening,[],[f22])).
% 2.52/1.00  
% 2.52/1.00  fof(f41,plain,(
% 2.52/1.00    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) | ~v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.52/1.00    inference(nnf_transformation,[],[f23])).
% 2.52/1.00  
% 2.52/1.00  fof(f42,plain,(
% 2.52/1.00    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) | ~v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) & ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.52/1.00    inference(flattening,[],[f41])).
% 2.52/1.00  
% 2.52/1.00  fof(f58,plain,(
% 2.52/1.00    ( ! [X0,X1] : (v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.52/1.00    inference(cnf_transformation,[],[f42])).
% 2.52/1.00  
% 2.52/1.00  fof(f9,axiom,(
% 2.52/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r2_hidden(X1,k5_tmap_1(X0,X1))))),
% 2.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/1.00  
% 2.52/1.00  fof(f28,plain,(
% 2.52/1.00    ! [X0] : (! [X1] : (r2_hidden(X1,k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.52/1.00    inference(ennf_transformation,[],[f9])).
% 2.52/1.00  
% 2.52/1.00  fof(f29,plain,(
% 2.52/1.00    ! [X0] : (! [X1] : (r2_hidden(X1,k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.52/1.00    inference(flattening,[],[f28])).
% 2.52/1.00  
% 2.52/1.00  fof(f65,plain,(
% 2.52/1.00    ( ! [X0,X1] : (r2_hidden(X1,k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.52/1.00    inference(cnf_transformation,[],[f29])).
% 2.52/1.00  
% 2.52/1.00  fof(f11,axiom,(
% 2.52/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 2.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/1.00  
% 2.52/1.00  fof(f32,plain,(
% 2.52/1.00    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.52/1.00    inference(ennf_transformation,[],[f11])).
% 2.52/1.00  
% 2.52/1.00  fof(f33,plain,(
% 2.52/1.00    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.52/1.00    inference(flattening,[],[f32])).
% 2.52/1.00  
% 2.52/1.00  fof(f68,plain,(
% 2.52/1.00    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.52/1.00    inference(cnf_transformation,[],[f33])).
% 2.52/1.00  
% 2.52/1.00  fof(f3,axiom,(
% 2.52/1.00    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/1.00  
% 2.52/1.00  fof(f18,plain,(
% 2.52/1.00    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.52/1.00    inference(ennf_transformation,[],[f3])).
% 2.52/1.00  
% 2.52/1.00  fof(f52,plain,(
% 2.52/1.00    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.52/1.00    inference(cnf_transformation,[],[f18])).
% 2.52/1.00  
% 2.52/1.00  fof(f8,axiom,(
% 2.52/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))))),
% 2.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/1.00  
% 2.52/1.00  fof(f14,plain,(
% 2.52/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))))),
% 2.52/1.00    inference(pure_predicate_removal,[],[f8])).
% 2.52/1.00  
% 2.52/1.00  fof(f26,plain,(
% 2.52/1.00    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.52/1.00    inference(ennf_transformation,[],[f14])).
% 2.52/1.00  
% 2.52/1.00  fof(f27,plain,(
% 2.52/1.00    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.52/1.00    inference(flattening,[],[f26])).
% 2.52/1.00  
% 2.52/1.00  fof(f64,plain,(
% 2.52/1.00    ( ! [X0,X1] : (l1_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.52/1.00    inference(cnf_transformation,[],[f27])).
% 2.52/1.00  
% 2.52/1.00  fof(f69,plain,(
% 2.52/1.00    ( ! [X0,X1] : (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.52/1.00    inference(cnf_transformation,[],[f33])).
% 2.52/1.00  
% 2.52/1.00  fof(f4,axiom,(
% 2.52/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,X1) => v3_pre_topc(X2,X0))))))),
% 2.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/1.00  
% 2.52/1.00  fof(f19,plain,(
% 2.52/1.00    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 2.52/1.00    inference(ennf_transformation,[],[f4])).
% 2.52/1.00  
% 2.52/1.00  fof(f20,plain,(
% 2.52/1.00    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 2.52/1.00    inference(flattening,[],[f19])).
% 2.52/1.00  
% 2.52/1.00  fof(f37,plain,(
% 2.52/1.00    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 2.52/1.00    inference(nnf_transformation,[],[f20])).
% 2.52/1.00  
% 2.52/1.00  fof(f38,plain,(
% 2.52/1.00    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 2.52/1.00    inference(rectify,[],[f37])).
% 2.52/1.00  
% 2.52/1.00  fof(f39,plain,(
% 2.52/1.00    ! [X1,X0] : (? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK0(X0,X1),X0) & r2_hidden(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.52/1.00    introduced(choice_axiom,[])).
% 2.52/1.00  
% 2.52/1.00  fof(f40,plain,(
% 2.52/1.00    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | (~v3_pre_topc(sK0(X0,X1),X0) & r2_hidden(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 2.52/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).
% 2.52/1.00  
% 2.52/1.00  fof(f53,plain,(
% 2.52/1.00    ( ! [X0,X3,X1] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.52/1.00    inference(cnf_transformation,[],[f40])).
% 2.52/1.00  
% 2.52/1.00  fof(f1,axiom,(
% 2.52/1.00    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/1.00  
% 2.52/1.00  fof(f15,plain,(
% 2.52/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.52/1.00    inference(ennf_transformation,[],[f1])).
% 2.52/1.00  
% 2.52/1.00  fof(f16,plain,(
% 2.52/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.52/1.00    inference(flattening,[],[f15])).
% 2.52/1.00  
% 2.52/1.00  fof(f49,plain,(
% 2.52/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.52/1.00    inference(cnf_transformation,[],[f16])).
% 2.52/1.00  
% 2.52/1.00  fof(f60,plain,(
% 2.52/1.00    ( ! [X0,X1] : (v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) | ~v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.52/1.00    inference(cnf_transformation,[],[f42])).
% 2.52/1.00  
% 2.52/1.00  fof(f5,axiom,(
% 2.52/1.00    ! [X0] : (l1_pre_topc(X0) => v1_tops_2(u1_pre_topc(X0),X0))),
% 2.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/1.00  
% 2.52/1.00  fof(f21,plain,(
% 2.52/1.00    ! [X0] : (v1_tops_2(u1_pre_topc(X0),X0) | ~l1_pre_topc(X0))),
% 2.52/1.00    inference(ennf_transformation,[],[f5])).
% 2.52/1.00  
% 2.52/1.00  fof(f57,plain,(
% 2.52/1.00    ( ! [X0] : (v1_tops_2(u1_pre_topc(X0),X0) | ~l1_pre_topc(X0)) )),
% 2.52/1.00    inference(cnf_transformation,[],[f21])).
% 2.52/1.00  
% 2.52/1.00  fof(f7,axiom,(
% 2.52/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1)))),
% 2.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/1.00  
% 2.52/1.00  fof(f24,plain,(
% 2.52/1.00    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.52/1.00    inference(ennf_transformation,[],[f7])).
% 2.52/1.00  
% 2.52/1.00  fof(f25,plain,(
% 2.52/1.00    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.52/1.00    inference(flattening,[],[f24])).
% 2.52/1.00  
% 2.52/1.00  fof(f62,plain,(
% 2.52/1.00    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.52/1.00    inference(cnf_transformation,[],[f25])).
% 2.52/1.00  
% 2.52/1.00  fof(f75,plain,(
% 2.52/1.00    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k6_tmap_1(sK1,sK2) | ~v3_pre_topc(sK2,sK1)),
% 2.52/1.00    inference(cnf_transformation,[],[f48])).
% 2.52/1.00  
% 2.52/1.00  cnf(c_22,negated_conjecture,
% 2.52/1.00      ( v3_pre_topc(sK2,sK1)
% 2.52/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,sK2) ),
% 2.52/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_2495,negated_conjecture,
% 2.52/1.00      ( v3_pre_topc(sK2,sK1)
% 2.52/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,sK2) ),
% 2.52/1.00      inference(subtyping,[status(esa)],[c_22]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_3163,plain,
% 2.52/1.00      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,sK2)
% 2.52/1.00      | v3_pre_topc(sK2,sK1) = iProver_top ),
% 2.52/1.00      inference(predicate_to_equality,[status(thm)],[c_2495]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_23,negated_conjecture,
% 2.52/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.52/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_2494,negated_conjecture,
% 2.52/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.52/1.00      inference(subtyping,[status(esa)],[c_23]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_3164,plain,
% 2.52/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.52/1.00      inference(predicate_to_equality,[status(thm)],[c_2494]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_2,plain,
% 2.52/1.00      ( ~ v3_pre_topc(X0,X1)
% 2.52/1.00      | r2_hidden(X0,u1_pre_topc(X1))
% 2.52/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.52/1.00      | ~ l1_pre_topc(X1) ),
% 2.52/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_2503,plain,
% 2.52/1.00      ( ~ v3_pre_topc(X0_44,X0_45)
% 2.52/1.00      | r2_hidden(X0_44,u1_pre_topc(X0_45))
% 2.52/1.00      | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(X0_45)))
% 2.52/1.00      | ~ l1_pre_topc(X0_45) ),
% 2.52/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_3155,plain,
% 2.52/1.00      ( v3_pre_topc(X0_44,X0_45) != iProver_top
% 2.52/1.00      | r2_hidden(X0_44,u1_pre_topc(X0_45)) = iProver_top
% 2.52/1.00      | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(X0_45))) != iProver_top
% 2.52/1.00      | l1_pre_topc(X0_45) != iProver_top ),
% 2.52/1.00      inference(predicate_to_equality,[status(thm)],[c_2503]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_3696,plain,
% 2.52/1.00      ( v3_pre_topc(sK2,sK1) != iProver_top
% 2.52/1.00      | r2_hidden(sK2,u1_pre_topc(sK1)) = iProver_top
% 2.52/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.52/1.00      inference(superposition,[status(thm)],[c_3164,c_3155]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_24,negated_conjecture,
% 2.52/1.00      ( l1_pre_topc(sK1) ),
% 2.52/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_29,plain,
% 2.52/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 2.52/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_3990,plain,
% 2.52/1.00      ( r2_hidden(sK2,u1_pre_topc(sK1)) = iProver_top
% 2.52/1.00      | v3_pre_topc(sK2,sK1) != iProver_top ),
% 2.52/1.00      inference(global_propositional_subsumption,
% 2.52/1.00                [status(thm)],
% 2.52/1.00                [c_3696,c_29]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_3991,plain,
% 2.52/1.00      ( v3_pre_topc(sK2,sK1) != iProver_top
% 2.52/1.00      | r2_hidden(sK2,u1_pre_topc(sK1)) = iProver_top ),
% 2.52/1.00      inference(renaming,[status(thm)],[c_3990]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_18,plain,
% 2.52/1.00      ( ~ r2_hidden(X0,u1_pre_topc(X1))
% 2.52/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.52/1.00      | v2_struct_0(X1)
% 2.52/1.00      | ~ v2_pre_topc(X1)
% 2.52/1.00      | ~ l1_pre_topc(X1)
% 2.52/1.00      | k5_tmap_1(X1,X0) = u1_pre_topc(X1) ),
% 2.52/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_26,negated_conjecture,
% 2.52/1.00      ( ~ v2_struct_0(sK1) ),
% 2.52/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_570,plain,
% 2.52/1.00      ( ~ r2_hidden(X0,u1_pre_topc(X1))
% 2.52/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.52/1.00      | ~ v2_pre_topc(X1)
% 2.52/1.00      | ~ l1_pre_topc(X1)
% 2.52/1.00      | k5_tmap_1(X1,X0) = u1_pre_topc(X1)
% 2.52/1.00      | sK1 != X1 ),
% 2.52/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_26]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_571,plain,
% 2.52/1.00      ( ~ r2_hidden(X0,u1_pre_topc(sK1))
% 2.52/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.52/1.00      | ~ v2_pre_topc(sK1)
% 2.52/1.00      | ~ l1_pre_topc(sK1)
% 2.52/1.00      | k5_tmap_1(sK1,X0) = u1_pre_topc(sK1) ),
% 2.52/1.00      inference(unflattening,[status(thm)],[c_570]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_25,negated_conjecture,
% 2.52/1.00      ( v2_pre_topc(sK1) ),
% 2.52/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_575,plain,
% 2.52/1.00      ( ~ r2_hidden(X0,u1_pre_topc(sK1))
% 2.52/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.52/1.00      | k5_tmap_1(sK1,X0) = u1_pre_topc(sK1) ),
% 2.52/1.00      inference(global_propositional_subsumption,
% 2.52/1.00                [status(thm)],
% 2.52/1.00                [c_571,c_25,c_24]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_2490,plain,
% 2.52/1.00      ( ~ r2_hidden(X0_44,u1_pre_topc(sK1))
% 2.52/1.00      | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.52/1.00      | k5_tmap_1(sK1,X0_44) = u1_pre_topc(sK1) ),
% 2.52/1.00      inference(subtyping,[status(esa)],[c_575]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_3168,plain,
% 2.52/1.00      ( k5_tmap_1(sK1,X0_44) = u1_pre_topc(sK1)
% 2.52/1.00      | r2_hidden(X0_44,u1_pre_topc(sK1)) != iProver_top
% 2.52/1.00      | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.52/1.00      inference(predicate_to_equality,[status(thm)],[c_2490]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_4389,plain,
% 2.52/1.00      ( k5_tmap_1(sK1,sK2) = u1_pre_topc(sK1)
% 2.52/1.00      | r2_hidden(sK2,u1_pre_topc(sK1)) != iProver_top ),
% 2.52/1.00      inference(superposition,[status(thm)],[c_3164,c_3168]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_4412,plain,
% 2.52/1.00      ( k5_tmap_1(sK1,sK2) = u1_pre_topc(sK1)
% 2.52/1.00      | v3_pre_topc(sK2,sK1) != iProver_top ),
% 2.52/1.00      inference(superposition,[status(thm)],[c_3991,c_4389]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_4692,plain,
% 2.52/1.00      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,sK2)
% 2.52/1.00      | k5_tmap_1(sK1,sK2) = u1_pre_topc(sK1) ),
% 2.52/1.00      inference(superposition,[status(thm)],[c_3163,c_4412]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_12,plain,
% 2.52/1.00      ( ~ v1_tops_2(X0,X1)
% 2.52/1.00      | v1_tops_2(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.52/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.52/1.00      | v2_struct_0(X1)
% 2.52/1.00      | ~ v2_pre_topc(X1)
% 2.52/1.00      | ~ l1_pre_topc(X1) ),
% 2.52/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_684,plain,
% 2.52/1.00      ( ~ v1_tops_2(X0,X1)
% 2.52/1.00      | v1_tops_2(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.52/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.52/1.00      | ~ v2_pre_topc(X1)
% 2.52/1.00      | ~ l1_pre_topc(X1)
% 2.52/1.00      | sK1 != X1 ),
% 2.52/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_26]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_685,plain,
% 2.52/1.00      ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 2.52/1.00      | ~ v1_tops_2(X0,sK1)
% 2.52/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 2.52/1.00      | ~ v2_pre_topc(sK1)
% 2.52/1.00      | ~ l1_pre_topc(sK1) ),
% 2.52/1.00      inference(unflattening,[status(thm)],[c_684]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_689,plain,
% 2.52/1.00      ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 2.52/1.00      | ~ v1_tops_2(X0,sK1)
% 2.52/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
% 2.52/1.00      inference(global_propositional_subsumption,
% 2.52/1.00                [status(thm)],
% 2.52/1.00                [c_685,c_25,c_24]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_2485,plain,
% 2.52/1.00      ( v1_tops_2(X0_44,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 2.52/1.00      | ~ v1_tops_2(X0_44,sK1)
% 2.52/1.00      | ~ m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
% 2.52/1.00      inference(subtyping,[status(esa)],[c_689]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_3173,plain,
% 2.52/1.00      ( v1_tops_2(X0_44,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 2.52/1.00      | v1_tops_2(X0_44,sK1) != iProver_top
% 2.52/1.00      | m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
% 2.52/1.00      inference(predicate_to_equality,[status(thm)],[c_2485]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_4932,plain,
% 2.52/1.00      ( k5_tmap_1(sK1,sK2) = u1_pre_topc(sK1)
% 2.52/1.00      | v1_tops_2(X0_44,k6_tmap_1(sK1,sK2)) = iProver_top
% 2.52/1.00      | v1_tops_2(X0_44,sK1) != iProver_top
% 2.52/1.00      | m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
% 2.52/1.00      inference(superposition,[status(thm)],[c_4692,c_3173]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_30,plain,
% 2.52/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.52/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_16,plain,
% 2.52/1.00      ( r2_hidden(X0,k5_tmap_1(X1,X0))
% 2.52/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.52/1.00      | v2_struct_0(X1)
% 2.52/1.00      | ~ v2_pre_topc(X1)
% 2.52/1.00      | ~ l1_pre_topc(X1) ),
% 2.52/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_612,plain,
% 2.52/1.00      ( r2_hidden(X0,k5_tmap_1(X1,X0))
% 2.52/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.52/1.00      | ~ v2_pre_topc(X1)
% 2.52/1.00      | ~ l1_pre_topc(X1)
% 2.52/1.00      | sK1 != X1 ),
% 2.52/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_26]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_613,plain,
% 2.52/1.00      ( r2_hidden(X0,k5_tmap_1(sK1,X0))
% 2.52/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.52/1.00      | ~ v2_pre_topc(sK1)
% 2.52/1.00      | ~ l1_pre_topc(sK1) ),
% 2.52/1.00      inference(unflattening,[status(thm)],[c_612]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_617,plain,
% 2.52/1.00      ( r2_hidden(X0,k5_tmap_1(sK1,X0))
% 2.52/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.52/1.00      inference(global_propositional_subsumption,
% 2.52/1.00                [status(thm)],
% 2.52/1.00                [c_613,c_25,c_24]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_2488,plain,
% 2.52/1.00      ( r2_hidden(X0_44,k5_tmap_1(sK1,X0_44))
% 2.52/1.00      | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.52/1.00      inference(subtyping,[status(esa)],[c_617]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_2578,plain,
% 2.52/1.00      ( r2_hidden(X0_44,k5_tmap_1(sK1,X0_44)) = iProver_top
% 2.52/1.00      | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.52/1.00      inference(predicate_to_equality,[status(thm)],[c_2488]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_2580,plain,
% 2.52/1.00      ( r2_hidden(sK2,k5_tmap_1(sK1,sK2)) = iProver_top
% 2.52/1.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.52/1.00      inference(instantiation,[status(thm)],[c_2578]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_20,plain,
% 2.52/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.52/1.00      | v2_struct_0(X1)
% 2.52/1.00      | ~ v2_pre_topc(X1)
% 2.52/1.00      | ~ l1_pre_topc(X1)
% 2.52/1.00      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
% 2.52/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_534,plain,
% 2.52/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.52/1.00      | ~ v2_pre_topc(X1)
% 2.52/1.00      | ~ l1_pre_topc(X1)
% 2.52/1.00      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1)
% 2.52/1.00      | sK1 != X1 ),
% 2.52/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_26]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_535,plain,
% 2.52/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.52/1.00      | ~ v2_pre_topc(sK1)
% 2.52/1.00      | ~ l1_pre_topc(sK1)
% 2.52/1.00      | u1_struct_0(k6_tmap_1(sK1,X0)) = u1_struct_0(sK1) ),
% 2.52/1.00      inference(unflattening,[status(thm)],[c_534]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_539,plain,
% 2.52/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.52/1.00      | u1_struct_0(k6_tmap_1(sK1,X0)) = u1_struct_0(sK1) ),
% 2.52/1.00      inference(global_propositional_subsumption,
% 2.52/1.00                [status(thm)],
% 2.52/1.00                [c_535,c_25,c_24]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_2492,plain,
% 2.52/1.00      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.52/1.00      | u1_struct_0(k6_tmap_1(sK1,X0_44)) = u1_struct_0(sK1) ),
% 2.52/1.00      inference(subtyping,[status(esa)],[c_539]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_3166,plain,
% 2.52/1.00      ( u1_struct_0(k6_tmap_1(sK1,X0_44)) = u1_struct_0(sK1)
% 2.52/1.00      | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.52/1.00      inference(predicate_to_equality,[status(thm)],[c_2492]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_3440,plain,
% 2.52/1.00      ( u1_struct_0(k6_tmap_1(sK1,sK2)) = u1_struct_0(sK1) ),
% 2.52/1.00      inference(superposition,[status(thm)],[c_3164,c_3166]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_3,plain,
% 2.52/1.00      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.52/1.00      | ~ l1_pre_topc(X0) ),
% 2.52/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_2502,plain,
% 2.52/1.00      ( m1_subset_1(u1_pre_topc(X0_45),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0_45))))
% 2.52/1.00      | ~ l1_pre_topc(X0_45) ),
% 2.52/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_3156,plain,
% 2.52/1.00      ( m1_subset_1(u1_pre_topc(X0_45),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0_45)))) = iProver_top
% 2.52/1.00      | l1_pre_topc(X0_45) != iProver_top ),
% 2.52/1.00      inference(predicate_to_equality,[status(thm)],[c_2502]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_3613,plain,
% 2.52/1.00      ( m1_subset_1(u1_pre_topc(k6_tmap_1(sK1,sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
% 2.52/1.00      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 2.52/1.00      inference(superposition,[status(thm)],[c_3440,c_3156]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_14,plain,
% 2.52/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.52/1.00      | v2_struct_0(X1)
% 2.52/1.00      | ~ v2_pre_topc(X1)
% 2.52/1.00      | ~ l1_pre_topc(X1)
% 2.52/1.00      | l1_pre_topc(k6_tmap_1(X1,X0)) ),
% 2.52/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_648,plain,
% 2.52/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.52/1.00      | ~ v2_pre_topc(X1)
% 2.52/1.00      | ~ l1_pre_topc(X1)
% 2.52/1.00      | l1_pre_topc(k6_tmap_1(X1,X0))
% 2.52/1.00      | sK1 != X1 ),
% 2.52/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_26]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_649,plain,
% 2.52/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.52/1.00      | ~ v2_pre_topc(sK1)
% 2.52/1.00      | l1_pre_topc(k6_tmap_1(sK1,X0))
% 2.52/1.00      | ~ l1_pre_topc(sK1) ),
% 2.52/1.00      inference(unflattening,[status(thm)],[c_648]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_653,plain,
% 2.52/1.00      ( l1_pre_topc(k6_tmap_1(sK1,X0))
% 2.52/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.52/1.00      inference(global_propositional_subsumption,
% 2.52/1.00                [status(thm)],
% 2.52/1.00                [c_649,c_25,c_24]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_654,plain,
% 2.52/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.52/1.00      | l1_pre_topc(k6_tmap_1(sK1,X0)) ),
% 2.52/1.00      inference(renaming,[status(thm)],[c_653]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_2487,plain,
% 2.52/1.00      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.52/1.00      | l1_pre_topc(k6_tmap_1(sK1,X0_44)) ),
% 2.52/1.00      inference(subtyping,[status(esa)],[c_654]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_2581,plain,
% 2.52/1.00      ( m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.52/1.00      | l1_pre_topc(k6_tmap_1(sK1,X0_44)) = iProver_top ),
% 2.52/1.00      inference(predicate_to_equality,[status(thm)],[c_2487]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_2583,plain,
% 2.52/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.52/1.00      | l1_pre_topc(k6_tmap_1(sK1,sK2)) = iProver_top ),
% 2.52/1.00      inference(instantiation,[status(thm)],[c_2581]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_4331,plain,
% 2.52/1.00      ( m1_subset_1(u1_pre_topc(k6_tmap_1(sK1,sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
% 2.52/1.00      inference(global_propositional_subsumption,
% 2.52/1.00                [status(thm)],
% 2.52/1.00                [c_3613,c_30,c_2583]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_19,plain,
% 2.52/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.52/1.00      | v2_struct_0(X1)
% 2.52/1.00      | ~ v2_pre_topc(X1)
% 2.52/1.00      | ~ l1_pre_topc(X1)
% 2.52/1.00      | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0) ),
% 2.52/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_552,plain,
% 2.52/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.52/1.00      | ~ v2_pre_topc(X1)
% 2.52/1.00      | ~ l1_pre_topc(X1)
% 2.52/1.00      | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0)
% 2.52/1.00      | sK1 != X1 ),
% 2.52/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_26]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_553,plain,
% 2.52/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.52/1.00      | ~ v2_pre_topc(sK1)
% 2.52/1.00      | ~ l1_pre_topc(sK1)
% 2.52/1.00      | u1_pre_topc(k6_tmap_1(sK1,X0)) = k5_tmap_1(sK1,X0) ),
% 2.52/1.00      inference(unflattening,[status(thm)],[c_552]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_557,plain,
% 2.52/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.52/1.00      | u1_pre_topc(k6_tmap_1(sK1,X0)) = k5_tmap_1(sK1,X0) ),
% 2.52/1.00      inference(global_propositional_subsumption,
% 2.52/1.00                [status(thm)],
% 2.52/1.00                [c_553,c_25,c_24]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_2491,plain,
% 2.52/1.00      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.52/1.00      | u1_pre_topc(k6_tmap_1(sK1,X0_44)) = k5_tmap_1(sK1,X0_44) ),
% 2.52/1.00      inference(subtyping,[status(esa)],[c_557]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_3167,plain,
% 2.52/1.00      ( u1_pre_topc(k6_tmap_1(sK1,X0_44)) = k5_tmap_1(sK1,X0_44)
% 2.52/1.00      | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.52/1.00      inference(predicate_to_equality,[status(thm)],[c_2491]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_3856,plain,
% 2.52/1.00      ( u1_pre_topc(k6_tmap_1(sK1,sK2)) = k5_tmap_1(sK1,sK2) ),
% 2.52/1.00      inference(superposition,[status(thm)],[c_3164,c_3167]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_4335,plain,
% 2.52/1.00      ( m1_subset_1(k5_tmap_1(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
% 2.52/1.00      inference(light_normalisation,[status(thm)],[c_4331,c_3856]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_7,plain,
% 2.52/1.00      ( ~ v1_tops_2(X0,X1)
% 2.52/1.00      | v3_pre_topc(X2,X1)
% 2.52/1.00      | ~ r2_hidden(X2,X0)
% 2.52/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.52/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.52/1.00      | ~ l1_pre_topc(X1) ),
% 2.52/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_2498,plain,
% 2.52/1.00      ( ~ v1_tops_2(X0_44,X0_45)
% 2.52/1.00      | v3_pre_topc(X1_44,X0_45)
% 2.52/1.00      | ~ r2_hidden(X1_44,X0_44)
% 2.52/1.00      | ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(X0_45)))
% 2.52/1.00      | ~ m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0_45))))
% 2.52/1.00      | ~ l1_pre_topc(X0_45) ),
% 2.52/1.00      inference(subtyping,[status(esa)],[c_7]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_3160,plain,
% 2.52/1.00      ( v1_tops_2(X0_44,X0_45) != iProver_top
% 2.52/1.00      | v3_pre_topc(X1_44,X0_45) = iProver_top
% 2.52/1.00      | r2_hidden(X1_44,X0_44) != iProver_top
% 2.52/1.00      | m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(X0_45))) != iProver_top
% 2.52/1.00      | m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0_45)))) != iProver_top
% 2.52/1.00      | l1_pre_topc(X0_45) != iProver_top ),
% 2.52/1.00      inference(predicate_to_equality,[status(thm)],[c_2498]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_0,plain,
% 2.52/1.00      ( ~ r2_hidden(X0,X1)
% 2.52/1.00      | m1_subset_1(X0,X2)
% 2.52/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 2.52/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_2505,plain,
% 2.52/1.00      ( ~ r2_hidden(X0_44,X1_44)
% 2.52/1.00      | m1_subset_1(X0_44,X0_46)
% 2.52/1.00      | ~ m1_subset_1(X1_44,k1_zfmisc_1(X0_46)) ),
% 2.52/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_3153,plain,
% 2.52/1.00      ( r2_hidden(X0_44,X1_44) != iProver_top
% 2.52/1.00      | m1_subset_1(X0_44,X0_46) = iProver_top
% 2.52/1.00      | m1_subset_1(X1_44,k1_zfmisc_1(X0_46)) != iProver_top ),
% 2.52/1.00      inference(predicate_to_equality,[status(thm)],[c_2505]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_3305,plain,
% 2.52/1.00      ( v1_tops_2(X0_44,X0_45) != iProver_top
% 2.52/1.00      | v3_pre_topc(X1_44,X0_45) = iProver_top
% 2.52/1.00      | r2_hidden(X1_44,X0_44) != iProver_top
% 2.52/1.00      | m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0_45)))) != iProver_top
% 2.52/1.00      | l1_pre_topc(X0_45) != iProver_top ),
% 2.52/1.00      inference(forward_subsumption_resolution,
% 2.52/1.00                [status(thm)],
% 2.52/1.00                [c_3160,c_3153]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_4773,plain,
% 2.52/1.00      ( v1_tops_2(k5_tmap_1(sK1,sK2),sK1) != iProver_top
% 2.52/1.00      | v3_pre_topc(X0_44,sK1) = iProver_top
% 2.52/1.00      | r2_hidden(X0_44,k5_tmap_1(sK1,sK2)) != iProver_top
% 2.52/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.52/1.00      inference(superposition,[status(thm)],[c_4335,c_3305]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_4809,plain,
% 2.52/1.00      ( v1_tops_2(k5_tmap_1(sK1,sK2),sK1) != iProver_top
% 2.52/1.00      | v3_pre_topc(sK2,sK1) = iProver_top
% 2.52/1.00      | r2_hidden(sK2,k5_tmap_1(sK1,sK2)) != iProver_top
% 2.52/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.52/1.00      inference(instantiation,[status(thm)],[c_4773]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_10,plain,
% 2.52/1.00      ( v1_tops_2(X0,X1)
% 2.52/1.00      | ~ v1_tops_2(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.52/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
% 2.52/1.00      | v2_struct_0(X1)
% 2.52/1.00      | ~ v2_pre_topc(X1)
% 2.52/1.00      | ~ l1_pre_topc(X1) ),
% 2.52/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_726,plain,
% 2.52/1.00      ( v1_tops_2(X0,X1)
% 2.52/1.00      | ~ v1_tops_2(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.52/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
% 2.52/1.00      | ~ v2_pre_topc(X1)
% 2.52/1.00      | ~ l1_pre_topc(X1)
% 2.52/1.00      | sK1 != X1 ),
% 2.52/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_26]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_727,plain,
% 2.52/1.00      ( ~ v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 2.52/1.00      | v1_tops_2(X0,sK1)
% 2.52/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 2.52/1.00      | ~ v2_pre_topc(sK1)
% 2.52/1.00      | ~ l1_pre_topc(sK1) ),
% 2.52/1.00      inference(unflattening,[status(thm)],[c_726]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_731,plain,
% 2.52/1.00      ( ~ v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 2.52/1.00      | v1_tops_2(X0,sK1)
% 2.52/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
% 2.52/1.00      inference(global_propositional_subsumption,
% 2.52/1.00                [status(thm)],
% 2.52/1.00                [c_727,c_25,c_24]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_2483,plain,
% 2.52/1.00      ( ~ v1_tops_2(X0_44,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 2.52/1.00      | v1_tops_2(X0_44,sK1)
% 2.52/1.00      | ~ m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
% 2.52/1.00      inference(subtyping,[status(esa)],[c_731]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_3175,plain,
% 2.52/1.00      ( v1_tops_2(X0_44,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 2.52/1.00      | v1_tops_2(X0_44,sK1) = iProver_top
% 2.52/1.00      | m1_subset_1(X0_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
% 2.52/1.00      inference(predicate_to_equality,[status(thm)],[c_2483]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_4602,plain,
% 2.52/1.00      ( v1_tops_2(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 2.52/1.00      | v1_tops_2(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK1) = iProver_top
% 2.52/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 2.52/1.00      inference(superposition,[status(thm)],[c_3156,c_3175]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_8,plain,
% 2.52/1.00      ( v1_tops_2(u1_pre_topc(X0),X0) | ~ l1_pre_topc(X0) ),
% 2.52/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_2497,plain,
% 2.52/1.00      ( v1_tops_2(u1_pre_topc(X0_45),X0_45) | ~ l1_pre_topc(X0_45) ),
% 2.52/1.00      inference(subtyping,[status(esa)],[c_8]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_3370,plain,
% 2.52/1.00      ( v1_tops_2(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 2.52/1.00      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 2.52/1.00      inference(instantiation,[status(thm)],[c_2497]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_3373,plain,
% 2.52/1.00      ( v1_tops_2(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 2.52/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 2.52/1.00      inference(predicate_to_equality,[status(thm)],[c_3370]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_6109,plain,
% 2.52/1.00      ( v1_tops_2(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK1) = iProver_top
% 2.52/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 2.52/1.00      inference(global_propositional_subsumption,
% 2.52/1.00                [status(thm)],
% 2.52/1.00                [c_4602,c_3373]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_6115,plain,
% 2.52/1.00      ( k5_tmap_1(sK1,sK2) = u1_pre_topc(sK1)
% 2.52/1.00      | v1_tops_2(u1_pre_topc(k6_tmap_1(sK1,sK2)),sK1) = iProver_top
% 2.52/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 2.52/1.00      inference(superposition,[status(thm)],[c_4692,c_6109]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_6116,plain,
% 2.52/1.00      ( k5_tmap_1(sK1,sK2) = u1_pre_topc(sK1)
% 2.52/1.00      | v1_tops_2(k5_tmap_1(sK1,sK2),sK1) = iProver_top
% 2.52/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 2.52/1.00      inference(light_normalisation,[status(thm)],[c_6115,c_3856]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_69,plain,
% 2.52/1.00      ( v1_tops_2(u1_pre_topc(X0),X0) = iProver_top
% 2.52/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.52/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_71,plain,
% 2.52/1.00      ( v1_tops_2(u1_pre_topc(sK1),sK1) = iProver_top
% 2.52/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.52/1.00      inference(instantiation,[status(thm)],[c_69]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_2508,plain,( X0_45 = X0_45 ),theory(equality) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_2537,plain,
% 2.52/1.00      ( sK1 = sK1 ),
% 2.52/1.00      inference(instantiation,[status(thm)],[c_2508]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_2519,plain,
% 2.52/1.00      ( ~ l1_pre_topc(X0_45) | l1_pre_topc(X1_45) | X1_45 != X0_45 ),
% 2.52/1.00      theory(equality) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_3460,plain,
% 2.52/1.00      ( ~ l1_pre_topc(X0_45)
% 2.52/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 2.52/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != X0_45 ),
% 2.52/1.00      inference(instantiation,[status(thm)],[c_2519]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_3676,plain,
% 2.52/1.00      ( ~ l1_pre_topc(k6_tmap_1(sK1,sK2))
% 2.52/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 2.52/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k6_tmap_1(sK1,sK2) ),
% 2.52/1.00      inference(instantiation,[status(thm)],[c_3460]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_3677,plain,
% 2.52/1.00      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k6_tmap_1(sK1,sK2)
% 2.52/1.00      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top
% 2.52/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
% 2.52/1.00      inference(predicate_to_equality,[status(thm)],[c_3676]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_2520,plain,
% 2.52/1.00      ( ~ v1_tops_2(X0_44,X0_45)
% 2.52/1.00      | v1_tops_2(X1_44,X1_45)
% 2.52/1.00      | X1_45 != X0_45
% 2.52/1.00      | X1_44 != X0_44 ),
% 2.52/1.00      theory(equality) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_3432,plain,
% 2.52/1.00      ( v1_tops_2(X0_44,X0_45)
% 2.52/1.00      | ~ v1_tops_2(u1_pre_topc(X1_45),X1_45)
% 2.52/1.00      | X0_45 != X1_45
% 2.52/1.00      | X0_44 != u1_pre_topc(X1_45) ),
% 2.52/1.00      inference(instantiation,[status(thm)],[c_2520]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_4024,plain,
% 2.52/1.00      ( v1_tops_2(k5_tmap_1(sK1,X0_44),X0_45)
% 2.52/1.00      | ~ v1_tops_2(u1_pre_topc(sK1),sK1)
% 2.52/1.00      | X0_45 != sK1
% 2.52/1.00      | k5_tmap_1(sK1,X0_44) != u1_pre_topc(sK1) ),
% 2.52/1.00      inference(instantiation,[status(thm)],[c_3432]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_4025,plain,
% 2.52/1.00      ( X0_45 != sK1
% 2.52/1.00      | k5_tmap_1(sK1,X0_44) != u1_pre_topc(sK1)
% 2.52/1.00      | v1_tops_2(k5_tmap_1(sK1,X0_44),X0_45) = iProver_top
% 2.52/1.00      | v1_tops_2(u1_pre_topc(sK1),sK1) != iProver_top ),
% 2.52/1.00      inference(predicate_to_equality,[status(thm)],[c_4024]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_4027,plain,
% 2.52/1.00      ( sK1 != sK1
% 2.52/1.00      | k5_tmap_1(sK1,sK2) != u1_pre_topc(sK1)
% 2.52/1.00      | v1_tops_2(k5_tmap_1(sK1,sK2),sK1) = iProver_top
% 2.52/1.00      | v1_tops_2(u1_pre_topc(sK1),sK1) != iProver_top ),
% 2.52/1.00      inference(instantiation,[status(thm)],[c_4025]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_6972,plain,
% 2.52/1.00      ( v1_tops_2(k5_tmap_1(sK1,sK2),sK1) = iProver_top ),
% 2.52/1.00      inference(global_propositional_subsumption,
% 2.52/1.00                [status(thm)],
% 2.52/1.00                [c_6116,c_29,c_30,c_71,c_2537,c_2583,c_3677,c_4027,
% 2.52/1.00                 c_4692]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_7089,plain,
% 2.52/1.00      ( k5_tmap_1(sK1,sK2) = u1_pre_topc(sK1) ),
% 2.52/1.00      inference(global_propositional_subsumption,
% 2.52/1.00                [status(thm)],
% 2.52/1.00                [c_4932,c_29,c_30,c_71,c_2537,c_2580,c_2583,c_3677,
% 2.52/1.00                 c_4027,c_4412,c_4692,c_4809,c_6116]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_13,plain,
% 2.52/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.52/1.00      | v2_struct_0(X1)
% 2.52/1.00      | ~ v2_pre_topc(X1)
% 2.52/1.00      | ~ l1_pre_topc(X1)
% 2.52/1.00      | g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X0)) = k6_tmap_1(X1,X0) ),
% 2.52/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_666,plain,
% 2.52/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.52/1.00      | ~ v2_pre_topc(X1)
% 2.52/1.00      | ~ l1_pre_topc(X1)
% 2.52/1.00      | g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X0)) = k6_tmap_1(X1,X0)
% 2.52/1.00      | sK1 != X1 ),
% 2.52/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_26]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_667,plain,
% 2.52/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.52/1.00      | ~ v2_pre_topc(sK1)
% 2.52/1.00      | ~ l1_pre_topc(sK1)
% 2.52/1.00      | g1_pre_topc(u1_struct_0(sK1),k5_tmap_1(sK1,X0)) = k6_tmap_1(sK1,X0) ),
% 2.52/1.00      inference(unflattening,[status(thm)],[c_666]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_671,plain,
% 2.52/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.52/1.00      | g1_pre_topc(u1_struct_0(sK1),k5_tmap_1(sK1,X0)) = k6_tmap_1(sK1,X0) ),
% 2.52/1.00      inference(global_propositional_subsumption,
% 2.52/1.00                [status(thm)],
% 2.52/1.00                [c_667,c_25,c_24]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_2486,plain,
% 2.52/1.00      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.52/1.00      | g1_pre_topc(u1_struct_0(sK1),k5_tmap_1(sK1,X0_44)) = k6_tmap_1(sK1,X0_44) ),
% 2.52/1.00      inference(subtyping,[status(esa)],[c_671]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_3172,plain,
% 2.52/1.00      ( g1_pre_topc(u1_struct_0(sK1),k5_tmap_1(sK1,X0_44)) = k6_tmap_1(sK1,X0_44)
% 2.52/1.00      | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.52/1.00      inference(predicate_to_equality,[status(thm)],[c_2486]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_3946,plain,
% 2.52/1.00      ( g1_pre_topc(u1_struct_0(sK1),k5_tmap_1(sK1,sK2)) = k6_tmap_1(sK1,sK2) ),
% 2.52/1.00      inference(superposition,[status(thm)],[c_3164,c_3172]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_7099,plain,
% 2.52/1.00      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,sK2) ),
% 2.52/1.00      inference(demodulation,[status(thm)],[c_7089,c_3946]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_21,negated_conjecture,
% 2.52/1.00      ( ~ v3_pre_topc(sK2,sK1)
% 2.52/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k6_tmap_1(sK1,sK2) ),
% 2.52/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_2496,negated_conjecture,
% 2.52/1.00      ( ~ v3_pre_topc(sK2,sK1)
% 2.52/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k6_tmap_1(sK1,sK2) ),
% 2.52/1.00      inference(subtyping,[status(esa)],[c_21]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_2562,plain,
% 2.52/1.00      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k6_tmap_1(sK1,sK2)
% 2.52/1.00      | v3_pre_topc(sK2,sK1) != iProver_top ),
% 2.52/1.00      inference(predicate_to_equality,[status(thm)],[c_2496]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(contradiction,plain,
% 2.52/1.00      ( $false ),
% 2.52/1.00      inference(minisat,
% 2.52/1.00                [status(thm)],
% 2.52/1.00                [c_7099,c_6972,c_4809,c_2580,c_2562,c_30,c_29]) ).
% 2.52/1.00  
% 2.52/1.00  
% 2.52/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.52/1.00  
% 2.52/1.00  ------                               Statistics
% 2.52/1.00  
% 2.52/1.00  ------ General
% 2.52/1.00  
% 2.52/1.00  abstr_ref_over_cycles:                  0
% 2.52/1.00  abstr_ref_under_cycles:                 0
% 2.52/1.00  gc_basic_clause_elim:                   0
% 2.52/1.00  forced_gc_time:                         0
% 2.52/1.00  parsing_time:                           0.011
% 2.52/1.00  unif_index_cands_time:                  0.
% 2.52/1.00  unif_index_add_time:                    0.
% 2.52/1.00  orderings_time:                         0.
% 2.52/1.00  out_proof_time:                         0.01
% 2.52/1.00  total_time:                             0.238
% 2.52/1.00  num_of_symbols:                         47
% 2.52/1.00  num_of_terms:                           3811
% 2.52/1.00  
% 2.52/1.00  ------ Preprocessing
% 2.52/1.00  
% 2.52/1.00  num_of_splits:                          0
% 2.52/1.00  num_of_split_atoms:                     0
% 2.52/1.00  num_of_reused_defs:                     0
% 2.52/1.00  num_eq_ax_congr_red:                    10
% 2.52/1.00  num_of_sem_filtered_clauses:            1
% 2.52/1.00  num_of_subtypes:                        3
% 2.52/1.00  monotx_restored_types:                  0
% 2.52/1.00  sat_num_of_epr_types:                   0
% 2.52/1.00  sat_num_of_non_cyclic_types:            0
% 2.52/1.00  sat_guarded_non_collapsed_types:        0
% 2.52/1.00  num_pure_diseq_elim:                    0
% 2.52/1.00  simp_replaced_by:                       0
% 2.52/1.00  res_preprocessed:                       134
% 2.52/1.00  prep_upred:                             0
% 2.52/1.00  prep_unflattend:                        118
% 2.52/1.00  smt_new_axioms:                         0
% 2.52/1.00  pred_elim_cands:                        5
% 2.52/1.00  pred_elim:                              2
% 2.52/1.00  pred_elim_cl:                           3
% 2.52/1.00  pred_elim_cycles:                       8
% 2.52/1.00  merged_defs:                            8
% 2.52/1.00  merged_defs_ncl:                        0
% 2.52/1.00  bin_hyper_res:                          8
% 2.52/1.00  prep_cycles:                            4
% 2.52/1.00  pred_elim_time:                         0.059
% 2.52/1.00  splitting_time:                         0.
% 2.52/1.00  sem_filter_time:                        0.
% 2.52/1.00  monotx_time:                            0.
% 2.52/1.00  subtype_inf_time:                       0.
% 2.52/1.00  
% 2.52/1.00  ------ Problem properties
% 2.52/1.00  
% 2.52/1.00  clauses:                                24
% 2.52/1.00  conjectures:                            4
% 2.52/1.00  epr:                                    1
% 2.52/1.00  horn:                                   21
% 2.52/1.00  ground:                                 4
% 2.52/1.00  unary:                                  2
% 2.52/1.00  binary:                                 9
% 2.52/1.00  lits:                                   67
% 2.52/1.00  lits_eq:                                7
% 2.52/1.00  fd_pure:                                0
% 2.52/1.00  fd_pseudo:                              0
% 2.52/1.00  fd_cond:                                0
% 2.52/1.00  fd_pseudo_cond:                         0
% 2.52/1.00  ac_symbols:                             0
% 2.52/1.00  
% 2.52/1.00  ------ Propositional Solver
% 2.52/1.00  
% 2.52/1.00  prop_solver_calls:                      28
% 2.52/1.00  prop_fast_solver_calls:                 1550
% 2.52/1.00  smt_solver_calls:                       0
% 2.52/1.00  smt_fast_solver_calls:                  0
% 2.52/1.00  prop_num_of_clauses:                    1803
% 2.52/1.00  prop_preprocess_simplified:             6599
% 2.52/1.00  prop_fo_subsumed:                       81
% 2.52/1.00  prop_solver_time:                       0.
% 2.52/1.00  smt_solver_time:                        0.
% 2.52/1.00  smt_fast_solver_time:                   0.
% 2.52/1.00  prop_fast_solver_time:                  0.
% 2.52/1.00  prop_unsat_core_time:                   0.
% 2.52/1.00  
% 2.52/1.00  ------ QBF
% 2.52/1.00  
% 2.52/1.00  qbf_q_res:                              0
% 2.52/1.00  qbf_num_tautologies:                    0
% 2.52/1.00  qbf_prep_cycles:                        0
% 2.52/1.00  
% 2.52/1.00  ------ BMC1
% 2.52/1.00  
% 2.52/1.00  bmc1_current_bound:                     -1
% 2.52/1.00  bmc1_last_solved_bound:                 -1
% 2.52/1.00  bmc1_unsat_core_size:                   -1
% 2.52/1.00  bmc1_unsat_core_parents_size:           -1
% 2.52/1.00  bmc1_merge_next_fun:                    0
% 2.52/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.52/1.00  
% 2.52/1.00  ------ Instantiation
% 2.52/1.00  
% 2.52/1.00  inst_num_of_clauses:                    505
% 2.52/1.00  inst_num_in_passive:                    59
% 2.52/1.00  inst_num_in_active:                     289
% 2.52/1.00  inst_num_in_unprocessed:                157
% 2.52/1.00  inst_num_of_loops:                      340
% 2.52/1.00  inst_num_of_learning_restarts:          0
% 2.52/1.00  inst_num_moves_active_passive:          48
% 2.52/1.00  inst_lit_activity:                      0
% 2.52/1.00  inst_lit_activity_moves:                0
% 2.52/1.00  inst_num_tautologies:                   0
% 2.52/1.00  inst_num_prop_implied:                  0
% 2.52/1.00  inst_num_existing_simplified:           0
% 2.52/1.00  inst_num_eq_res_simplified:             0
% 2.52/1.00  inst_num_child_elim:                    0
% 2.52/1.00  inst_num_of_dismatching_blockings:      307
% 2.52/1.00  inst_num_of_non_proper_insts:           623
% 2.52/1.00  inst_num_of_duplicates:                 0
% 2.52/1.00  inst_inst_num_from_inst_to_res:         0
% 2.52/1.00  inst_dismatching_checking_time:         0.
% 2.52/1.00  
% 2.52/1.00  ------ Resolution
% 2.52/1.00  
% 2.52/1.00  res_num_of_clauses:                     0
% 2.52/1.00  res_num_in_passive:                     0
% 2.52/1.00  res_num_in_active:                      0
% 2.52/1.00  res_num_of_loops:                       138
% 2.52/1.00  res_forward_subset_subsumed:            39
% 2.52/1.00  res_backward_subset_subsumed:           0
% 2.52/1.00  res_forward_subsumed:                   0
% 2.52/1.00  res_backward_subsumed:                  0
% 2.52/1.00  res_forward_subsumption_resolution:     8
% 2.52/1.00  res_backward_subsumption_resolution:    0
% 2.52/1.00  res_clause_to_clause_subsumption:       262
% 2.52/1.00  res_orphan_elimination:                 0
% 2.52/1.00  res_tautology_del:                      113
% 2.52/1.00  res_num_eq_res_simplified:              0
% 2.52/1.00  res_num_sel_changes:                    0
% 2.52/1.00  res_moves_from_active_to_pass:          0
% 2.52/1.00  
% 2.52/1.00  ------ Superposition
% 2.52/1.00  
% 2.52/1.00  sup_time_total:                         0.
% 2.52/1.00  sup_time_generating:                    0.
% 2.52/1.00  sup_time_sim_full:                      0.
% 2.52/1.00  sup_time_sim_immed:                     0.
% 2.52/1.00  
% 2.52/1.00  sup_num_of_clauses:                     81
% 2.52/1.00  sup_num_in_active:                      49
% 2.52/1.00  sup_num_in_passive:                     32
% 2.52/1.00  sup_num_of_loops:                       66
% 2.52/1.00  sup_fw_superposition:                   60
% 2.52/1.00  sup_bw_superposition:                   61
% 2.52/1.00  sup_immediate_simplified:               38
% 2.52/1.00  sup_given_eliminated:                   0
% 2.52/1.00  comparisons_done:                       0
% 2.52/1.00  comparisons_avoided:                    3
% 2.52/1.00  
% 2.52/1.00  ------ Simplifications
% 2.52/1.00  
% 2.52/1.00  
% 2.52/1.00  sim_fw_subset_subsumed:                 14
% 2.52/1.00  sim_bw_subset_subsumed:                 15
% 2.52/1.00  sim_fw_subsumed:                        16
% 2.52/1.00  sim_bw_subsumed:                        0
% 2.52/1.00  sim_fw_subsumption_res:                 1
% 2.52/1.00  sim_bw_subsumption_res:                 0
% 2.52/1.00  sim_tautology_del:                      7
% 2.52/1.00  sim_eq_tautology_del:                   0
% 2.52/1.00  sim_eq_res_simp:                        0
% 2.52/1.00  sim_fw_demodulated:                     0
% 2.52/1.00  sim_bw_demodulated:                     10
% 2.52/1.00  sim_light_normalised:                   13
% 2.52/1.00  sim_joinable_taut:                      0
% 2.52/1.00  sim_joinable_simp:                      0
% 2.52/1.00  sim_ac_normalised:                      0
% 2.52/1.00  sim_smt_subsumption:                    0
% 2.52/1.00  
%------------------------------------------------------------------------------
