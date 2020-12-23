%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:59 EST 2020

% Result     : Theorem 52.00s
% Output     : CNFRefutation 52.00s
% Verified   : 
% Statistics : Number of formulae       :  431 (4162805 expanded)
%              Number of clauses        :  341 (1239329 expanded)
%              Number of leaves         :   20 (881965 expanded)
%              Depth                    :   57
%              Number of atoms          : 2113 (33606455 expanded)
%              Number of equality atoms : 1413 (2165100 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   28 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
                & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
                & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
                & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
            | ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
            | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
            | ~ v1_funct_1(k7_tmap_1(X0,X1))
            | ~ v3_pre_topc(X1,X0) )
          & ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) )
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
            | ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
            | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
            | ~ v1_funct_1(k7_tmap_1(X0,X1))
            | ~ v3_pre_topc(X1,X0) )
          & ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) )
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
            | ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
            | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
            | ~ v1_funct_1(k7_tmap_1(X0,X1))
            | ~ v3_pre_topc(X1,X0) )
          & ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) )
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ m1_subset_1(k7_tmap_1(X0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2)))))
          | ~ v5_pre_topc(k7_tmap_1(X0,sK2),X0,k6_tmap_1(X0,sK2))
          | ~ v1_funct_2(k7_tmap_1(X0,sK2),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2)))
          | ~ v1_funct_1(k7_tmap_1(X0,sK2))
          | ~ v3_pre_topc(sK2,X0) )
        & ( ( m1_subset_1(k7_tmap_1(X0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2)))))
            & v5_pre_topc(k7_tmap_1(X0,sK2),X0,k6_tmap_1(X0,sK2))
            & v1_funct_2(k7_tmap_1(X0,sK2),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2)))
            & v1_funct_1(k7_tmap_1(X0,sK2)) )
          | v3_pre_topc(sK2,X0) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              | ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              | ~ v1_funct_1(k7_tmap_1(X0,X1))
              | ~ v3_pre_topc(X1,X0) )
            & ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
                & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
                & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
                & v1_funct_1(k7_tmap_1(X0,X1)) )
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(k7_tmap_1(sK1,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X1)))))
            | ~ v5_pre_topc(k7_tmap_1(sK1,X1),sK1,k6_tmap_1(sK1,X1))
            | ~ v1_funct_2(k7_tmap_1(sK1,X1),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X1)))
            | ~ v1_funct_1(k7_tmap_1(sK1,X1))
            | ~ v3_pre_topc(X1,sK1) )
          & ( ( m1_subset_1(k7_tmap_1(sK1,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X1)))))
              & v5_pre_topc(k7_tmap_1(sK1,X1),sK1,k6_tmap_1(sK1,X1))
              & v1_funct_2(k7_tmap_1(sK1,X1),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X1)))
              & v1_funct_1(k7_tmap_1(sK1,X1)) )
            | v3_pre_topc(X1,sK1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ( ~ m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))))
      | ~ v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
      | ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
      | ~ v1_funct_1(k7_tmap_1(sK1,sK2))
      | ~ v3_pre_topc(sK2,sK1) )
    & ( ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))))
        & v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
        & v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
        & v1_funct_1(k7_tmap_1(sK1,sK2)) )
      | v3_pre_topc(sK2,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f52,f54,f53])).

fof(f91,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f66,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f63,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f92,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f55])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f89,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f90,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f95,plain,
    ( v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
    | v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f86,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f96,plain,
    ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( k2_struct_0(X1) = k1_xboole_0
                 => k2_struct_0(X0) = k1_xboole_0 )
               => ( v5_pre_topc(X2,X0,X1)
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( v3_pre_topc(X3,X1)
                       => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ( k2_struct_0(X0) != k1_xboole_0
                & k2_struct_0(X1) = k1_xboole_0 )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ( k2_struct_0(X0) != k1_xboole_0
                & k2_struct_0(X1) = k1_xboole_0 )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v3_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      | ~ v3_pre_topc(X3,X1)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ( k2_struct_0(X0) != k1_xboole_0
                & k2_struct_0(X1) = k1_xboole_0 )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v3_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v3_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ( k2_struct_0(X0) != k1_xboole_0
                & k2_struct_0(X1) = k1_xboole_0 )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f46])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v3_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
        & v3_pre_topc(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
                    & v3_pre_topc(sK0(X0,X1,X2),X1)
                    & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v3_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ( k2_struct_0(X0) != k1_xboole_0
                & k2_struct_0(X1) = k1_xboole_0 )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f47,f48])).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
      | ~ v3_pre_topc(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | k2_struct_0(X1) = k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f77,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
      | k2_struct_0(X1) = k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | k2_struct_0(X1) = k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f15,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,k6_tmap_1(X0,X1))
      | X1 != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f100,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,k6_tmap_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X2))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f88])).

fof(f94,plain,
    ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f97,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | ~ v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
    | ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ v1_funct_1(k7_tmap_1(sK1,sK2))
    | ~ v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f93,plain,
    ( v1_funct_1(k7_tmap_1(sK1,sK2))
    | v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f84,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(X0) = k5_tmap_1(X0,X1)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f87,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | v3_pre_topc(sK0(X0,X1,X2),X1)
      | k2_struct_0(X1) = k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | k2_struct_0(X0) != k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | u1_pre_topc(X0) != k5_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
      | ~ v3_pre_topc(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | k2_struct_0(X0) != k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
      | k2_struct_0(X0) != k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f98,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | v3_pre_topc(sK0(X0,X1,X2),X1)
      | k2_struct_0(X0) != k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_39,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1648,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_10,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1677,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2374,plain,
    ( l1_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1648,c_1677])).

cnf(c_7,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1680,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2461,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_2374,c_1680])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1649,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_2701,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2461,c_1649])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1668,plain,
    ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4991,plain,
    ( k7_tmap_1(sK1,X0) = k6_partfun1(u1_struct_0(sK1))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2461,c_1668])).

cnf(c_4997,plain,
    ( k7_tmap_1(sK1,X0) = k6_partfun1(k2_struct_0(sK1))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4991,c_2461])).

cnf(c_41,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_42,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_40,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_43,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_44,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_8319,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | k7_tmap_1(sK1,X0) = k6_partfun1(k2_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4997,c_42,c_43,c_44])).

cnf(c_8320,plain,
    ( k7_tmap_1(sK1,X0) = k6_partfun1(k2_struct_0(sK1))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_8319])).

cnf(c_8328,plain,
    ( k7_tmap_1(sK1,sK2) = k6_partfun1(k2_struct_0(sK1)) ),
    inference(superposition,[status(thm)],[c_2701,c_8320])).

cnf(c_35,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
    | v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1652,plain,
    ( v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_8346,plain,
    ( v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(sK2,sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8328,c_1652])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1656,plain,
    ( u1_struct_0(k6_tmap_1(X0,X1)) = u1_struct_0(X0)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3692,plain,
    ( u1_struct_0(k6_tmap_1(sK1,X0)) = u1_struct_0(sK1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2461,c_1656])).

cnf(c_3698,plain,
    ( u1_struct_0(k6_tmap_1(sK1,X0)) = k2_struct_0(sK1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3692,c_2461])).

cnf(c_4548,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | u1_struct_0(k6_tmap_1(sK1,X0)) = k2_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3698,c_42,c_43,c_44])).

cnf(c_4549,plain,
    ( u1_struct_0(k6_tmap_1(sK1,X0)) = k2_struct_0(sK1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4548])).

cnf(c_4557,plain,
    ( u1_struct_0(k6_tmap_1(sK1,sK2)) = k2_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_2701,c_4549])).

cnf(c_34,negated_conjecture,
    ( v3_pre_topc(sK2,sK1)
    | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1653,plain,
    ( v3_pre_topc(sK2,sK1) = iProver_top
    | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_45,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2285,plain,
    ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_2286,plain,
    ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2285])).

cnf(c_2335,plain,
    ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1653,c_42,c_43,c_44,c_45,c_2286])).

cnf(c_2699,plain,
    ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2461,c_2335])).

cnf(c_5158,plain,
    ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4557,c_2699])).

cnf(c_8343,plain,
    ( m1_subset_1(k6_partfun1(k2_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8328,c_5158])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ v3_pre_topc(X3,X2)
    | v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1669,plain,
    ( k2_struct_0(X0) = k1_xboole_0
    | v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X0)) != iProver_top
    | v5_pre_topc(X1,X2,X0) != iProver_top
    | v3_pre_topc(X3,X0) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X0),X1,X3),X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_7525,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | v5_pre_topc(X0,X1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(X2,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK1),X0,X2),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4557,c_1669])).

cnf(c_7536,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0,X1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(X2,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK1),X0,X2),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7525,c_4557])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k6_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1667,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(k6_tmap_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4957,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,X0)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2461,c_1667])).

cnf(c_7205,plain,
    ( l1_pre_topc(k6_tmap_1(sK1,X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4957,c_42,c_43,c_44])).

cnf(c_7206,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_7205])).

cnf(c_7214,plain,
    ( l1_pre_topc(k6_tmap_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2701,c_7206])).

cnf(c_7345,plain,
    ( l1_struct_0(k6_tmap_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7214,c_1677])).

cnf(c_7349,plain,
    ( u1_struct_0(k6_tmap_1(sK1,sK2)) = k2_struct_0(k6_tmap_1(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_7345,c_1680])).

cnf(c_7350,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_7349,c_4557])).

cnf(c_7537,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0,X1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(X2,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK1),X0,X2),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7536,c_7350])).

cnf(c_2212,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | l1_pre_topc(k6_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_2213,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2212])).

cnf(c_34853,plain,
    ( l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK1)))) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK1),X0,X2),X1) = iProver_top
    | v3_pre_topc(X2,k6_tmap_1(sK1,sK2)) != iProver_top
    | v5_pre_topc(X0,X1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK1)) != iProver_top
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7537,c_42,c_43,c_44,c_45,c_2213])).

cnf(c_34854,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0,X1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(X2,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK1),X0,X2),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_34853])).

cnf(c_34869,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0,u1_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(X1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0,X1),sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2461,c_34854])).

cnf(c_34995,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(X1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0,X1),sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_34869,c_2461])).

cnf(c_7522,plain,
    ( k2_struct_0(X0) = k1_xboole_0
    | v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0)) != iProver_top
    | v5_pre_topc(X1,sK1,X0) != iProver_top
    | v3_pre_topc(X2,X0) != iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0),X1,X2),sK1) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2461,c_1669])).

cnf(c_7600,plain,
    ( k2_struct_0(X0) = k1_xboole_0
    | v1_funct_2(X1,k2_struct_0(sK1),u1_struct_0(X0)) != iProver_top
    | v5_pre_topc(X1,sK1,X0) != iProver_top
    | v3_pre_topc(X2,X0) != iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0),X1,X2),sK1) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7522,c_2461])).

cnf(c_20630,plain,
    ( l1_pre_topc(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0)))) != iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0),X1,X2),sK1) = iProver_top
    | v3_pre_topc(X2,X0) != iProver_top
    | v5_pre_topc(X1,sK1,X0) != iProver_top
    | v1_funct_2(X1,k2_struct_0(sK1),u1_struct_0(X0)) != iProver_top
    | k2_struct_0(X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7600,c_44])).

cnf(c_20631,plain,
    ( k2_struct_0(X0) = k1_xboole_0
    | v1_funct_2(X1,k2_struct_0(sK1),u1_struct_0(X0)) != iProver_top
    | v5_pre_topc(X1,sK1,X0) != iProver_top
    | v3_pre_topc(X2,X0) != iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0),X1,X2),sK1) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_20630])).

cnf(c_20645,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | v1_funct_2(X0,k2_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(X1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0,X1),sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4557,c_20631])).

cnf(c_20676,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(X1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0,X1),sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_20645,c_4557])).

cnf(c_20677,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(X1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0,X1),sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_20676,c_7350])).

cnf(c_35437,plain,
    ( v1_funct_1(X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0,X1),sK1) = iProver_top
    | v3_pre_topc(X1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_34995,c_42,c_43,c_44,c_45,c_2213,c_20677])).

cnf(c_35438,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(X1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0,X1),sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_35437])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1675,plain,
    ( k2_struct_0(X0) = k1_xboole_0
    | v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X0)) != iProver_top
    | v5_pre_topc(X1,X2,X0) = iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X0),X1,sK0(X2,X0,X1)),X2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_8045,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0,X1,sK1) = iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK1),X0,sK0(X1,sK1,X0)),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2461,c_1675])).

cnf(c_8073,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0,X1,sK1) = iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK1),X0,sK0(X1,sK1,X0)),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8045,c_2461])).

cnf(c_17443,plain,
    ( l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK1)))) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK1),X0,sK0(X1,sK1,X0)),X1) != iProver_top
    | v5_pre_topc(X0,X1,sK1) = iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK1)) != iProver_top
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8073,c_44])).

cnf(c_17444,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0,X1,sK1) = iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK1),X0,sK0(X1,sK1,X0)),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_17443])).

cnf(c_17455,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0,u1_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0,sK1,sK1) = iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0,sK0(sK1,sK1,X0)),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2461,c_17444])).

cnf(c_17495,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0,sK1,sK1) = iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0,sK0(sK1,sK1,X0)),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17455,c_2461])).

cnf(c_18067,plain,
    ( v1_funct_1(X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0,sK0(sK1,sK1,X0)),sK1) != iProver_top
    | v5_pre_topc(X0,sK1,sK1) = iProver_top
    | v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_17495,c_44])).

cnf(c_18068,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0,sK1,sK1) = iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0,sK0(sK1,sK1,X0)),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_18067])).

cnf(c_35455,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v5_pre_topc(X0,sK1,sK1) = iProver_top
    | v3_pre_topc(sK0(sK1,sK1,X0),k6_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK1,X0),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_35438,c_18068])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1671,plain,
    ( k2_struct_0(X0) = k1_xboole_0
    | v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X0)) != iProver_top
    | v5_pre_topc(X1,X2,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(sK0(X2,X0,X1),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_7795,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0,X1,sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(X1,sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2461,c_1671])).

cnf(c_7823,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0,X1,sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(X1,sK1,X0),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7795,c_2461])).

cnf(c_16432,plain,
    ( l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | m1_subset_1(sK0(X1,sK1,X0),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK1)))) != iProver_top
    | v5_pre_topc(X0,X1,sK1) = iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK1)) != iProver_top
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7823,c_44])).

cnf(c_16433,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0,X1,sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(X1,sK1,X0),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_16432])).

cnf(c_16444,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0,u1_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0,sK1,sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK1,X0),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2461,c_16433])).

cnf(c_16484,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0,sK1,sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK1,X0),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16444,c_2461])).

cnf(c_16643,plain,
    ( v1_funct_1(X0) != iProver_top
    | m1_subset_1(sK0(sK1,sK1,X0),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | v5_pre_topc(X0,sK1,sK1) = iProver_top
    | v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_16484,c_44])).

cnf(c_16644,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0,sK1,sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK1,X0),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_16643])).

cnf(c_114115,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | v3_pre_topc(sK0(sK1,sK1,X0),k6_tmap_1(sK1,sK2)) != iProver_top
    | v5_pre_topc(X0,sK1,sK1) = iProver_top
    | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_35455,c_16644])).

cnf(c_114116,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v5_pre_topc(X0,sK1,sK1) = iProver_top
    | v3_pre_topc(sK0(sK1,sK1,X0),k6_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_114115])).

cnf(c_114129,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(k6_partfun1(k2_struct_0(sK1)),k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,sK1) = iProver_top
    | v3_pre_topc(sK0(sK1,sK1,k6_partfun1(k2_struct_0(sK1))),k6_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(k6_partfun1(k2_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8343,c_114116])).

cnf(c_32,plain,
    ( v3_pre_topc(X0,k6_tmap_1(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X0))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1655,plain,
    ( v3_pre_topc(X0,k6_tmap_1(X1,X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X0)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_5189,plain,
    ( v3_pre_topc(sK2,k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4557,c_1655])).

cnf(c_5196,plain,
    ( v3_pre_topc(sK2,k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5189,c_2461])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1651,plain,
    ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) = iProver_top
    | v3_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_23,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2289,plain,
    ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_2290,plain,
    ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2289])).

cnf(c_2296,plain,
    ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1651,c_42,c_43,c_44,c_45,c_2290])).

cnf(c_2700,plain,
    ( v1_funct_2(k7_tmap_1(sK1,sK2),k2_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2461,c_2296])).

cnf(c_5159,plain,
    ( v1_funct_2(k7_tmap_1(sK1,sK2),k2_struct_0(sK1),k2_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4557,c_2700])).

cnf(c_8344,plain,
    ( v1_funct_2(k6_partfun1(k2_struct_0(sK1)),k2_struct_0(sK1),k2_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8328,c_5159])).

cnf(c_33,negated_conjecture,
    ( ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
    | ~ v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | ~ v1_funct_1(k7_tmap_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1654,plain,
    ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_50,plain,
    ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k7_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2220,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | v1_funct_1(k7_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_2221,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k7_tmap_1(sK1,sK2)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2220])).

cnf(c_2228,plain,
    ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
    | v3_pre_topc(sK2,sK1) != iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1654,c_42,c_43,c_44,c_45,c_50,c_2221])).

cnf(c_2229,plain,
    ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2228])).

cnf(c_2340,plain,
    ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2335,c_2229])).

cnf(c_2688,plain,
    ( v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(sK2,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2340,c_42,c_43,c_44,c_45,c_50,c_2221,c_2286,c_2290])).

cnf(c_8345,plain,
    ( v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(sK2,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8328,c_2688])).

cnf(c_37,negated_conjecture,
    ( v3_pre_topc(sK2,sK1)
    | v1_funct_1(k7_tmap_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1650,plain,
    ( v3_pre_topc(sK2,sK1) = iProver_top
    | v1_funct_1(k7_tmap_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_2237,plain,
    ( v1_funct_1(k7_tmap_1(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1650,c_42,c_43,c_44,c_45,c_2221])).

cnf(c_8347,plain,
    ( v1_funct_1(k6_partfun1(k2_struct_0(sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8328,c_2237])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1682,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2452,plain,
    ( r1_tarski(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1649,c_1682])).

cnf(c_2698,plain,
    ( r1_tarski(sK2,k2_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2461,c_2452])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k8_relset_1(X1,X1,k6_partfun1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_285,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_286,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_285])).

cnf(c_357,plain,
    ( ~ r1_tarski(X0,X1)
    | k8_relset_1(X1,X1,k6_partfun1(X1),X0) = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_286])).

cnf(c_1645,plain,
    ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_357])).

cnf(c_3547,plain,
    ( k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),k6_partfun1(k2_struct_0(sK1)),sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_2698,c_1645])).

cnf(c_35453,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(k6_partfun1(k2_struct_0(sK1)),k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(sK2,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(sK2,sK1) = iProver_top
    | m1_subset_1(k6_partfun1(k2_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v1_funct_1(k6_partfun1(k2_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3547,c_35438])).

cnf(c_114369,plain,
    ( v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_114129,c_42,c_43,c_44,c_2701,c_5196,c_8343,c_8344,c_8345,c_8347,c_35453])).

cnf(c_114370,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_114369])).

cnf(c_114375,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v3_pre_topc(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_8346,c_114370])).

cnf(c_9,plain,
    ( r2_hidden(X0,u1_pre_topc(X1))
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1678,plain,
    ( r2_hidden(X0,u1_pre_topc(X1)) = iProver_top
    | v3_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3842,plain,
    ( r2_hidden(X0,u1_pre_topc(sK1)) = iProver_top
    | v3_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2461,c_1678])).

cnf(c_4159,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v3_pre_topc(X0,sK1) != iProver_top
    | r2_hidden(X0,u1_pre_topc(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3842,c_44])).

cnf(c_4160,plain,
    ( r2_hidden(X0,u1_pre_topc(sK1)) = iProver_top
    | v3_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4159])).

cnf(c_4169,plain,
    ( r2_hidden(sK2,u1_pre_topc(sK1)) = iProver_top
    | v3_pre_topc(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2701,c_4160])).

cnf(c_29,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) = u1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1658,plain,
    ( k5_tmap_1(X0,X1) = u1_pre_topc(X0)
    | r2_hidden(X1,u1_pre_topc(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5920,plain,
    ( k5_tmap_1(sK1,X0) = u1_pre_topc(sK1)
    | r2_hidden(X0,u1_pre_topc(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2461,c_1658])).

cnf(c_11382,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | r2_hidden(X0,u1_pre_topc(sK1)) != iProver_top
    | k5_tmap_1(sK1,X0) = u1_pre_topc(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5920,c_42,c_43,c_44])).

cnf(c_11383,plain,
    ( k5_tmap_1(sK1,X0) = u1_pre_topc(sK1)
    | r2_hidden(X0,u1_pre_topc(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_11382])).

cnf(c_11392,plain,
    ( k5_tmap_1(sK1,sK2) = u1_pre_topc(sK1)
    | r2_hidden(sK2,u1_pre_topc(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2701,c_11383])).

cnf(c_12936,plain,
    ( k5_tmap_1(sK1,sK2) = u1_pre_topc(sK1)
    | v3_pre_topc(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4169,c_11392])).

cnf(c_114380,plain,
    ( k5_tmap_1(sK1,sK2) = u1_pre_topc(sK1)
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_114375,c_12936])).

cnf(c_10077,plain,
    ( v3_pre_topc(sK2,k6_tmap_1(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5196,c_42,c_43,c_44,c_2701])).

cnf(c_1683,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3841,plain,
    ( r2_hidden(X0,u1_pre_topc(X1)) = iProver_top
    | v3_pre_topc(X0,X1) != iProver_top
    | r1_tarski(X0,u1_struct_0(X1)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1683,c_1678])).

cnf(c_13617,plain,
    ( r2_hidden(X0,u1_pre_topc(k6_tmap_1(sK1,sK2))) = iProver_top
    | v3_pre_topc(X0,k6_tmap_1(sK1,sK2)) != iProver_top
    | r1_tarski(X0,k2_struct_0(sK1)) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4557,c_3841])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1657,plain,
    ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4574,plain,
    ( u1_pre_topc(k6_tmap_1(sK1,X0)) = k5_tmap_1(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2461,c_1657])).

cnf(c_10083,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | u1_pre_topc(k6_tmap_1(sK1,X0)) = k5_tmap_1(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4574,c_42,c_43,c_44])).

cnf(c_10084,plain,
    ( u1_pre_topc(k6_tmap_1(sK1,X0)) = k5_tmap_1(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_10083])).

cnf(c_10092,plain,
    ( u1_pre_topc(k6_tmap_1(sK1,sK2)) = k5_tmap_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_2701,c_10084])).

cnf(c_13631,plain,
    ( r2_hidden(X0,k5_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(X0,k6_tmap_1(sK1,sK2)) != iProver_top
    | r1_tarski(X0,k2_struct_0(sK1)) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13617,c_10092])).

cnf(c_13917,plain,
    ( r1_tarski(X0,k2_struct_0(sK1)) != iProver_top
    | v3_pre_topc(X0,k6_tmap_1(sK1,sK2)) != iProver_top
    | r2_hidden(X0,k5_tmap_1(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13631,c_42,c_43,c_44,c_45,c_2213])).

cnf(c_13918,plain,
    ( r2_hidden(X0,k5_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(X0,k6_tmap_1(sK1,sK2)) != iProver_top
    | r1_tarski(X0,k2_struct_0(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_13917])).

cnf(c_13927,plain,
    ( r2_hidden(sK2,k5_tmap_1(sK1,sK2)) = iProver_top
    | r1_tarski(sK2,k2_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10077,c_13918])).

cnf(c_5188,plain,
    ( r2_hidden(X0,u1_pre_topc(k6_tmap_1(sK1,sK2))) = iProver_top
    | v3_pre_topc(X0,k6_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4557,c_1678])).

cnf(c_6679,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v3_pre_topc(X0,k6_tmap_1(sK1,sK2)) != iProver_top
    | r2_hidden(X0,u1_pre_topc(k6_tmap_1(sK1,sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5188,c_42,c_43,c_44,c_45,c_2213])).

cnf(c_6680,plain,
    ( r2_hidden(X0,u1_pre_topc(k6_tmap_1(sK1,sK2))) = iProver_top
    | v3_pre_topc(X0,k6_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6679])).

cnf(c_10269,plain,
    ( r2_hidden(X0,k5_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(X0,k6_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10092,c_6680])).

cnf(c_10798,plain,
    ( r2_hidden(sK2,k5_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_10077,c_10269])).

cnf(c_22570,plain,
    ( r2_hidden(sK2,k5_tmap_1(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13927,c_2701,c_10798])).

cnf(c_114707,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | r2_hidden(sK2,u1_pre_topc(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_114380,c_22570])).

cnf(c_1665,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0))))) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_7792,plain,
    ( k2_struct_0(k6_tmap_1(X0,X1)) = k1_xboole_0
    | v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) != iProver_top
    | v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(sK0(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1)),k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(k7_tmap_1(X0,X1)) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(k6_tmap_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1665,c_1671])).

cnf(c_78,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_41028,plain,
    ( k2_struct_0(k6_tmap_1(X0,X1)) = k1_xboole_0
    | v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(sK0(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1)),k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(k7_tmap_1(X0,X1)) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(k6_tmap_1(X0,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7792,c_78])).

cnf(c_1663,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v1_funct_1(k7_tmap_1(X1,X0)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_41043,plain,
    ( k2_struct_0(k6_tmap_1(X0,X1)) = k1_xboole_0
    | v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(sK0(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1)),k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_41028,c_1667,c_1663])).

cnf(c_41049,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(sK0(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2)),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4557,c_41043])).

cnf(c_41287,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_41049,c_2461,c_8328])).

cnf(c_41288,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_41287,c_7350])).

cnf(c_49596,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | m1_subset_1(sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_41288,c_42,c_43,c_44,c_2701,c_5196,c_8343,c_8344,c_8345,c_8347,c_35453])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(X1))
    | v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1679,plain,
    ( r2_hidden(X0,u1_pre_topc(X1)) != iProver_top
    | v3_pre_topc(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3991,plain,
    ( r2_hidden(X0,u1_pre_topc(sK1)) != iProver_top
    | v3_pre_topc(X0,sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2461,c_1679])).

cnf(c_4289,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v3_pre_topc(X0,sK1) = iProver_top
    | r2_hidden(X0,u1_pre_topc(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3991,c_44])).

cnf(c_4290,plain,
    ( r2_hidden(X0,u1_pre_topc(sK1)) != iProver_top
    | v3_pre_topc(X0,sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4289])).

cnf(c_49618,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | r2_hidden(sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),u1_pre_topc(sK1)) != iProver_top
    | v3_pre_topc(sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_49596,c_4290])).

cnf(c_49602,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | r1_tarski(sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k2_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_49596,c_1682])).

cnf(c_51806,plain,
    ( k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),k6_partfun1(k2_struct_0(sK1)),sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))) = sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_49602,c_1645])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1681,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3207,plain,
    ( k8_relset_1(k2_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)),k7_tmap_1(sK1,sK2),X0) = k10_relat_1(k7_tmap_1(sK1,sK2),X0) ),
    inference(superposition,[status(thm)],[c_2699,c_1681])).

cnf(c_5156,plain,
    ( k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),k7_tmap_1(sK1,sK2),X0) = k10_relat_1(k7_tmap_1(sK1,sK2),X0) ),
    inference(demodulation,[status(thm)],[c_4557,c_3207])).

cnf(c_8341,plain,
    ( k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),k6_partfun1(k2_struct_0(sK1)),X0) = k10_relat_1(k6_partfun1(k2_struct_0(sK1)),X0) ),
    inference(demodulation,[status(thm)],[c_8328,c_5156])).

cnf(c_51830,plain,
    ( k10_relat_1(k6_partfun1(k2_struct_0(sK1)),sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))) = sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_51806,c_8341])).

cnf(c_8046,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | v5_pre_topc(X0,X1,k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK1),X0,sK0(X1,k6_tmap_1(sK1,sK2),X0)),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4557,c_1675])).

cnf(c_8055,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0,X1,k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK1),X0,sK0(X1,k6_tmap_1(sK1,sK2),X0)),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8046,c_4557])).

cnf(c_8056,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0,X1,k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK1),X0,sK0(X1,k6_tmap_1(sK1,sK2),X0)),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8055,c_7350])).

cnf(c_48260,plain,
    ( l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK1)))) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK1),X0,sK0(X1,k6_tmap_1(sK1,sK2),X0)),X1) != iProver_top
    | v5_pre_topc(X0,X1,k6_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK1)) != iProver_top
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8056,c_42,c_43,c_44,c_45,c_2213])).

cnf(c_48261,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0,X1,k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK1),X0,sK0(X1,k6_tmap_1(sK1,sK2),X0)),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_48260])).

cnf(c_48276,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0,u1_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0,sK0(sK1,k6_tmap_1(sK1,sK2),X0)),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2461,c_48261])).

cnf(c_48309,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0,sK0(sK1,k6_tmap_1(sK1,sK2),X0)),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_48276,c_2461])).

cnf(c_8043,plain,
    ( k2_struct_0(X0) = k1_xboole_0
    | v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0)) != iProver_top
    | v5_pre_topc(X1,sK1,X0) = iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0),X1,sK0(sK1,X0,X1)),sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2461,c_1675])).

cnf(c_8107,plain,
    ( k2_struct_0(X0) = k1_xboole_0
    | v1_funct_2(X1,k2_struct_0(sK1),u1_struct_0(X0)) != iProver_top
    | v5_pre_topc(X1,sK1,X0) = iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0),X1,sK0(sK1,X0,X1)),sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0)))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8043,c_2461])).

cnf(c_18263,plain,
    ( l1_pre_topc(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0)))) != iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0),X1,sK0(sK1,X0,X1)),sK1) != iProver_top
    | v5_pre_topc(X1,sK1,X0) = iProver_top
    | v1_funct_2(X1,k2_struct_0(sK1),u1_struct_0(X0)) != iProver_top
    | k2_struct_0(X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8107,c_44])).

cnf(c_18264,plain,
    ( k2_struct_0(X0) = k1_xboole_0
    | v1_funct_2(X1,k2_struct_0(sK1),u1_struct_0(X0)) != iProver_top
    | v5_pre_topc(X1,sK1,X0) = iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0),X1,sK0(sK1,X0,X1)),sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0)))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_18263])).

cnf(c_18276,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | v1_funct_2(X0,k2_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0,sK0(sK1,k6_tmap_1(sK1,sK2),X0)),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4557,c_18264])).

cnf(c_18300,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0,sK0(sK1,k6_tmap_1(sK1,sK2),X0)),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_18276,c_4557])).

cnf(c_18301,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0,sK0(sK1,k6_tmap_1(sK1,sK2),X0)),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_18300,c_7350])).

cnf(c_48807,plain,
    ( v1_funct_1(X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0,sK0(sK1,k6_tmap_1(sK1,sK2),X0)),sK1) != iProver_top
    | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_48309,c_42,c_43,c_44,c_45,c_2213,c_18301])).

cnf(c_48808,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0,sK0(sK1,k6_tmap_1(sK1,sK2),X0)),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_48807])).

cnf(c_48822,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(k6_partfun1(k2_struct_0(sK1)),k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK1)),sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))),sK1) != iProver_top
    | m1_subset_1(k6_partfun1(k2_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k6_partfun1(k2_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8341,c_48808])).

cnf(c_95335,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK1)),sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))),sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_48822,c_42,c_43,c_44,c_2701,c_5196,c_8343,c_8344,c_8345,c_8347,c_35453])).

cnf(c_95341,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v3_pre_topc(sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_51830,c_95335])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | v3_pre_topc(sK0(X1,X2,X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1673,plain,
    ( k2_struct_0(X0) = k1_xboole_0
    | v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X0)) != iProver_top
    | v5_pre_topc(X1,X2,X0) = iProver_top
    | v3_pre_topc(sK0(X2,X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6551,plain,
    ( k2_struct_0(k6_tmap_1(X0,X1)) = k1_xboole_0
    | v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) != iProver_top
    | v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) = iProver_top
    | v3_pre_topc(sK0(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1)),k6_tmap_1(X0,X1)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(k7_tmap_1(X0,X1)) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(k6_tmap_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1665,c_1673])).

cnf(c_33511,plain,
    ( k2_struct_0(k6_tmap_1(X0,X1)) = k1_xboole_0
    | v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) = iProver_top
    | v3_pre_topc(sK0(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1)),k6_tmap_1(X0,X1)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(k7_tmap_1(X0,X1)) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(k6_tmap_1(X0,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6551,c_78])).

cnf(c_33526,plain,
    ( k2_struct_0(k6_tmap_1(X0,X1)) = k1_xboole_0
    | v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) = iProver_top
    | v3_pre_topc(sK0(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1)),k6_tmap_1(X0,X1)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_33511,c_1667,c_1663])).

cnf(c_33530,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_8328,c_33526])).

cnf(c_33610,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_33530,c_2461,c_8328])).

cnf(c_33611,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_33610,c_7350])).

cnf(c_49147,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v3_pre_topc(sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k6_tmap_1(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_33611,c_42,c_43,c_44,c_2701,c_5196,c_8343,c_8344,c_8345,c_8347,c_35453])).

cnf(c_49153,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | r2_hidden(sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k5_tmap_1(sK1,sK2)) = iProver_top
    | r1_tarski(sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k2_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_49147,c_13918])).

cnf(c_49154,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | r2_hidden(sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k5_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_49147,c_10269])).

cnf(c_49170,plain,
    ( r2_hidden(sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k5_tmap_1(sK1,sK2)) = iProver_top
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_49153,c_42,c_43,c_44,c_2701,c_5196,c_8343,c_8344,c_8345,c_8347,c_35453,c_41288,c_49154])).

cnf(c_49171,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | r2_hidden(sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k5_tmap_1(sK1,sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_49170])).

cnf(c_114703,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | r2_hidden(sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),u1_pre_topc(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_114380,c_49171])).

cnf(c_114963,plain,
    ( k2_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_114707,c_49618,c_95341,c_114703])).

cnf(c_115324,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_114963,c_8343])).

cnf(c_115345,plain,
    ( u1_struct_0(sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_114963,c_2461])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1672,plain,
    ( k2_struct_0(X0) != k1_xboole_0
    | v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(X2)) != iProver_top
    | v5_pre_topc(X1,X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(sK0(X0,X2,X1),k1_zfmisc_1(u1_struct_0(X2))) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_116997,plain,
    ( v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(X0,sK1,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(sK0(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_114963,c_1672])).

cnf(c_121528,plain,
    ( l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | m1_subset_1(sK0(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) != iProver_top
    | v5_pre_topc(X0,sK1,X1) = iProver_top
    | v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_116997,c_44])).

cnf(c_121529,plain,
    ( v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(X0,sK1,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(sK0(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_121528])).

cnf(c_121532,plain,
    ( v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(X0,sK1,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(sK0(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_121529,c_115345])).

cnf(c_121544,plain,
    ( v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(X0,sK1,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X1)))) != iProver_top
    | r1_tarski(sK0(sK1,X1,X0),u1_struct_0(X1)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_121532,c_1682])).

cnf(c_122063,plain,
    ( v1_funct_2(X0,k1_xboole_0,u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0,sK1,sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | r1_tarski(sK0(sK1,sK1,X0),u1_struct_0(sK1)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_115345,c_121544])).

cnf(c_122084,plain,
    ( v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(X0,sK1,sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | r1_tarski(sK0(sK1,sK1,X0),k1_xboole_0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_122063,c_115345])).

cnf(c_134344,plain,
    ( v1_funct_1(X0) != iProver_top
    | r1_tarski(sK0(sK1,sK1,X0),k1_xboole_0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v5_pre_topc(X0,sK1,sK1) = iProver_top
    | v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_122084,c_44])).

cnf(c_134345,plain,
    ( v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(X0,sK1,sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | r1_tarski(sK0(sK1,sK1,X0),k1_xboole_0) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_134344])).

cnf(c_134356,plain,
    ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(k6_partfun1(k1_xboole_0),sK1,sK1) = iProver_top
    | r1_tarski(sK0(sK1,sK1,k6_partfun1(k1_xboole_0)),k1_xboole_0) = iProver_top
    | v1_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_115324,c_134345])).

cnf(c_4299,plain,
    ( r2_hidden(sK2,u1_pre_topc(sK1)) != iProver_top
    | v3_pre_topc(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2701,c_4290])).

cnf(c_28,plain,
    ( r2_hidden(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) != u1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_6847,plain,
    ( r2_hidden(sK2,u1_pre_topc(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | k5_tmap_1(sK1,sK2) != u1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_6848,plain,
    ( k5_tmap_1(sK1,sK2) != u1_pre_topc(sK1)
    | r2_hidden(sK2,u1_pre_topc(sK1)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6847])).

cnf(c_12937,plain,
    ( ~ v3_pre_topc(sK2,sK1)
    | k5_tmap_1(sK1,sK2) = u1_pre_topc(sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_12936])).

cnf(c_115326,plain,
    ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_114963,c_8344])).

cnf(c_115327,plain,
    ( v5_pre_topc(k6_partfun1(k1_xboole_0),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(sK2,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_114963,c_8345])).

cnf(c_115329,plain,
    ( v1_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_114963,c_8347])).

cnf(c_743,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | v5_pre_topc(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_749,plain,
    ( X0 != X1
    | X2 != X3
    | k6_tmap_1(X0,X2) = k6_tmap_1(X1,X3) ),
    theory(equality)).

cnf(c_102316,plain,
    ( ~ v5_pre_topc(X0,X1,k6_tmap_1(X2,X3))
    | v5_pre_topc(X4,X5,k6_tmap_1(X6,X7))
    | X4 != X0
    | X5 != X1
    | X6 != X2
    | X7 != X3 ),
    inference(resolution,[status(thm)],[c_743,c_749])).

cnf(c_165921,plain,
    ( v5_pre_topc(X0,X1,k6_tmap_1(X2,X3))
    | v3_pre_topc(sK2,sK1)
    | X0 != k7_tmap_1(sK1,sK2)
    | X3 != sK2
    | X1 != sK1
    | X2 != sK1 ),
    inference(resolution,[status(thm)],[c_102316,c_35])).

cnf(c_2716,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2701])).

cnf(c_5307,plain,
    ( v3_pre_topc(sK2,k6_tmap_1(sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5196])).

cnf(c_116952,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_115324])).

cnf(c_116954,plain,
    ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_115326])).

cnf(c_115328,plain,
    ( v5_pre_topc(k6_partfun1(k1_xboole_0),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(sK2,sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_114963,c_8346])).

cnf(c_116956,plain,
    ( v5_pre_topc(k6_partfun1(k1_xboole_0),sK1,k6_tmap_1(sK1,sK2))
    | v3_pre_topc(sK2,sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_115328])).

cnf(c_116957,plain,
    ( v1_funct_1(k6_partfun1(k1_xboole_0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_115329])).

cnf(c_115344,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_114963,c_2701])).

cnf(c_116982,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_115344])).

cnf(c_115341,plain,
    ( k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK2) = sK2 ),
    inference(demodulation,[status(thm)],[c_114963,c_3547])).

cnf(c_115336,plain,
    ( u1_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_114963,c_4557])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ v3_pre_topc(X3,X2)
    | v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1670,plain,
    ( k2_struct_0(X0) != k1_xboole_0
    | v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(X2)) != iProver_top
    | v5_pre_topc(X1,X0,X2) != iProver_top
    | v3_pre_topc(X3,X2) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X3),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_116996,plain,
    ( v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(X0,sK1,X1) != iProver_top
    | v3_pre_topc(X2,X1) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X0,X2),sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_114963,c_1670])).

cnf(c_148047,plain,
    ( l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X0,X2),sK1) = iProver_top
    | v3_pre_topc(X2,X1) != iProver_top
    | v5_pre_topc(X0,sK1,X1) != iProver_top
    | v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_116996,c_44])).

cnf(c_148048,plain,
    ( v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(X0,sK1,X1) != iProver_top
    | v3_pre_topc(X2,X1) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X0,X2),sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_148047])).

cnf(c_148051,plain,
    ( v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(X0,sK1,X1) != iProver_top
    | v3_pre_topc(X2,X1) != iProver_top
    | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X1),X0,X2),sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_148048,c_115345])).

cnf(c_148065,plain,
    ( v1_funct_2(X0,k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(X1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0,X1),sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_115336,c_148051])).

cnf(c_148075,plain,
    ( v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(X1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0,X1),sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_148065,c_115336])).

cnf(c_148974,plain,
    ( v1_funct_1(X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0,X1),sK1) = iProver_top
    | v3_pre_topc(X1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_148075,c_42,c_43,c_44,c_45,c_2213])).

cnf(c_148975,plain,
    ( v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(X1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0,X1),sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_148974])).

cnf(c_148990,plain,
    ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(k6_partfun1(k1_xboole_0),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(sK2,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(sK2,sK1) = iProver_top
    | m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_115341,c_148975])).

cnf(c_149070,plain,
    ( ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ v5_pre_topc(k6_partfun1(k1_xboole_0),sK1,k6_tmap_1(sK1,sK2))
    | ~ v3_pre_topc(sK2,k6_tmap_1(sK1,sK2))
    | v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_1(k6_partfun1(k1_xboole_0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_148990])).

cnf(c_166127,plain,
    ( v3_pre_topc(sK2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_165921,c_41,c_40,c_39,c_2716,c_5307,c_116952,c_116954,c_116956,c_116957,c_116982,c_149070])).

cnf(c_148064,plain,
    ( v1_funct_2(X0,k1_xboole_0,u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0,sK1,sK1) != iProver_top
    | v3_pre_topc(X1,sK1) != iProver_top
    | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0,X1),sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_115345,c_148051])).

cnf(c_148092,plain,
    ( v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(X0,sK1,sK1) != iProver_top
    | v3_pre_topc(X1,sK1) != iProver_top
    | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0,X1),sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_148064,c_115345])).

cnf(c_148818,plain,
    ( v1_funct_1(X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0,X1),sK1) = iProver_top
    | v3_pre_topc(X1,sK1) != iProver_top
    | v5_pre_topc(X0,sK1,sK1) != iProver_top
    | v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_148092,c_44])).

cnf(c_148819,plain,
    ( v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(X0,sK1,sK1) != iProver_top
    | v3_pre_topc(X1,sK1) != iProver_top
    | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0,X1),sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_148818])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1676,plain,
    ( k2_struct_0(X0) != k1_xboole_0
    | v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(X2)) != iProver_top
    | v5_pre_topc(X1,X0,X2) = iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,sK0(X0,X2,X1)),X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_116995,plain,
    ( v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(X0,sK1,X1) = iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X0,sK0(sK1,X1,X0)),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_114963,c_1676])).

cnf(c_128802,plain,
    ( l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X0,sK0(sK1,X1,X0)),sK1) != iProver_top
    | v5_pre_topc(X0,sK1,X1) = iProver_top
    | v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_116995,c_44])).

cnf(c_128803,plain,
    ( v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(X0,sK1,X1) = iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X0,sK0(sK1,X1,X0)),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_128802])).

cnf(c_128806,plain,
    ( v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(X0,sK1,X1) = iProver_top
    | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X1),X0,sK0(sK1,X1,X0)),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_128803,c_115345])).

cnf(c_128818,plain,
    ( v1_funct_2(X0,k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0,sK0(sK1,k6_tmap_1(sK1,sK2),X0)),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_115336,c_128806])).

cnf(c_128825,plain,
    ( v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0,sK0(sK1,k6_tmap_1(sK1,sK2),X0)),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_128818,c_115336])).

cnf(c_129618,plain,
    ( v1_funct_1(X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0,sK0(sK1,k6_tmap_1(sK1,sK2),X0)),sK1) != iProver_top
    | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_128825,c_42,c_43,c_44,c_45,c_2213])).

cnf(c_129619,plain,
    ( v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0,sK0(sK1,k6_tmap_1(sK1,sK2),X0)),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_129618])).

cnf(c_148836,plain,
    ( v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | v5_pre_topc(X0,sK1,sK1) != iProver_top
    | v3_pre_topc(sK0(sK1,k6_tmap_1(sK1,sK2),X0),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(sK0(sK1,k6_tmap_1(sK1,sK2),X0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_148819,c_129619])).

cnf(c_121543,plain,
    ( v1_funct_2(X0,k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
    | m1_subset_1(sK0(sK1,k6_tmap_1(sK1,sK2),X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_115336,c_121532])).

cnf(c_121731,plain,
    ( v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(sK0(sK1,k6_tmap_1(sK1,sK2),X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_121543,c_115336])).

cnf(c_122064,plain,
    ( v1_funct_2(X0,k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | r1_tarski(sK0(sK1,k6_tmap_1(sK1,sK2),X0),u1_struct_0(k6_tmap_1(sK1,sK2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_115336,c_121544])).

cnf(c_122071,plain,
    ( v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | r1_tarski(sK0(sK1,k6_tmap_1(sK1,sK2),X0),k1_xboole_0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_122064,c_115336])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1684,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3545,plain,
    ( k8_relset_1(X0,X0,k6_partfun1(X0),X0) = X0 ),
    inference(superposition,[status(thm)],[c_1684,c_1645])).

cnf(c_148988,plain,
    ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(k6_partfun1(k1_xboole_0),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(k1_xboole_0,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(k1_xboole_0,sK1) = iProver_top
    | m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3545,c_148975])).

cnf(c_171517,plain,
    ( v5_pre_topc(k6_partfun1(k1_xboole_0),sK1,k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_148988,c_41,c_42,c_40,c_43,c_39,c_44,c_45,c_2716,c_4299,c_5307,c_6848,c_12937,c_116952,c_116954,c_115327,c_116956,c_116957,c_116982,c_149070])).

cnf(c_171527,plain,
    ( v3_pre_topc(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_115328,c_171517])).

cnf(c_171701,plain,
    ( k5_tmap_1(sK1,sK2) = u1_pre_topc(sK1) ),
    inference(superposition,[status(thm)],[c_171527,c_12936])).

cnf(c_121554,plain,
    ( v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(X0,sK1,X1) = iProver_top
    | r2_hidden(sK0(sK1,X1,X0),u1_pre_topc(X1)) = iProver_top
    | v3_pre_topc(sK0(sK1,X1,X0),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_121532,c_1678])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | v3_pre_topc(sK0(X1,X2,X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1674,plain,
    ( k2_struct_0(X0) != k1_xboole_0
    | v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(X2)) != iProver_top
    | v5_pre_topc(X1,X0,X2) = iProver_top
    | v3_pre_topc(sK0(X0,X2,X1),X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_116998,plain,
    ( v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(X0,sK1,X1) = iProver_top
    | v3_pre_topc(sK0(sK1,X1,X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_114963,c_1674])).

cnf(c_117656,plain,
    ( l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) != iProver_top
    | v3_pre_topc(sK0(sK1,X1,X0),X1) = iProver_top
    | v5_pre_topc(X0,sK1,X1) = iProver_top
    | v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_116998,c_44])).

cnf(c_117657,plain,
    ( v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(X0,sK1,X1) = iProver_top
    | v3_pre_topc(sK0(sK1,X1,X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_117656])).

cnf(c_118405,plain,
    ( v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(X0,sK1,X1) = iProver_top
    | v3_pre_topc(sK0(sK1,X1,X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_115345,c_117657])).

cnf(c_123853,plain,
    ( r2_hidden(sK0(sK1,X1,X0),u1_pre_topc(X1)) = iProver_top
    | v5_pre_topc(X0,sK1,X1) = iProver_top
    | v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_121554,c_118405])).

cnf(c_123854,plain,
    ( v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(X0,sK1,X1) = iProver_top
    | r2_hidden(sK0(sK1,X1,X0),u1_pre_topc(X1)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_123853])).

cnf(c_123867,plain,
    ( v1_funct_2(X0,k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | r2_hidden(sK0(sK1,k6_tmap_1(sK1,sK2),X0),u1_pre_topc(k6_tmap_1(sK1,sK2))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_115336,c_123854])).

cnf(c_123874,plain,
    ( v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | r2_hidden(sK0(sK1,k6_tmap_1(sK1,sK2),X0),k5_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_123867,c_10092,c_115336])).

cnf(c_124110,plain,
    ( v1_funct_1(X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | r2_hidden(sK0(sK1,k6_tmap_1(sK1,sK2),X0),k5_tmap_1(sK1,sK2)) = iProver_top
    | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_123874,c_42,c_43,c_44,c_45,c_2213])).

cnf(c_124111,plain,
    ( v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | r2_hidden(sK0(sK1,k6_tmap_1(sK1,sK2),X0),k5_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_124110])).

cnf(c_171726,plain,
    ( v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | r2_hidden(sK0(sK1,k6_tmap_1(sK1,sK2),X0),u1_pre_topc(sK1)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_171701,c_124111])).

cnf(c_4298,plain,
    ( r2_hidden(X0,u1_pre_topc(sK1)) != iProver_top
    | v3_pre_topc(X0,sK1) = iProver_top
    | r1_tarski(X0,k2_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1683,c_4290])).

cnf(c_115281,plain,
    ( r2_hidden(X0,u1_pre_topc(sK1)) != iProver_top
    | v3_pre_topc(X0,sK1) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_114963,c_4298])).

cnf(c_172510,plain,
    ( v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(sK0(sK1,k6_tmap_1(sK1,sK2),X0),sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | r1_tarski(sK0(sK1,k6_tmap_1(sK1,sK2),X0),k1_xboole_0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_171726,c_115281])).

cnf(c_176976,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | v5_pre_topc(X0,sK1,sK1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_148836,c_42,c_43,c_44,c_45,c_2213,c_121731,c_122071,c_172510])).

cnf(c_176977,plain,
    ( v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | v5_pre_topc(X0,sK1,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_176976])).

cnf(c_176988,plain,
    ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(k6_partfun1(k1_xboole_0),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | v5_pre_topc(k6_partfun1(k1_xboole_0),sK1,sK1) != iProver_top
    | v1_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_115324,c_176977])).

cnf(c_187327,plain,
    ( r1_tarski(sK0(sK1,sK1,k6_partfun1(k1_xboole_0)),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_134356,c_41,c_42,c_40,c_43,c_39,c_44,c_45,c_2716,c_4299,c_5307,c_6848,c_12937,c_116952,c_115326,c_116954,c_115327,c_116956,c_115329,c_116957,c_116982,c_149070,c_176988])).

cnf(c_187332,plain,
    ( k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK0(sK1,sK1,k6_partfun1(k1_xboole_0))) = sK0(sK1,sK1,k6_partfun1(k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_187327,c_1645])).

cnf(c_128817,plain,
    ( v1_funct_2(X0,k1_xboole_0,u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0,sK1,sK1) = iProver_top
    | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0,sK0(sK1,sK1,X0)),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_115345,c_128806])).

cnf(c_128838,plain,
    ( v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(X0,sK1,sK1) = iProver_top
    | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0,sK0(sK1,sK1,X0)),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_128817,c_115345])).

cnf(c_129397,plain,
    ( v1_funct_1(X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0,sK0(sK1,sK1,X0)),sK1) != iProver_top
    | v5_pre_topc(X0,sK1,sK1) = iProver_top
    | v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_128838,c_44])).

cnf(c_129398,plain,
    ( v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(X0,sK1,sK1) = iProver_top
    | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0,sK0(sK1,sK1,X0)),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_129397])).

cnf(c_188496,plain,
    ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(k6_partfun1(k1_xboole_0),sK1,sK1) = iProver_top
    | v3_pre_topc(sK0(sK1,sK1,k6_partfun1(k1_xboole_0)),sK1) != iProver_top
    | m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_187332,c_129398])).

cnf(c_136185,plain,
    ( v1_funct_2(X0,k1_xboole_0,u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0,sK1,sK1) = iProver_top
    | v3_pre_topc(sK0(sK1,sK1,X0),sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_115345,c_118405])).

cnf(c_136206,plain,
    ( v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(X0,sK1,sK1) = iProver_top
    | v3_pre_topc(sK0(sK1,sK1,X0),sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_136185,c_115345])).

cnf(c_136528,plain,
    ( v1_funct_1(X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v3_pre_topc(sK0(sK1,sK1,X0),sK1) = iProver_top
    | v5_pre_topc(X0,sK1,sK1) = iProver_top
    | v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_136206,c_44])).

cnf(c_136529,plain,
    ( v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(X0,sK1,sK1) = iProver_top
    | v3_pre_topc(sK0(sK1,sK1,X0),sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_136528])).

cnf(c_136540,plain,
    ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(k6_partfun1(k1_xboole_0),sK1,sK1) = iProver_top
    | v3_pre_topc(sK0(sK1,sK1,k6_partfun1(k1_xboole_0)),sK1) = iProver_top
    | v1_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_115324,c_136529])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_188496,c_176988,c_166127,c_136540,c_115329,c_115327,c_115326,c_115324,c_12937,c_6848,c_4299,c_45,c_44,c_43,c_42])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:18:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 52.00/7.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 52.00/7.00  
% 52.00/7.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 52.00/7.00  
% 52.00/7.00  ------  iProver source info
% 52.00/7.00  
% 52.00/7.00  git: date: 2020-06-30 10:37:57 +0100
% 52.00/7.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 52.00/7.00  git: non_committed_changes: false
% 52.00/7.00  git: last_make_outside_of_git: false
% 52.00/7.00  
% 52.00/7.00  ------ 
% 52.00/7.00  ------ Parsing...
% 52.00/7.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 52.00/7.00  
% 52.00/7.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 52.00/7.00  
% 52.00/7.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 52.00/7.00  
% 52.00/7.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 52.00/7.00  ------ Proving...
% 52.00/7.00  ------ Problem Properties 
% 52.00/7.00  
% 52.00/7.00  
% 52.00/7.00  clauses                                 41
% 52.00/7.00  conjectures                             9
% 52.00/7.00  EPR                                     6
% 52.00/7.00  Horn                                    17
% 52.00/7.00  unary                                   5
% 52.00/7.00  binary                                  10
% 52.00/7.00  lits                                    179
% 52.00/7.00  lits eq                                 17
% 52.00/7.00  fd_pure                                 0
% 52.00/7.00  fd_pseudo                               0
% 52.00/7.00  fd_cond                                 0
% 52.00/7.00  fd_pseudo_cond                          1
% 52.00/7.00  AC symbols                              0
% 52.00/7.00  
% 52.00/7.00  ------ Input Options Time Limit: Unbounded
% 52.00/7.00  
% 52.00/7.00  
% 52.00/7.00  ------ 
% 52.00/7.00  Current options:
% 52.00/7.00  ------ 
% 52.00/7.00  
% 52.00/7.00  
% 52.00/7.00  
% 52.00/7.00  
% 52.00/7.00  ------ Proving...
% 52.00/7.00  
% 52.00/7.00  
% 52.00/7.00  % SZS status Theorem for theBenchmark.p
% 52.00/7.00  
% 52.00/7.00  % SZS output start CNFRefutation for theBenchmark.p
% 52.00/7.00  
% 52.00/7.00  fof(f16,conjecture,(
% 52.00/7.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))))),
% 52.00/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 52.00/7.00  
% 52.00/7.00  fof(f17,negated_conjecture,(
% 52.00/7.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))))),
% 52.00/7.00    inference(negated_conjecture,[],[f16])).
% 52.00/7.00  
% 52.00/7.00  fof(f40,plain,(
% 52.00/7.00    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 52.00/7.00    inference(ennf_transformation,[],[f17])).
% 52.00/7.00  
% 52.00/7.00  fof(f41,plain,(
% 52.00/7.00    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 52.00/7.00    inference(flattening,[],[f40])).
% 52.00/7.00  
% 52.00/7.00  fof(f51,plain,(
% 52.00/7.00    ? [X0] : (? [X1] : ((((~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1))) | ~v3_pre_topc(X1,X0)) & ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 52.00/7.00    inference(nnf_transformation,[],[f41])).
% 52.00/7.00  
% 52.00/7.00  fof(f52,plain,(
% 52.00/7.00    ? [X0] : (? [X1] : ((~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1)) | ~v3_pre_topc(X1,X0)) & ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 52.00/7.00    inference(flattening,[],[f51])).
% 52.00/7.00  
% 52.00/7.00  fof(f54,plain,(
% 52.00/7.00    ( ! [X0] : (? [X1] : ((~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1)) | ~v3_pre_topc(X1,X0)) & ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((~m1_subset_1(k7_tmap_1(X0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2))))) | ~v5_pre_topc(k7_tmap_1(X0,sK2),X0,k6_tmap_1(X0,sK2)) | ~v1_funct_2(k7_tmap_1(X0,sK2),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2))) | ~v1_funct_1(k7_tmap_1(X0,sK2)) | ~v3_pre_topc(sK2,X0)) & ((m1_subset_1(k7_tmap_1(X0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2))))) & v5_pre_topc(k7_tmap_1(X0,sK2),X0,k6_tmap_1(X0,sK2)) & v1_funct_2(k7_tmap_1(X0,sK2),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2))) & v1_funct_1(k7_tmap_1(X0,sK2))) | v3_pre_topc(sK2,X0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 52.00/7.00    introduced(choice_axiom,[])).
% 52.00/7.00  
% 52.00/7.00  fof(f53,plain,(
% 52.00/7.00    ? [X0] : (? [X1] : ((~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1)) | ~v3_pre_topc(X1,X0)) & ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~m1_subset_1(k7_tmap_1(sK1,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X1))))) | ~v5_pre_topc(k7_tmap_1(sK1,X1),sK1,k6_tmap_1(sK1,X1)) | ~v1_funct_2(k7_tmap_1(sK1,X1),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X1))) | ~v1_funct_1(k7_tmap_1(sK1,X1)) | ~v3_pre_topc(X1,sK1)) & ((m1_subset_1(k7_tmap_1(sK1,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X1))))) & v5_pre_topc(k7_tmap_1(sK1,X1),sK1,k6_tmap_1(sK1,X1)) & v1_funct_2(k7_tmap_1(sK1,X1),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X1))) & v1_funct_1(k7_tmap_1(sK1,X1))) | v3_pre_topc(X1,sK1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 52.00/7.00    introduced(choice_axiom,[])).
% 52.00/7.00  
% 52.00/7.00  fof(f55,plain,(
% 52.00/7.00    ((~m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) | ~v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) | ~v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) | ~v1_funct_1(k7_tmap_1(sK1,sK2)) | ~v3_pre_topc(sK2,sK1)) & ((m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) & v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) & v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) & v1_funct_1(k7_tmap_1(sK1,sK2))) | v3_pre_topc(sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 52.00/7.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f52,f54,f53])).
% 52.00/7.00  
% 52.00/7.00  fof(f91,plain,(
% 52.00/7.00    l1_pre_topc(sK1)),
% 52.00/7.00    inference(cnf_transformation,[],[f55])).
% 52.00/7.00  
% 52.00/7.00  fof(f7,axiom,(
% 52.00/7.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 52.00/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 52.00/7.00  
% 52.00/7.00  fof(f23,plain,(
% 52.00/7.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 52.00/7.00    inference(ennf_transformation,[],[f7])).
% 52.00/7.00  
% 52.00/7.00  fof(f66,plain,(
% 52.00/7.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 52.00/7.00    inference(cnf_transformation,[],[f23])).
% 52.00/7.00  
% 52.00/7.00  fof(f5,axiom,(
% 52.00/7.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 52.00/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 52.00/7.00  
% 52.00/7.00  fof(f21,plain,(
% 52.00/7.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 52.00/7.00    inference(ennf_transformation,[],[f5])).
% 52.00/7.00  
% 52.00/7.00  fof(f63,plain,(
% 52.00/7.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 52.00/7.00    inference(cnf_transformation,[],[f21])).
% 52.00/7.00  
% 52.00/7.00  fof(f92,plain,(
% 52.00/7.00    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 52.00/7.00    inference(cnf_transformation,[],[f55])).
% 52.00/7.00  
% 52.00/7.00  fof(f9,axiom,(
% 52.00/7.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,X1)))),
% 52.00/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 52.00/7.00  
% 52.00/7.00  fof(f26,plain,(
% 52.00/7.00    ! [X0] : (! [X1] : (k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 52.00/7.00    inference(ennf_transformation,[],[f9])).
% 52.00/7.00  
% 52.00/7.00  fof(f27,plain,(
% 52.00/7.00    ! [X0] : (! [X1] : (k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 52.00/7.00    inference(flattening,[],[f26])).
% 52.00/7.00  
% 52.00/7.00  fof(f75,plain,(
% 52.00/7.00    ( ! [X0,X1] : (k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 52.00/7.00    inference(cnf_transformation,[],[f27])).
% 52.00/7.00  
% 52.00/7.00  fof(f89,plain,(
% 52.00/7.00    ~v2_struct_0(sK1)),
% 52.00/7.00    inference(cnf_transformation,[],[f55])).
% 52.00/7.00  
% 52.00/7.00  fof(f90,plain,(
% 52.00/7.00    v2_pre_topc(sK1)),
% 52.00/7.00    inference(cnf_transformation,[],[f55])).
% 52.00/7.00  
% 52.00/7.00  fof(f95,plain,(
% 52.00/7.00    v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) | v3_pre_topc(sK2,sK1)),
% 52.00/7.00    inference(cnf_transformation,[],[f55])).
% 52.00/7.00  
% 52.00/7.00  fof(f14,axiom,(
% 52.00/7.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 52.00/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 52.00/7.00  
% 52.00/7.00  fof(f36,plain,(
% 52.00/7.00    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 52.00/7.00    inference(ennf_transformation,[],[f14])).
% 52.00/7.00  
% 52.00/7.00  fof(f37,plain,(
% 52.00/7.00    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 52.00/7.00    inference(flattening,[],[f36])).
% 52.00/7.00  
% 52.00/7.00  fof(f86,plain,(
% 52.00/7.00    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 52.00/7.00    inference(cnf_transformation,[],[f37])).
% 52.00/7.00  
% 52.00/7.00  fof(f96,plain,(
% 52.00/7.00    m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) | v3_pre_topc(sK2,sK1)),
% 52.00/7.00    inference(cnf_transformation,[],[f55])).
% 52.00/7.00  
% 52.00/7.00  fof(f11,axiom,(
% 52.00/7.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 52.00/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 52.00/7.00  
% 52.00/7.00  fof(f30,plain,(
% 52.00/7.00    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 52.00/7.00    inference(ennf_transformation,[],[f11])).
% 52.00/7.00  
% 52.00/7.00  fof(f31,plain,(
% 52.00/7.00    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 52.00/7.00    inference(flattening,[],[f30])).
% 52.00/7.00  
% 52.00/7.00  fof(f80,plain,(
% 52.00/7.00    ( ! [X0,X1] : (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 52.00/7.00    inference(cnf_transformation,[],[f31])).
% 52.00/7.00  
% 52.00/7.00  fof(f8,axiom,(
% 52.00/7.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_struct_0(X1) = k1_xboole_0 => k2_struct_0(X0) = k1_xboole_0) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v3_pre_topc(X3,X1) => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0))))))))),
% 52.00/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 52.00/7.00  
% 52.00/7.00  fof(f24,plain,(
% 52.00/7.00    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k2_struct_0(X0) != k1_xboole_0 & k2_struct_0(X1) = k1_xboole_0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 52.00/7.00    inference(ennf_transformation,[],[f8])).
% 52.00/7.00  
% 52.00/7.00  fof(f25,plain,(
% 52.00/7.00    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k2_struct_0(X0) != k1_xboole_0 & k2_struct_0(X1) = k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 52.00/7.00    inference(flattening,[],[f24])).
% 52.00/7.00  
% 52.00/7.00  fof(f46,plain,(
% 52.00/7.00    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k2_struct_0(X0) != k1_xboole_0 & k2_struct_0(X1) = k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 52.00/7.00    inference(nnf_transformation,[],[f25])).
% 52.00/7.00  
% 52.00/7.00  fof(f47,plain,(
% 52.00/7.00    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k2_struct_0(X0) != k1_xboole_0 & k2_struct_0(X1) = k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 52.00/7.00    inference(rectify,[],[f46])).
% 52.00/7.00  
% 52.00/7.00  fof(f48,plain,(
% 52.00/7.00    ! [X2,X1,X0] : (? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) & v3_pre_topc(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 52.00/7.00    introduced(choice_axiom,[])).
% 52.00/7.00  
% 52.00/7.00  fof(f49,plain,(
% 52.00/7.00    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) & v3_pre_topc(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k2_struct_0(X0) != k1_xboole_0 & k2_struct_0(X1) = k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 52.00/7.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f47,f48])).
% 52.00/7.00  
% 52.00/7.00  fof(f67,plain,(
% 52.00/7.00    ( ! [X4,X2,X0,X1] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v5_pre_topc(X2,X0,X1) | k2_struct_0(X1) = k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 52.00/7.00    inference(cnf_transformation,[],[f49])).
% 52.00/7.00  
% 52.00/7.00  fof(f10,axiom,(
% 52.00/7.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))))),
% 52.00/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 52.00/7.00  
% 52.00/7.00  fof(f18,plain,(
% 52.00/7.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))))),
% 52.00/7.00    inference(pure_predicate_removal,[],[f10])).
% 52.00/7.00  
% 52.00/7.00  fof(f28,plain,(
% 52.00/7.00    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 52.00/7.00    inference(ennf_transformation,[],[f18])).
% 52.00/7.00  
% 52.00/7.00  fof(f29,plain,(
% 52.00/7.00    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 52.00/7.00    inference(flattening,[],[f28])).
% 52.00/7.00  
% 52.00/7.00  fof(f77,plain,(
% 52.00/7.00    ( ! [X0,X1] : (l1_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 52.00/7.00    inference(cnf_transformation,[],[f29])).
% 52.00/7.00  
% 52.00/7.00  fof(f73,plain,(
% 52.00/7.00    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) | k2_struct_0(X1) = k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 52.00/7.00    inference(cnf_transformation,[],[f49])).
% 52.00/7.00  
% 52.00/7.00  fof(f69,plain,(
% 52.00/7.00    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | k2_struct_0(X1) = k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 52.00/7.00    inference(cnf_transformation,[],[f49])).
% 52.00/7.00  
% 52.00/7.00  fof(f15,axiom,(
% 52.00/7.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) => (X1 = X2 => v3_pre_topc(X2,k6_tmap_1(X0,X1))))))),
% 52.00/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 52.00/7.00  
% 52.00/7.00  fof(f38,plain,(
% 52.00/7.00    ! [X0] : (! [X1] : (! [X2] : ((v3_pre_topc(X2,k6_tmap_1(X0,X1)) | X1 != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 52.00/7.00    inference(ennf_transformation,[],[f15])).
% 52.00/7.00  
% 52.00/7.00  fof(f39,plain,(
% 52.00/7.00    ! [X0] : (! [X1] : (! [X2] : (v3_pre_topc(X2,k6_tmap_1(X0,X1)) | X1 != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 52.00/7.00    inference(flattening,[],[f38])).
% 52.00/7.00  
% 52.00/7.00  fof(f88,plain,(
% 52.00/7.00    ( ! [X2,X0,X1] : (v3_pre_topc(X2,k6_tmap_1(X0,X1)) | X1 != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 52.00/7.00    inference(cnf_transformation,[],[f39])).
% 52.00/7.00  
% 52.00/7.00  fof(f100,plain,(
% 52.00/7.00    ( ! [X2,X0] : (v3_pre_topc(X2,k6_tmap_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 52.00/7.00    inference(equality_resolution,[],[f88])).
% 52.00/7.00  
% 52.00/7.00  fof(f94,plain,(
% 52.00/7.00    v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) | v3_pre_topc(sK2,sK1)),
% 52.00/7.00    inference(cnf_transformation,[],[f55])).
% 52.00/7.00  
% 52.00/7.00  fof(f79,plain,(
% 52.00/7.00    ( ! [X0,X1] : (v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 52.00/7.00    inference(cnf_transformation,[],[f31])).
% 52.00/7.00  
% 52.00/7.00  fof(f97,plain,(
% 52.00/7.00    ~m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) | ~v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) | ~v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) | ~v1_funct_1(k7_tmap_1(sK1,sK2)) | ~v3_pre_topc(sK2,sK1)),
% 52.00/7.00    inference(cnf_transformation,[],[f55])).
% 52.00/7.00  
% 52.00/7.00  fof(f78,plain,(
% 52.00/7.00    ( ! [X0,X1] : (v1_funct_1(k7_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 52.00/7.00    inference(cnf_transformation,[],[f31])).
% 52.00/7.00  
% 52.00/7.00  fof(f93,plain,(
% 52.00/7.00    v1_funct_1(k7_tmap_1(sK1,sK2)) | v3_pre_topc(sK2,sK1)),
% 52.00/7.00    inference(cnf_transformation,[],[f55])).
% 52.00/7.00  
% 52.00/7.00  fof(f2,axiom,(
% 52.00/7.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 52.00/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 52.00/7.00  
% 52.00/7.00  fof(f44,plain,(
% 52.00/7.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 52.00/7.00    inference(nnf_transformation,[],[f2])).
% 52.00/7.00  
% 52.00/7.00  fof(f59,plain,(
% 52.00/7.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 52.00/7.00    inference(cnf_transformation,[],[f44])).
% 52.00/7.00  
% 52.00/7.00  fof(f4,axiom,(
% 52.00/7.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 52.00/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 52.00/7.00  
% 52.00/7.00  fof(f20,plain,(
% 52.00/7.00    ! [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 52.00/7.00    inference(ennf_transformation,[],[f4])).
% 52.00/7.00  
% 52.00/7.00  fof(f62,plain,(
% 52.00/7.00    ( ! [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 52.00/7.00    inference(cnf_transformation,[],[f20])).
% 52.00/7.00  
% 52.00/7.00  fof(f60,plain,(
% 52.00/7.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 52.00/7.00    inference(cnf_transformation,[],[f44])).
% 52.00/7.00  
% 52.00/7.00  fof(f6,axiom,(
% 52.00/7.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 52.00/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 52.00/7.00  
% 52.00/7.00  fof(f22,plain,(
% 52.00/7.00    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 52.00/7.00    inference(ennf_transformation,[],[f6])).
% 52.00/7.00  
% 52.00/7.00  fof(f45,plain,(
% 52.00/7.00    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 52.00/7.00    inference(nnf_transformation,[],[f22])).
% 52.00/7.00  
% 52.00/7.00  fof(f64,plain,(
% 52.00/7.00    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 52.00/7.00    inference(cnf_transformation,[],[f45])).
% 52.00/7.00  
% 52.00/7.00  fof(f13,axiom,(
% 52.00/7.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1))))),
% 52.00/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 52.00/7.00  
% 52.00/7.00  fof(f34,plain,(
% 52.00/7.00    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 52.00/7.00    inference(ennf_transformation,[],[f13])).
% 52.00/7.00  
% 52.00/7.00  fof(f35,plain,(
% 52.00/7.00    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 52.00/7.00    inference(flattening,[],[f34])).
% 52.00/7.00  
% 52.00/7.00  fof(f50,plain,(
% 52.00/7.00    ! [X0] : (! [X1] : (((r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1)) & (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 52.00/7.00    inference(nnf_transformation,[],[f35])).
% 52.00/7.00  
% 52.00/7.00  fof(f84,plain,(
% 52.00/7.00    ( ! [X0,X1] : (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 52.00/7.00    inference(cnf_transformation,[],[f50])).
% 52.00/7.00  
% 52.00/7.00  fof(f87,plain,(
% 52.00/7.00    ( ! [X0,X1] : (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 52.00/7.00    inference(cnf_transformation,[],[f37])).
% 52.00/7.00  
% 52.00/7.00  fof(f65,plain,(
% 52.00/7.00    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 52.00/7.00    inference(cnf_transformation,[],[f45])).
% 52.00/7.00  
% 52.00/7.00  fof(f3,axiom,(
% 52.00/7.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 52.00/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 52.00/7.00  
% 52.00/7.00  fof(f19,plain,(
% 52.00/7.00    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 52.00/7.00    inference(ennf_transformation,[],[f3])).
% 52.00/7.00  
% 52.00/7.00  fof(f61,plain,(
% 52.00/7.00    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 52.00/7.00    inference(cnf_transformation,[],[f19])).
% 52.00/7.00  
% 52.00/7.00  fof(f71,plain,(
% 52.00/7.00    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | v3_pre_topc(sK0(X0,X1,X2),X1) | k2_struct_0(X1) = k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 52.00/7.00    inference(cnf_transformation,[],[f49])).
% 52.00/7.00  
% 52.00/7.00  fof(f70,plain,(
% 52.00/7.00    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | k2_struct_0(X0) != k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 52.00/7.00    inference(cnf_transformation,[],[f49])).
% 52.00/7.00  
% 52.00/7.00  fof(f85,plain,(
% 52.00/7.00    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 52.00/7.00    inference(cnf_transformation,[],[f50])).
% 52.00/7.00  
% 52.00/7.00  fof(f68,plain,(
% 52.00/7.00    ( ! [X4,X2,X0,X1] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v5_pre_topc(X2,X0,X1) | k2_struct_0(X0) != k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 52.00/7.00    inference(cnf_transformation,[],[f49])).
% 52.00/7.00  
% 52.00/7.00  fof(f74,plain,(
% 52.00/7.00    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) | k2_struct_0(X0) != k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 52.00/7.00    inference(cnf_transformation,[],[f49])).
% 52.00/7.00  
% 52.00/7.00  fof(f1,axiom,(
% 52.00/7.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 52.00/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 52.00/7.00  
% 52.00/7.00  fof(f42,plain,(
% 52.00/7.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 52.00/7.00    inference(nnf_transformation,[],[f1])).
% 52.00/7.00  
% 52.00/7.00  fof(f43,plain,(
% 52.00/7.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 52.00/7.00    inference(flattening,[],[f42])).
% 52.00/7.00  
% 52.00/7.00  fof(f57,plain,(
% 52.00/7.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 52.00/7.00    inference(cnf_transformation,[],[f43])).
% 52.00/7.00  
% 52.00/7.00  fof(f98,plain,(
% 52.00/7.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 52.00/7.00    inference(equality_resolution,[],[f57])).
% 52.00/7.00  
% 52.00/7.00  fof(f72,plain,(
% 52.00/7.00    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | v3_pre_topc(sK0(X0,X1,X2),X1) | k2_struct_0(X0) != k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 52.00/7.00    inference(cnf_transformation,[],[f49])).
% 52.00/7.00  
% 52.00/7.00  cnf(c_39,negated_conjecture,
% 52.00/7.00      ( l1_pre_topc(sK1) ),
% 52.00/7.00      inference(cnf_transformation,[],[f91]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_1648,plain,
% 52.00/7.00      ( l1_pre_topc(sK1) = iProver_top ),
% 52.00/7.00      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_10,plain,
% 52.00/7.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 52.00/7.00      inference(cnf_transformation,[],[f66]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_1677,plain,
% 52.00/7.00      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 52.00/7.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_2374,plain,
% 52.00/7.00      ( l1_struct_0(sK1) = iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_1648,c_1677]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_7,plain,
% 52.00/7.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 52.00/7.00      inference(cnf_transformation,[],[f63]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_1680,plain,
% 52.00/7.00      ( u1_struct_0(X0) = k2_struct_0(X0)
% 52.00/7.00      | l1_struct_0(X0) != iProver_top ),
% 52.00/7.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_2461,plain,
% 52.00/7.00      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_2374,c_1680]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_38,negated_conjecture,
% 52.00/7.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 52.00/7.00      inference(cnf_transformation,[],[f92]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_1649,plain,
% 52.00/7.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 52.00/7.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_2701,plain,
% 52.00/7.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
% 52.00/7.00      inference(demodulation,[status(thm)],[c_2461,c_1649]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_19,plain,
% 52.00/7.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 52.00/7.00      | v2_struct_0(X1)
% 52.00/7.00      | ~ v2_pre_topc(X1)
% 52.00/7.00      | ~ l1_pre_topc(X1)
% 52.00/7.00      | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
% 52.00/7.00      inference(cnf_transformation,[],[f75]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_1668,plain,
% 52.00/7.00      ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
% 52.00/7.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 52.00/7.00      | v2_struct_0(X0) = iProver_top
% 52.00/7.00      | v2_pre_topc(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(X0) != iProver_top ),
% 52.00/7.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_4991,plain,
% 52.00/7.00      ( k7_tmap_1(sK1,X0) = k6_partfun1(u1_struct_0(sK1))
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 52.00/7.00      | v2_struct_0(sK1) = iProver_top
% 52.00/7.00      | v2_pre_topc(sK1) != iProver_top
% 52.00/7.00      | l1_pre_topc(sK1) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_2461,c_1668]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_4997,plain,
% 52.00/7.00      ( k7_tmap_1(sK1,X0) = k6_partfun1(k2_struct_0(sK1))
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 52.00/7.00      | v2_struct_0(sK1) = iProver_top
% 52.00/7.00      | v2_pre_topc(sK1) != iProver_top
% 52.00/7.00      | l1_pre_topc(sK1) != iProver_top ),
% 52.00/7.00      inference(light_normalisation,[status(thm)],[c_4991,c_2461]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_41,negated_conjecture,
% 52.00/7.00      ( ~ v2_struct_0(sK1) ),
% 52.00/7.00      inference(cnf_transformation,[],[f89]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_42,plain,
% 52.00/7.00      ( v2_struct_0(sK1) != iProver_top ),
% 52.00/7.00      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_40,negated_conjecture,
% 52.00/7.00      ( v2_pre_topc(sK1) ),
% 52.00/7.00      inference(cnf_transformation,[],[f90]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_43,plain,
% 52.00/7.00      ( v2_pre_topc(sK1) = iProver_top ),
% 52.00/7.00      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_44,plain,
% 52.00/7.00      ( l1_pre_topc(sK1) = iProver_top ),
% 52.00/7.00      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_8319,plain,
% 52.00/7.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 52.00/7.00      | k7_tmap_1(sK1,X0) = k6_partfun1(k2_struct_0(sK1)) ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_4997,c_42,c_43,c_44]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_8320,plain,
% 52.00/7.00      ( k7_tmap_1(sK1,X0) = k6_partfun1(k2_struct_0(sK1))
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 52.00/7.00      inference(renaming,[status(thm)],[c_8319]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_8328,plain,
% 52.00/7.00      ( k7_tmap_1(sK1,sK2) = k6_partfun1(k2_struct_0(sK1)) ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_2701,c_8320]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_35,negated_conjecture,
% 52.00/7.00      ( v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
% 52.00/7.00      | v3_pre_topc(sK2,sK1) ),
% 52.00/7.00      inference(cnf_transformation,[],[f95]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_1652,plain,
% 52.00/7.00      ( v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | v3_pre_topc(sK2,sK1) = iProver_top ),
% 52.00/7.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_8346,plain,
% 52.00/7.00      ( v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | v3_pre_topc(sK2,sK1) = iProver_top ),
% 52.00/7.00      inference(demodulation,[status(thm)],[c_8328,c_1652]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_31,plain,
% 52.00/7.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 52.00/7.00      | v2_struct_0(X1)
% 52.00/7.00      | ~ v2_pre_topc(X1)
% 52.00/7.00      | ~ l1_pre_topc(X1)
% 52.00/7.00      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
% 52.00/7.00      inference(cnf_transformation,[],[f86]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_1656,plain,
% 52.00/7.00      ( u1_struct_0(k6_tmap_1(X0,X1)) = u1_struct_0(X0)
% 52.00/7.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 52.00/7.00      | v2_struct_0(X0) = iProver_top
% 52.00/7.00      | v2_pre_topc(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(X0) != iProver_top ),
% 52.00/7.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_3692,plain,
% 52.00/7.00      ( u1_struct_0(k6_tmap_1(sK1,X0)) = u1_struct_0(sK1)
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 52.00/7.00      | v2_struct_0(sK1) = iProver_top
% 52.00/7.00      | v2_pre_topc(sK1) != iProver_top
% 52.00/7.00      | l1_pre_topc(sK1) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_2461,c_1656]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_3698,plain,
% 52.00/7.00      ( u1_struct_0(k6_tmap_1(sK1,X0)) = k2_struct_0(sK1)
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 52.00/7.00      | v2_struct_0(sK1) = iProver_top
% 52.00/7.00      | v2_pre_topc(sK1) != iProver_top
% 52.00/7.00      | l1_pre_topc(sK1) != iProver_top ),
% 52.00/7.00      inference(light_normalisation,[status(thm)],[c_3692,c_2461]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_4548,plain,
% 52.00/7.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 52.00/7.00      | u1_struct_0(k6_tmap_1(sK1,X0)) = k2_struct_0(sK1) ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_3698,c_42,c_43,c_44]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_4549,plain,
% 52.00/7.00      ( u1_struct_0(k6_tmap_1(sK1,X0)) = k2_struct_0(sK1)
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 52.00/7.00      inference(renaming,[status(thm)],[c_4548]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_4557,plain,
% 52.00/7.00      ( u1_struct_0(k6_tmap_1(sK1,sK2)) = k2_struct_0(sK1) ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_2701,c_4549]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_34,negated_conjecture,
% 52.00/7.00      ( v3_pre_topc(sK2,sK1)
% 52.00/7.00      | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) ),
% 52.00/7.00      inference(cnf_transformation,[],[f96]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_1653,plain,
% 52.00/7.00      ( v3_pre_topc(sK2,sK1) = iProver_top
% 52.00/7.00      | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) = iProver_top ),
% 52.00/7.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_45,plain,
% 52.00/7.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 52.00/7.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_22,plain,
% 52.00/7.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 52.00/7.00      | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 52.00/7.00      | v2_struct_0(X1)
% 52.00/7.00      | ~ v2_pre_topc(X1)
% 52.00/7.00      | ~ l1_pre_topc(X1) ),
% 52.00/7.00      inference(cnf_transformation,[],[f80]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_2285,plain,
% 52.00/7.00      ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))))
% 52.00/7.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 52.00/7.00      | v2_struct_0(sK1)
% 52.00/7.00      | ~ v2_pre_topc(sK1)
% 52.00/7.00      | ~ l1_pre_topc(sK1) ),
% 52.00/7.00      inference(instantiation,[status(thm)],[c_22]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_2286,plain,
% 52.00/7.00      ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) = iProver_top
% 52.00/7.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 52.00/7.00      | v2_struct_0(sK1) = iProver_top
% 52.00/7.00      | v2_pre_topc(sK1) != iProver_top
% 52.00/7.00      | l1_pre_topc(sK1) != iProver_top ),
% 52.00/7.00      inference(predicate_to_equality,[status(thm)],[c_2285]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_2335,plain,
% 52.00/7.00      ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) = iProver_top ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_1653,c_42,c_43,c_44,c_45,c_2286]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_2699,plain,
% 52.00/7.00      ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) = iProver_top ),
% 52.00/7.00      inference(demodulation,[status(thm)],[c_2461,c_2335]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_5158,plain,
% 52.00/7.00      ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) = iProver_top ),
% 52.00/7.00      inference(demodulation,[status(thm)],[c_4557,c_2699]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_8343,plain,
% 52.00/7.00      ( m1_subset_1(k6_partfun1(k2_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) = iProver_top ),
% 52.00/7.00      inference(demodulation,[status(thm)],[c_8328,c_5158]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_18,plain,
% 52.00/7.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 52.00/7.00      | ~ v5_pre_topc(X0,X1,X2)
% 52.00/7.00      | ~ v3_pre_topc(X3,X2)
% 52.00/7.00      | v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
% 52.00/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 52.00/7.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 52.00/7.00      | ~ v1_funct_1(X0)
% 52.00/7.00      | ~ l1_pre_topc(X1)
% 52.00/7.00      | ~ l1_pre_topc(X2)
% 52.00/7.00      | k2_struct_0(X2) = k1_xboole_0 ),
% 52.00/7.00      inference(cnf_transformation,[],[f67]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_1669,plain,
% 52.00/7.00      ( k2_struct_0(X0) = k1_xboole_0
% 52.00/7.00      | v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X0)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X1,X2,X0) != iProver_top
% 52.00/7.00      | v3_pre_topc(X3,X0) != iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X0),X1,X3),X2) = iProver_top
% 52.00/7.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) != iProver_top
% 52.00/7.00      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 52.00/7.00      | v1_funct_1(X1) != iProver_top
% 52.00/7.00      | l1_pre_topc(X2) != iProver_top
% 52.00/7.00      | l1_pre_topc(X0) != iProver_top ),
% 52.00/7.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_7525,plain,
% 52.00/7.00      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 52.00/7.00      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,X1,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v3_pre_topc(X2,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK1),X0,X2),X1) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
% 52.00/7.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(X1) != iProver_top
% 52.00/7.00      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_4557,c_1669]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_7536,plain,
% 52.00/7.00      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 52.00/7.00      | v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,X1,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v3_pre_topc(X2,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK1),X0,X2),X1) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK1)))) != iProver_top
% 52.00/7.00      | m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(X1) != iProver_top
% 52.00/7.00      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 52.00/7.00      inference(light_normalisation,[status(thm)],[c_7525,c_4557]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_20,plain,
% 52.00/7.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 52.00/7.00      | v2_struct_0(X1)
% 52.00/7.00      | ~ v2_pre_topc(X1)
% 52.00/7.00      | ~ l1_pre_topc(X1)
% 52.00/7.00      | l1_pre_topc(k6_tmap_1(X1,X0)) ),
% 52.00/7.00      inference(cnf_transformation,[],[f77]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_1667,plain,
% 52.00/7.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 52.00/7.00      | v2_struct_0(X1) = iProver_top
% 52.00/7.00      | v2_pre_topc(X1) != iProver_top
% 52.00/7.00      | l1_pre_topc(X1) != iProver_top
% 52.00/7.00      | l1_pre_topc(k6_tmap_1(X1,X0)) = iProver_top ),
% 52.00/7.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_4957,plain,
% 52.00/7.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 52.00/7.00      | v2_struct_0(sK1) = iProver_top
% 52.00/7.00      | v2_pre_topc(sK1) != iProver_top
% 52.00/7.00      | l1_pre_topc(k6_tmap_1(sK1,X0)) = iProver_top
% 52.00/7.00      | l1_pre_topc(sK1) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_2461,c_1667]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_7205,plain,
% 52.00/7.00      ( l1_pre_topc(k6_tmap_1(sK1,X0)) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_4957,c_42,c_43,c_44]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_7206,plain,
% 52.00/7.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 52.00/7.00      | l1_pre_topc(k6_tmap_1(sK1,X0)) = iProver_top ),
% 52.00/7.00      inference(renaming,[status(thm)],[c_7205]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_7214,plain,
% 52.00/7.00      ( l1_pre_topc(k6_tmap_1(sK1,sK2)) = iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_2701,c_7206]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_7345,plain,
% 52.00/7.00      ( l1_struct_0(k6_tmap_1(sK1,sK2)) = iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_7214,c_1677]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_7349,plain,
% 52.00/7.00      ( u1_struct_0(k6_tmap_1(sK1,sK2)) = k2_struct_0(k6_tmap_1(sK1,sK2)) ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_7345,c_1680]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_7350,plain,
% 52.00/7.00      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k2_struct_0(sK1) ),
% 52.00/7.00      inference(light_normalisation,[status(thm)],[c_7349,c_4557]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_7537,plain,
% 52.00/7.00      ( k2_struct_0(sK1) = k1_xboole_0
% 52.00/7.00      | v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,X1,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v3_pre_topc(X2,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK1),X0,X2),X1) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK1)))) != iProver_top
% 52.00/7.00      | m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(X1) != iProver_top
% 52.00/7.00      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 52.00/7.00      inference(demodulation,[status(thm)],[c_7536,c_7350]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_2212,plain,
% 52.00/7.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 52.00/7.00      | v2_struct_0(sK1)
% 52.00/7.00      | ~ v2_pre_topc(sK1)
% 52.00/7.00      | l1_pre_topc(k6_tmap_1(sK1,sK2))
% 52.00/7.00      | ~ l1_pre_topc(sK1) ),
% 52.00/7.00      inference(instantiation,[status(thm)],[c_20]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_2213,plain,
% 52.00/7.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 52.00/7.00      | v2_struct_0(sK1) = iProver_top
% 52.00/7.00      | v2_pre_topc(sK1) != iProver_top
% 52.00/7.00      | l1_pre_topc(k6_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | l1_pre_topc(sK1) != iProver_top ),
% 52.00/7.00      inference(predicate_to_equality,[status(thm)],[c_2212]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_34853,plain,
% 52.00/7.00      ( l1_pre_topc(X1) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK1)))) != iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK1),X0,X2),X1) = iProver_top
% 52.00/7.00      | v3_pre_topc(X2,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,X1,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK1)) != iProver_top
% 52.00/7.00      | k2_struct_0(sK1) = k1_xboole_0 ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_7537,c_42,c_43,c_44,c_45,c_2213]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_34854,plain,
% 52.00/7.00      ( k2_struct_0(sK1) = k1_xboole_0
% 52.00/7.00      | v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,X1,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v3_pre_topc(X2,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK1),X0,X2),X1) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK1)))) != iProver_top
% 52.00/7.00      | m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(X1) != iProver_top ),
% 52.00/7.00      inference(renaming,[status(thm)],[c_34853]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_34869,plain,
% 52.00/7.00      ( k2_struct_0(sK1) = k1_xboole_0
% 52.00/7.00      | v1_funct_2(X0,u1_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v3_pre_topc(X1,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0,X1),sK1) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 52.00/7.00      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(sK1) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_2461,c_34854]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_34995,plain,
% 52.00/7.00      ( k2_struct_0(sK1) = k1_xboole_0
% 52.00/7.00      | v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v3_pre_topc(X1,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0,X1),sK1) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 52.00/7.00      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(sK1) != iProver_top ),
% 52.00/7.00      inference(light_normalisation,[status(thm)],[c_34869,c_2461]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_7522,plain,
% 52.00/7.00      ( k2_struct_0(X0) = k1_xboole_0
% 52.00/7.00      | v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X1,sK1,X0) != iProver_top
% 52.00/7.00      | v3_pre_topc(X2,X0) != iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0),X1,X2),sK1) = iProver_top
% 52.00/7.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) != iProver_top
% 52.00/7.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 52.00/7.00      | v1_funct_1(X1) != iProver_top
% 52.00/7.00      | l1_pre_topc(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(sK1) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_2461,c_1669]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_7600,plain,
% 52.00/7.00      ( k2_struct_0(X0) = k1_xboole_0
% 52.00/7.00      | v1_funct_2(X1,k2_struct_0(sK1),u1_struct_0(X0)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X1,sK1,X0) != iProver_top
% 52.00/7.00      | v3_pre_topc(X2,X0) != iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0),X1,X2),sK1) = iProver_top
% 52.00/7.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0)))) != iProver_top
% 52.00/7.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 52.00/7.00      | v1_funct_1(X1) != iProver_top
% 52.00/7.00      | l1_pre_topc(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(sK1) != iProver_top ),
% 52.00/7.00      inference(light_normalisation,[status(thm)],[c_7522,c_2461]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_20630,plain,
% 52.00/7.00      ( l1_pre_topc(X0) != iProver_top
% 52.00/7.00      | v1_funct_1(X1) != iProver_top
% 52.00/7.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 52.00/7.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0)))) != iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0),X1,X2),sK1) = iProver_top
% 52.00/7.00      | v3_pre_topc(X2,X0) != iProver_top
% 52.00/7.00      | v5_pre_topc(X1,sK1,X0) != iProver_top
% 52.00/7.00      | v1_funct_2(X1,k2_struct_0(sK1),u1_struct_0(X0)) != iProver_top
% 52.00/7.00      | k2_struct_0(X0) = k1_xboole_0 ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_7600,c_44]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_20631,plain,
% 52.00/7.00      ( k2_struct_0(X0) = k1_xboole_0
% 52.00/7.00      | v1_funct_2(X1,k2_struct_0(sK1),u1_struct_0(X0)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X1,sK1,X0) != iProver_top
% 52.00/7.00      | v3_pre_topc(X2,X0) != iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0),X1,X2),sK1) = iProver_top
% 52.00/7.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0)))) != iProver_top
% 52.00/7.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 52.00/7.00      | v1_funct_1(X1) != iProver_top
% 52.00/7.00      | l1_pre_topc(X0) != iProver_top ),
% 52.00/7.00      inference(renaming,[status(thm)],[c_20630]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_20645,plain,
% 52.00/7.00      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 52.00/7.00      | v1_funct_2(X0,k2_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v3_pre_topc(X1,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0,X1),sK1) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
% 52.00/7.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_4557,c_20631]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_20676,plain,
% 52.00/7.00      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 52.00/7.00      | v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v3_pre_topc(X1,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0,X1),sK1) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 52.00/7.00      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 52.00/7.00      inference(light_normalisation,[status(thm)],[c_20645,c_4557]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_20677,plain,
% 52.00/7.00      ( k2_struct_0(sK1) = k1_xboole_0
% 52.00/7.00      | v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v3_pre_topc(X1,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0,X1),sK1) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 52.00/7.00      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 52.00/7.00      inference(demodulation,[status(thm)],[c_20676,c_7350]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_35437,plain,
% 52.00/7.00      ( v1_funct_1(X0) != iProver_top
% 52.00/7.00      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0,X1),sK1) = iProver_top
% 52.00/7.00      | v3_pre_topc(X1,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 52.00/7.00      | k2_struct_0(sK1) = k1_xboole_0 ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_34995,c_42,c_43,c_44,c_45,c_2213,c_20677]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_35438,plain,
% 52.00/7.00      ( k2_struct_0(sK1) = k1_xboole_0
% 52.00/7.00      | v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v3_pre_topc(X1,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0,X1),sK1) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 52.00/7.00      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top ),
% 52.00/7.00      inference(renaming,[status(thm)],[c_35437]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_12,plain,
% 52.00/7.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 52.00/7.00      | v5_pre_topc(X0,X1,X2)
% 52.00/7.00      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0)),X1)
% 52.00/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 52.00/7.00      | ~ v1_funct_1(X0)
% 52.00/7.00      | ~ l1_pre_topc(X1)
% 52.00/7.00      | ~ l1_pre_topc(X2)
% 52.00/7.00      | k2_struct_0(X2) = k1_xboole_0 ),
% 52.00/7.00      inference(cnf_transformation,[],[f73]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_1675,plain,
% 52.00/7.00      ( k2_struct_0(X0) = k1_xboole_0
% 52.00/7.00      | v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X0)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X1,X2,X0) = iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X0),X1,sK0(X2,X0,X1)),X2) != iProver_top
% 52.00/7.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) != iProver_top
% 52.00/7.00      | v1_funct_1(X1) != iProver_top
% 52.00/7.00      | l1_pre_topc(X2) != iProver_top
% 52.00/7.00      | l1_pre_topc(X0) != iProver_top ),
% 52.00/7.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_8045,plain,
% 52.00/7.00      ( k2_struct_0(sK1) = k1_xboole_0
% 52.00/7.00      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,X1,sK1) = iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK1),X0,sK0(X1,sK1,X0)),X1) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(X1) != iProver_top
% 52.00/7.00      | l1_pre_topc(sK1) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_2461,c_1675]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_8073,plain,
% 52.00/7.00      ( k2_struct_0(sK1) = k1_xboole_0
% 52.00/7.00      | v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,X1,sK1) = iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK1),X0,sK0(X1,sK1,X0)),X1) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK1)))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(X1) != iProver_top
% 52.00/7.00      | l1_pre_topc(sK1) != iProver_top ),
% 52.00/7.00      inference(light_normalisation,[status(thm)],[c_8045,c_2461]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_17443,plain,
% 52.00/7.00      ( l1_pre_topc(X1) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK1)))) != iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK1),X0,sK0(X1,sK1,X0)),X1) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,X1,sK1) = iProver_top
% 52.00/7.00      | v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK1)) != iProver_top
% 52.00/7.00      | k2_struct_0(sK1) = k1_xboole_0 ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_8073,c_44]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_17444,plain,
% 52.00/7.00      ( k2_struct_0(sK1) = k1_xboole_0
% 52.00/7.00      | v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,X1,sK1) = iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK1),X0,sK0(X1,sK1,X0)),X1) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK1)))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(X1) != iProver_top ),
% 52.00/7.00      inference(renaming,[status(thm)],[c_17443]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_17455,plain,
% 52.00/7.00      ( k2_struct_0(sK1) = k1_xboole_0
% 52.00/7.00      | v1_funct_2(X0,u1_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,sK1) = iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0,sK0(sK1,sK1,X0)),sK1) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(sK1) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_2461,c_17444]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_17495,plain,
% 52.00/7.00      ( k2_struct_0(sK1) = k1_xboole_0
% 52.00/7.00      | v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,sK1) = iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0,sK0(sK1,sK1,X0)),sK1) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(sK1) != iProver_top ),
% 52.00/7.00      inference(light_normalisation,[status(thm)],[c_17455,c_2461]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_18067,plain,
% 52.00/7.00      ( v1_funct_1(X0) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0,sK0(sK1,sK1,X0)),sK1) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,sK1) = iProver_top
% 52.00/7.00      | v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 52.00/7.00      | k2_struct_0(sK1) = k1_xboole_0 ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_17495,c_44]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_18068,plain,
% 52.00/7.00      ( k2_struct_0(sK1) = k1_xboole_0
% 52.00/7.00      | v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,sK1) = iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0,sK0(sK1,sK1,X0)),sK1) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top ),
% 52.00/7.00      inference(renaming,[status(thm)],[c_18067]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_35455,plain,
% 52.00/7.00      ( k2_struct_0(sK1) = k1_xboole_0
% 52.00/7.00      | v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,sK1) = iProver_top
% 52.00/7.00      | v3_pre_topc(sK0(sK1,sK1,X0),k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 52.00/7.00      | m1_subset_1(sK0(sK1,sK1,X0),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_35438,c_18068]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_16,plain,
% 52.00/7.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 52.00/7.00      | v5_pre_topc(X0,X1,X2)
% 52.00/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 52.00/7.00      | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
% 52.00/7.00      | ~ v1_funct_1(X0)
% 52.00/7.00      | ~ l1_pre_topc(X1)
% 52.00/7.00      | ~ l1_pre_topc(X2)
% 52.00/7.00      | k2_struct_0(X2) = k1_xboole_0 ),
% 52.00/7.00      inference(cnf_transformation,[],[f69]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_1671,plain,
% 52.00/7.00      ( k2_struct_0(X0) = k1_xboole_0
% 52.00/7.00      | v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X0)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X1,X2,X0) = iProver_top
% 52.00/7.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) != iProver_top
% 52.00/7.00      | m1_subset_1(sK0(X2,X0,X1),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 52.00/7.00      | v1_funct_1(X1) != iProver_top
% 52.00/7.00      | l1_pre_topc(X2) != iProver_top
% 52.00/7.00      | l1_pre_topc(X0) != iProver_top ),
% 52.00/7.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_7795,plain,
% 52.00/7.00      ( k2_struct_0(sK1) = k1_xboole_0
% 52.00/7.00      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,X1,sK1) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK1)))) != iProver_top
% 52.00/7.00      | m1_subset_1(sK0(X1,sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(X1) != iProver_top
% 52.00/7.00      | l1_pre_topc(sK1) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_2461,c_1671]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_7823,plain,
% 52.00/7.00      ( k2_struct_0(sK1) = k1_xboole_0
% 52.00/7.00      | v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,X1,sK1) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK1)))) != iProver_top
% 52.00/7.00      | m1_subset_1(sK0(X1,sK1,X0),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(X1) != iProver_top
% 52.00/7.00      | l1_pre_topc(sK1) != iProver_top ),
% 52.00/7.00      inference(light_normalisation,[status(thm)],[c_7795,c_2461]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_16432,plain,
% 52.00/7.00      ( l1_pre_topc(X1) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | m1_subset_1(sK0(X1,sK1,X0),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK1)))) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,X1,sK1) = iProver_top
% 52.00/7.00      | v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK1)) != iProver_top
% 52.00/7.00      | k2_struct_0(sK1) = k1_xboole_0 ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_7823,c_44]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_16433,plain,
% 52.00/7.00      ( k2_struct_0(sK1) = k1_xboole_0
% 52.00/7.00      | v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,X1,sK1) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK1)))) != iProver_top
% 52.00/7.00      | m1_subset_1(sK0(X1,sK1,X0),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(X1) != iProver_top ),
% 52.00/7.00      inference(renaming,[status(thm)],[c_16432]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_16444,plain,
% 52.00/7.00      ( k2_struct_0(sK1) = k1_xboole_0
% 52.00/7.00      | v1_funct_2(X0,u1_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,sK1) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 52.00/7.00      | m1_subset_1(sK0(sK1,sK1,X0),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(sK1) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_2461,c_16433]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_16484,plain,
% 52.00/7.00      ( k2_struct_0(sK1) = k1_xboole_0
% 52.00/7.00      | v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,sK1) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 52.00/7.00      | m1_subset_1(sK0(sK1,sK1,X0),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(sK1) != iProver_top ),
% 52.00/7.00      inference(light_normalisation,[status(thm)],[c_16444,c_2461]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_16643,plain,
% 52.00/7.00      ( v1_funct_1(X0) != iProver_top
% 52.00/7.00      | m1_subset_1(sK0(sK1,sK1,X0),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,sK1) = iProver_top
% 52.00/7.00      | v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 52.00/7.00      | k2_struct_0(sK1) = k1_xboole_0 ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_16484,c_44]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_16644,plain,
% 52.00/7.00      ( k2_struct_0(sK1) = k1_xboole_0
% 52.00/7.00      | v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,sK1) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 52.00/7.00      | m1_subset_1(sK0(sK1,sK1,X0),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top ),
% 52.00/7.00      inference(renaming,[status(thm)],[c_16643]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_114115,plain,
% 52.00/7.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 52.00/7.00      | v3_pre_topc(sK0(sK1,sK1,X0),k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,sK1) = iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 52.00/7.00      | k2_struct_0(sK1) = k1_xboole_0
% 52.00/7.00      | v1_funct_1(X0) != iProver_top ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_35455,c_16644]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_114116,plain,
% 52.00/7.00      ( k2_struct_0(sK1) = k1_xboole_0
% 52.00/7.00      | v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,sK1) = iProver_top
% 52.00/7.00      | v3_pre_topc(sK0(sK1,sK1,X0),k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top ),
% 52.00/7.00      inference(renaming,[status(thm)],[c_114115]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_114129,plain,
% 52.00/7.00      ( k2_struct_0(sK1) = k1_xboole_0
% 52.00/7.00      | v1_funct_2(k6_partfun1(k2_struct_0(sK1)),k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,sK1) = iProver_top
% 52.00/7.00      | v3_pre_topc(sK0(sK1,sK1,k6_partfun1(k2_struct_0(sK1))),k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v1_funct_1(k6_partfun1(k2_struct_0(sK1))) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_8343,c_114116]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_32,plain,
% 52.00/7.00      ( v3_pre_topc(X0,k6_tmap_1(X1,X0))
% 52.00/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 52.00/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X0))))
% 52.00/7.00      | v2_struct_0(X1)
% 52.00/7.00      | ~ v2_pre_topc(X1)
% 52.00/7.00      | ~ l1_pre_topc(X1) ),
% 52.00/7.00      inference(cnf_transformation,[],[f100]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_1655,plain,
% 52.00/7.00      ( v3_pre_topc(X0,k6_tmap_1(X1,X0)) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X0)))) != iProver_top
% 52.00/7.00      | v2_struct_0(X1) = iProver_top
% 52.00/7.00      | v2_pre_topc(X1) != iProver_top
% 52.00/7.00      | l1_pre_topc(X1) != iProver_top ),
% 52.00/7.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_5189,plain,
% 52.00/7.00      ( v3_pre_topc(sK2,k6_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 52.00/7.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 52.00/7.00      | v2_struct_0(sK1) = iProver_top
% 52.00/7.00      | v2_pre_topc(sK1) != iProver_top
% 52.00/7.00      | l1_pre_topc(sK1) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_4557,c_1655]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_5196,plain,
% 52.00/7.00      ( v3_pre_topc(sK2,k6_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 52.00/7.00      | v2_struct_0(sK1) = iProver_top
% 52.00/7.00      | v2_pre_topc(sK1) != iProver_top
% 52.00/7.00      | l1_pre_topc(sK1) != iProver_top ),
% 52.00/7.00      inference(light_normalisation,[status(thm)],[c_5189,c_2461]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_36,negated_conjecture,
% 52.00/7.00      ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
% 52.00/7.00      | v3_pre_topc(sK2,sK1) ),
% 52.00/7.00      inference(cnf_transformation,[],[f94]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_1651,plain,
% 52.00/7.00      ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) = iProver_top
% 52.00/7.00      | v3_pre_topc(sK2,sK1) = iProver_top ),
% 52.00/7.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_23,plain,
% 52.00/7.00      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 52.00/7.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 52.00/7.00      | v2_struct_0(X0)
% 52.00/7.00      | ~ v2_pre_topc(X0)
% 52.00/7.00      | ~ l1_pre_topc(X0) ),
% 52.00/7.00      inference(cnf_transformation,[],[f79]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_2289,plain,
% 52.00/7.00      ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
% 52.00/7.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 52.00/7.00      | v2_struct_0(sK1)
% 52.00/7.00      | ~ v2_pre_topc(sK1)
% 52.00/7.00      | ~ l1_pre_topc(sK1) ),
% 52.00/7.00      inference(instantiation,[status(thm)],[c_23]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_2290,plain,
% 52.00/7.00      ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) = iProver_top
% 52.00/7.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 52.00/7.00      | v2_struct_0(sK1) = iProver_top
% 52.00/7.00      | v2_pre_topc(sK1) != iProver_top
% 52.00/7.00      | l1_pre_topc(sK1) != iProver_top ),
% 52.00/7.00      inference(predicate_to_equality,[status(thm)],[c_2289]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_2296,plain,
% 52.00/7.00      ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) = iProver_top ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_1651,c_42,c_43,c_44,c_45,c_2290]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_2700,plain,
% 52.00/7.00      ( v1_funct_2(k7_tmap_1(sK1,sK2),k2_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) = iProver_top ),
% 52.00/7.00      inference(demodulation,[status(thm)],[c_2461,c_2296]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_5159,plain,
% 52.00/7.00      ( v1_funct_2(k7_tmap_1(sK1,sK2),k2_struct_0(sK1),k2_struct_0(sK1)) = iProver_top ),
% 52.00/7.00      inference(demodulation,[status(thm)],[c_4557,c_2700]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_8344,plain,
% 52.00/7.00      ( v1_funct_2(k6_partfun1(k2_struct_0(sK1)),k2_struct_0(sK1),k2_struct_0(sK1)) = iProver_top ),
% 52.00/7.00      inference(demodulation,[status(thm)],[c_8328,c_5159]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_33,negated_conjecture,
% 52.00/7.00      ( ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
% 52.00/7.00      | ~ v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
% 52.00/7.00      | ~ v3_pre_topc(sK2,sK1)
% 52.00/7.00      | ~ m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))))
% 52.00/7.00      | ~ v1_funct_1(k7_tmap_1(sK1,sK2)) ),
% 52.00/7.00      inference(cnf_transformation,[],[f97]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_1654,plain,
% 52.00/7.00      ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
% 52.00/7.00      | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v3_pre_topc(sK2,sK1) != iProver_top
% 52.00/7.00      | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
% 52.00/7.00      | v1_funct_1(k7_tmap_1(sK1,sK2)) != iProver_top ),
% 52.00/7.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_50,plain,
% 52.00/7.00      ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
% 52.00/7.00      | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v3_pre_topc(sK2,sK1) != iProver_top
% 52.00/7.00      | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
% 52.00/7.00      | v1_funct_1(k7_tmap_1(sK1,sK2)) != iProver_top ),
% 52.00/7.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_24,plain,
% 52.00/7.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 52.00/7.00      | v2_struct_0(X1)
% 52.00/7.00      | ~ v2_pre_topc(X1)
% 52.00/7.00      | v1_funct_1(k7_tmap_1(X1,X0))
% 52.00/7.00      | ~ l1_pre_topc(X1) ),
% 52.00/7.00      inference(cnf_transformation,[],[f78]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_2220,plain,
% 52.00/7.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 52.00/7.00      | v2_struct_0(sK1)
% 52.00/7.00      | ~ v2_pre_topc(sK1)
% 52.00/7.00      | v1_funct_1(k7_tmap_1(sK1,sK2))
% 52.00/7.00      | ~ l1_pre_topc(sK1) ),
% 52.00/7.00      inference(instantiation,[status(thm)],[c_24]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_2221,plain,
% 52.00/7.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 52.00/7.00      | v2_struct_0(sK1) = iProver_top
% 52.00/7.00      | v2_pre_topc(sK1) != iProver_top
% 52.00/7.00      | v1_funct_1(k7_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | l1_pre_topc(sK1) != iProver_top ),
% 52.00/7.00      inference(predicate_to_equality,[status(thm)],[c_2220]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_2228,plain,
% 52.00/7.00      ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
% 52.00/7.00      | v3_pre_topc(sK2,sK1) != iProver_top
% 52.00/7.00      | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_1654,c_42,c_43,c_44,c_45,c_50,c_2221]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_2229,plain,
% 52.00/7.00      ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
% 52.00/7.00      | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v3_pre_topc(sK2,sK1) != iProver_top
% 52.00/7.00      | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top ),
% 52.00/7.00      inference(renaming,[status(thm)],[c_2228]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_2340,plain,
% 52.00/7.00      ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
% 52.00/7.00      | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v3_pre_topc(sK2,sK1) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_2335,c_2229]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_2688,plain,
% 52.00/7.00      ( v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v3_pre_topc(sK2,sK1) != iProver_top ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_2340,c_42,c_43,c_44,c_45,c_50,c_2221,c_2286,c_2290]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_8345,plain,
% 52.00/7.00      ( v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v3_pre_topc(sK2,sK1) != iProver_top ),
% 52.00/7.00      inference(demodulation,[status(thm)],[c_8328,c_2688]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_37,negated_conjecture,
% 52.00/7.00      ( v3_pre_topc(sK2,sK1) | v1_funct_1(k7_tmap_1(sK1,sK2)) ),
% 52.00/7.00      inference(cnf_transformation,[],[f93]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_1650,plain,
% 52.00/7.00      ( v3_pre_topc(sK2,sK1) = iProver_top
% 52.00/7.00      | v1_funct_1(k7_tmap_1(sK1,sK2)) = iProver_top ),
% 52.00/7.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_2237,plain,
% 52.00/7.00      ( v1_funct_1(k7_tmap_1(sK1,sK2)) = iProver_top ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_1650,c_42,c_43,c_44,c_45,c_2221]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_8347,plain,
% 52.00/7.00      ( v1_funct_1(k6_partfun1(k2_struct_0(sK1))) = iProver_top ),
% 52.00/7.00      inference(demodulation,[status(thm)],[c_8328,c_2237]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_4,plain,
% 52.00/7.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 52.00/7.00      inference(cnf_transformation,[],[f59]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_1682,plain,
% 52.00/7.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 52.00/7.00      | r1_tarski(X0,X1) = iProver_top ),
% 52.00/7.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_2452,plain,
% 52.00/7.00      ( r1_tarski(sK2,u1_struct_0(sK1)) = iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_1649,c_1682]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_2698,plain,
% 52.00/7.00      ( r1_tarski(sK2,k2_struct_0(sK1)) = iProver_top ),
% 52.00/7.00      inference(demodulation,[status(thm)],[c_2461,c_2452]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_6,plain,
% 52.00/7.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 52.00/7.00      | k8_relset_1(X1,X1,k6_partfun1(X1),X0) = X0 ),
% 52.00/7.00      inference(cnf_transformation,[],[f62]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_3,plain,
% 52.00/7.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 52.00/7.00      inference(cnf_transformation,[],[f60]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_285,plain,
% 52.00/7.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 52.00/7.00      inference(prop_impl,[status(thm)],[c_3]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_286,plain,
% 52.00/7.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 52.00/7.00      inference(renaming,[status(thm)],[c_285]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_357,plain,
% 52.00/7.00      ( ~ r1_tarski(X0,X1) | k8_relset_1(X1,X1,k6_partfun1(X1),X0) = X0 ),
% 52.00/7.00      inference(bin_hyper_res,[status(thm)],[c_6,c_286]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_1645,plain,
% 52.00/7.00      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1
% 52.00/7.00      | r1_tarski(X1,X0) != iProver_top ),
% 52.00/7.00      inference(predicate_to_equality,[status(thm)],[c_357]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_3547,plain,
% 52.00/7.00      ( k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),k6_partfun1(k2_struct_0(sK1)),sK2) = sK2 ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_2698,c_1645]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_35453,plain,
% 52.00/7.00      ( k2_struct_0(sK1) = k1_xboole_0
% 52.00/7.00      | v1_funct_2(k6_partfun1(k2_struct_0(sK1)),k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v3_pre_topc(sK2,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v3_pre_topc(sK2,sK1) = iProver_top
% 52.00/7.00      | m1_subset_1(k6_partfun1(k2_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 52.00/7.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 52.00/7.00      | v1_funct_1(k6_partfun1(k2_struct_0(sK1))) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_3547,c_35438]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_114369,plain,
% 52.00/7.00      ( v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | k2_struct_0(sK1) = k1_xboole_0 ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_114129,c_42,c_43,c_44,c_2701,c_5196,c_8343,c_8344,
% 52.00/7.00                 c_8345,c_8347,c_35453]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_114370,plain,
% 52.00/7.00      ( k2_struct_0(sK1) = k1_xboole_0
% 52.00/7.00      | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) != iProver_top ),
% 52.00/7.00      inference(renaming,[status(thm)],[c_114369]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_114375,plain,
% 52.00/7.00      ( k2_struct_0(sK1) = k1_xboole_0
% 52.00/7.00      | v3_pre_topc(sK2,sK1) = iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_8346,c_114370]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_9,plain,
% 52.00/7.00      ( r2_hidden(X0,u1_pre_topc(X1))
% 52.00/7.00      | ~ v3_pre_topc(X0,X1)
% 52.00/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 52.00/7.00      | ~ l1_pre_topc(X1) ),
% 52.00/7.00      inference(cnf_transformation,[],[f64]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_1678,plain,
% 52.00/7.00      ( r2_hidden(X0,u1_pre_topc(X1)) = iProver_top
% 52.00/7.00      | v3_pre_topc(X0,X1) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 52.00/7.00      | l1_pre_topc(X1) != iProver_top ),
% 52.00/7.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_3842,plain,
% 52.00/7.00      ( r2_hidden(X0,u1_pre_topc(sK1)) = iProver_top
% 52.00/7.00      | v3_pre_topc(X0,sK1) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 52.00/7.00      | l1_pre_topc(sK1) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_2461,c_1678]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_4159,plain,
% 52.00/7.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 52.00/7.00      | v3_pre_topc(X0,sK1) != iProver_top
% 52.00/7.00      | r2_hidden(X0,u1_pre_topc(sK1)) = iProver_top ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_3842,c_44]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_4160,plain,
% 52.00/7.00      ( r2_hidden(X0,u1_pre_topc(sK1)) = iProver_top
% 52.00/7.00      | v3_pre_topc(X0,sK1) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 52.00/7.00      inference(renaming,[status(thm)],[c_4159]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_4169,plain,
% 52.00/7.00      ( r2_hidden(sK2,u1_pre_topc(sK1)) = iProver_top
% 52.00/7.00      | v3_pre_topc(sK2,sK1) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_2701,c_4160]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_29,plain,
% 52.00/7.00      ( ~ r2_hidden(X0,u1_pre_topc(X1))
% 52.00/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 52.00/7.00      | v2_struct_0(X1)
% 52.00/7.00      | ~ v2_pre_topc(X1)
% 52.00/7.00      | ~ l1_pre_topc(X1)
% 52.00/7.00      | k5_tmap_1(X1,X0) = u1_pre_topc(X1) ),
% 52.00/7.00      inference(cnf_transformation,[],[f84]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_1658,plain,
% 52.00/7.00      ( k5_tmap_1(X0,X1) = u1_pre_topc(X0)
% 52.00/7.00      | r2_hidden(X1,u1_pre_topc(X0)) != iProver_top
% 52.00/7.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 52.00/7.00      | v2_struct_0(X0) = iProver_top
% 52.00/7.00      | v2_pre_topc(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(X0) != iProver_top ),
% 52.00/7.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_5920,plain,
% 52.00/7.00      ( k5_tmap_1(sK1,X0) = u1_pre_topc(sK1)
% 52.00/7.00      | r2_hidden(X0,u1_pre_topc(sK1)) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 52.00/7.00      | v2_struct_0(sK1) = iProver_top
% 52.00/7.00      | v2_pre_topc(sK1) != iProver_top
% 52.00/7.00      | l1_pre_topc(sK1) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_2461,c_1658]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_11382,plain,
% 52.00/7.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 52.00/7.00      | r2_hidden(X0,u1_pre_topc(sK1)) != iProver_top
% 52.00/7.00      | k5_tmap_1(sK1,X0) = u1_pre_topc(sK1) ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_5920,c_42,c_43,c_44]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_11383,plain,
% 52.00/7.00      ( k5_tmap_1(sK1,X0) = u1_pre_topc(sK1)
% 52.00/7.00      | r2_hidden(X0,u1_pre_topc(sK1)) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 52.00/7.00      inference(renaming,[status(thm)],[c_11382]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_11392,plain,
% 52.00/7.00      ( k5_tmap_1(sK1,sK2) = u1_pre_topc(sK1)
% 52.00/7.00      | r2_hidden(sK2,u1_pre_topc(sK1)) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_2701,c_11383]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_12936,plain,
% 52.00/7.00      ( k5_tmap_1(sK1,sK2) = u1_pre_topc(sK1)
% 52.00/7.00      | v3_pre_topc(sK2,sK1) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_4169,c_11392]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_114380,plain,
% 52.00/7.00      ( k5_tmap_1(sK1,sK2) = u1_pre_topc(sK1)
% 52.00/7.00      | k2_struct_0(sK1) = k1_xboole_0 ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_114375,c_12936]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_10077,plain,
% 52.00/7.00      ( v3_pre_topc(sK2,k6_tmap_1(sK1,sK2)) = iProver_top ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_5196,c_42,c_43,c_44,c_2701]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_1683,plain,
% 52.00/7.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 52.00/7.00      | r1_tarski(X0,X1) != iProver_top ),
% 52.00/7.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_3841,plain,
% 52.00/7.00      ( r2_hidden(X0,u1_pre_topc(X1)) = iProver_top
% 52.00/7.00      | v3_pre_topc(X0,X1) != iProver_top
% 52.00/7.00      | r1_tarski(X0,u1_struct_0(X1)) != iProver_top
% 52.00/7.00      | l1_pre_topc(X1) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_1683,c_1678]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_13617,plain,
% 52.00/7.00      ( r2_hidden(X0,u1_pre_topc(k6_tmap_1(sK1,sK2))) = iProver_top
% 52.00/7.00      | v3_pre_topc(X0,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | r1_tarski(X0,k2_struct_0(sK1)) != iProver_top
% 52.00/7.00      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_4557,c_3841]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_30,plain,
% 52.00/7.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 52.00/7.00      | v2_struct_0(X1)
% 52.00/7.00      | ~ v2_pre_topc(X1)
% 52.00/7.00      | ~ l1_pre_topc(X1)
% 52.00/7.00      | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0) ),
% 52.00/7.00      inference(cnf_transformation,[],[f87]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_1657,plain,
% 52.00/7.00      ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
% 52.00/7.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 52.00/7.00      | v2_struct_0(X0) = iProver_top
% 52.00/7.00      | v2_pre_topc(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(X0) != iProver_top ),
% 52.00/7.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_4574,plain,
% 52.00/7.00      ( u1_pre_topc(k6_tmap_1(sK1,X0)) = k5_tmap_1(sK1,X0)
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 52.00/7.00      | v2_struct_0(sK1) = iProver_top
% 52.00/7.00      | v2_pre_topc(sK1) != iProver_top
% 52.00/7.00      | l1_pre_topc(sK1) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_2461,c_1657]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_10083,plain,
% 52.00/7.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 52.00/7.00      | u1_pre_topc(k6_tmap_1(sK1,X0)) = k5_tmap_1(sK1,X0) ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_4574,c_42,c_43,c_44]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_10084,plain,
% 52.00/7.00      ( u1_pre_topc(k6_tmap_1(sK1,X0)) = k5_tmap_1(sK1,X0)
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 52.00/7.00      inference(renaming,[status(thm)],[c_10083]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_10092,plain,
% 52.00/7.00      ( u1_pre_topc(k6_tmap_1(sK1,sK2)) = k5_tmap_1(sK1,sK2) ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_2701,c_10084]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_13631,plain,
% 52.00/7.00      ( r2_hidden(X0,k5_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | v3_pre_topc(X0,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | r1_tarski(X0,k2_struct_0(sK1)) != iProver_top
% 52.00/7.00      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 52.00/7.00      inference(light_normalisation,[status(thm)],[c_13617,c_10092]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_13917,plain,
% 52.00/7.00      ( r1_tarski(X0,k2_struct_0(sK1)) != iProver_top
% 52.00/7.00      | v3_pre_topc(X0,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | r2_hidden(X0,k5_tmap_1(sK1,sK2)) = iProver_top ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_13631,c_42,c_43,c_44,c_45,c_2213]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_13918,plain,
% 52.00/7.00      ( r2_hidden(X0,k5_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | v3_pre_topc(X0,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | r1_tarski(X0,k2_struct_0(sK1)) != iProver_top ),
% 52.00/7.00      inference(renaming,[status(thm)],[c_13917]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_13927,plain,
% 52.00/7.00      ( r2_hidden(sK2,k5_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | r1_tarski(sK2,k2_struct_0(sK1)) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_10077,c_13918]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_5188,plain,
% 52.00/7.00      ( r2_hidden(X0,u1_pre_topc(k6_tmap_1(sK1,sK2))) = iProver_top
% 52.00/7.00      | v3_pre_topc(X0,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 52.00/7.00      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_4557,c_1678]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_6679,plain,
% 52.00/7.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 52.00/7.00      | v3_pre_topc(X0,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | r2_hidden(X0,u1_pre_topc(k6_tmap_1(sK1,sK2))) = iProver_top ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_5188,c_42,c_43,c_44,c_45,c_2213]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_6680,plain,
% 52.00/7.00      ( r2_hidden(X0,u1_pre_topc(k6_tmap_1(sK1,sK2))) = iProver_top
% 52.00/7.00      | v3_pre_topc(X0,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 52.00/7.00      inference(renaming,[status(thm)],[c_6679]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_10269,plain,
% 52.00/7.00      ( r2_hidden(X0,k5_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | v3_pre_topc(X0,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 52.00/7.00      inference(demodulation,[status(thm)],[c_10092,c_6680]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_10798,plain,
% 52.00/7.00      ( r2_hidden(sK2,k5_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_10077,c_10269]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_22570,plain,
% 52.00/7.00      ( r2_hidden(sK2,k5_tmap_1(sK1,sK2)) = iProver_top ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_13927,c_2701,c_10798]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_114707,plain,
% 52.00/7.00      ( k2_struct_0(sK1) = k1_xboole_0
% 52.00/7.00      | r2_hidden(sK2,u1_pre_topc(sK1)) = iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_114380,c_22570]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_1665,plain,
% 52.00/7.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 52.00/7.00      | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0))))) = iProver_top
% 52.00/7.00      | v2_struct_0(X1) = iProver_top
% 52.00/7.00      | v2_pre_topc(X1) != iProver_top
% 52.00/7.00      | l1_pre_topc(X1) != iProver_top ),
% 52.00/7.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_7792,plain,
% 52.00/7.00      ( k2_struct_0(k6_tmap_1(X0,X1)) = k1_xboole_0
% 52.00/7.00      | v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) != iProver_top
% 52.00/7.00      | v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) = iProver_top
% 52.00/7.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 52.00/7.00      | m1_subset_1(sK0(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1)),k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) = iProver_top
% 52.00/7.00      | v2_struct_0(X0) = iProver_top
% 52.00/7.00      | v2_pre_topc(X0) != iProver_top
% 52.00/7.00      | v1_funct_1(k7_tmap_1(X0,X1)) != iProver_top
% 52.00/7.00      | l1_pre_topc(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(k6_tmap_1(X0,X1)) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_1665,c_1671]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_78,plain,
% 52.00/7.00      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) = iProver_top
% 52.00/7.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 52.00/7.00      | v2_struct_0(X0) = iProver_top
% 52.00/7.00      | v2_pre_topc(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(X0) != iProver_top ),
% 52.00/7.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_41028,plain,
% 52.00/7.00      ( k2_struct_0(k6_tmap_1(X0,X1)) = k1_xboole_0
% 52.00/7.00      | v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) = iProver_top
% 52.00/7.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 52.00/7.00      | m1_subset_1(sK0(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1)),k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) = iProver_top
% 52.00/7.00      | v2_struct_0(X0) = iProver_top
% 52.00/7.00      | v2_pre_topc(X0) != iProver_top
% 52.00/7.00      | v1_funct_1(k7_tmap_1(X0,X1)) != iProver_top
% 52.00/7.00      | l1_pre_topc(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(k6_tmap_1(X0,X1)) != iProver_top ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_7792,c_78]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_1663,plain,
% 52.00/7.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 52.00/7.00      | v2_struct_0(X1) = iProver_top
% 52.00/7.00      | v2_pre_topc(X1) != iProver_top
% 52.00/7.00      | v1_funct_1(k7_tmap_1(X1,X0)) = iProver_top
% 52.00/7.00      | l1_pre_topc(X1) != iProver_top ),
% 52.00/7.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_41043,plain,
% 52.00/7.00      ( k2_struct_0(k6_tmap_1(X0,X1)) = k1_xboole_0
% 52.00/7.00      | v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) = iProver_top
% 52.00/7.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 52.00/7.00      | m1_subset_1(sK0(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1)),k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) = iProver_top
% 52.00/7.00      | v2_struct_0(X0) = iProver_top
% 52.00/7.00      | v2_pre_topc(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(X0) != iProver_top ),
% 52.00/7.00      inference(forward_subsumption_resolution,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_41028,c_1667,c_1663]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_41049,plain,
% 52.00/7.00      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 52.00/7.00      | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | m1_subset_1(sK0(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2)),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
% 52.00/7.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 52.00/7.00      | v2_struct_0(sK1) = iProver_top
% 52.00/7.00      | v2_pre_topc(sK1) != iProver_top
% 52.00/7.00      | l1_pre_topc(sK1) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_4557,c_41043]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_41287,plain,
% 52.00/7.00      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 52.00/7.00      | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | m1_subset_1(sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
% 52.00/7.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 52.00/7.00      | v2_struct_0(sK1) = iProver_top
% 52.00/7.00      | v2_pre_topc(sK1) != iProver_top
% 52.00/7.00      | l1_pre_topc(sK1) != iProver_top ),
% 52.00/7.00      inference(light_normalisation,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_41049,c_2461,c_8328]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_41288,plain,
% 52.00/7.00      ( k2_struct_0(sK1) = k1_xboole_0
% 52.00/7.00      | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | m1_subset_1(sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
% 52.00/7.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 52.00/7.00      | v2_struct_0(sK1) = iProver_top
% 52.00/7.00      | v2_pre_topc(sK1) != iProver_top
% 52.00/7.00      | l1_pre_topc(sK1) != iProver_top ),
% 52.00/7.00      inference(demodulation,[status(thm)],[c_41287,c_7350]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_49596,plain,
% 52.00/7.00      ( k2_struct_0(sK1) = k1_xboole_0
% 52.00/7.00      | m1_subset_1(sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_41288,c_42,c_43,c_44,c_2701,c_5196,c_8343,c_8344,
% 52.00/7.00                 c_8345,c_8347,c_35453]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_8,plain,
% 52.00/7.00      ( ~ r2_hidden(X0,u1_pre_topc(X1))
% 52.00/7.00      | v3_pre_topc(X0,X1)
% 52.00/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 52.00/7.00      | ~ l1_pre_topc(X1) ),
% 52.00/7.00      inference(cnf_transformation,[],[f65]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_1679,plain,
% 52.00/7.00      ( r2_hidden(X0,u1_pre_topc(X1)) != iProver_top
% 52.00/7.00      | v3_pre_topc(X0,X1) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 52.00/7.00      | l1_pre_topc(X1) != iProver_top ),
% 52.00/7.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_3991,plain,
% 52.00/7.00      ( r2_hidden(X0,u1_pre_topc(sK1)) != iProver_top
% 52.00/7.00      | v3_pre_topc(X0,sK1) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 52.00/7.00      | l1_pre_topc(sK1) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_2461,c_1679]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_4289,plain,
% 52.00/7.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 52.00/7.00      | v3_pre_topc(X0,sK1) = iProver_top
% 52.00/7.00      | r2_hidden(X0,u1_pre_topc(sK1)) != iProver_top ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_3991,c_44]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_4290,plain,
% 52.00/7.00      ( r2_hidden(X0,u1_pre_topc(sK1)) != iProver_top
% 52.00/7.00      | v3_pre_topc(X0,sK1) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 52.00/7.00      inference(renaming,[status(thm)],[c_4289]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_49618,plain,
% 52.00/7.00      ( k2_struct_0(sK1) = k1_xboole_0
% 52.00/7.00      | r2_hidden(sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),u1_pre_topc(sK1)) != iProver_top
% 52.00/7.00      | v3_pre_topc(sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),sK1) = iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_49596,c_4290]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_49602,plain,
% 52.00/7.00      ( k2_struct_0(sK1) = k1_xboole_0
% 52.00/7.00      | r1_tarski(sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k2_struct_0(sK1)) = iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_49596,c_1682]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_51806,plain,
% 52.00/7.00      ( k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),k6_partfun1(k2_struct_0(sK1)),sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))) = sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))
% 52.00/7.00      | k2_struct_0(sK1) = k1_xboole_0 ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_49602,c_1645]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_5,plain,
% 52.00/7.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 52.00/7.00      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 52.00/7.00      inference(cnf_transformation,[],[f61]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_1681,plain,
% 52.00/7.00      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 52.00/7.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 52.00/7.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_3207,plain,
% 52.00/7.00      ( k8_relset_1(k2_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)),k7_tmap_1(sK1,sK2),X0) = k10_relat_1(k7_tmap_1(sK1,sK2),X0) ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_2699,c_1681]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_5156,plain,
% 52.00/7.00      ( k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),k7_tmap_1(sK1,sK2),X0) = k10_relat_1(k7_tmap_1(sK1,sK2),X0) ),
% 52.00/7.00      inference(demodulation,[status(thm)],[c_4557,c_3207]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_8341,plain,
% 52.00/7.00      ( k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),k6_partfun1(k2_struct_0(sK1)),X0) = k10_relat_1(k6_partfun1(k2_struct_0(sK1)),X0) ),
% 52.00/7.00      inference(demodulation,[status(thm)],[c_8328,c_5156]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_51830,plain,
% 52.00/7.00      ( k10_relat_1(k6_partfun1(k2_struct_0(sK1)),sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))) = sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))
% 52.00/7.00      | k2_struct_0(sK1) = k1_xboole_0 ),
% 52.00/7.00      inference(demodulation,[status(thm)],[c_51806,c_8341]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_8046,plain,
% 52.00/7.00      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 52.00/7.00      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,X1,k6_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK1),X0,sK0(X1,k6_tmap_1(sK1,sK2),X0)),X1) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(X1) != iProver_top
% 52.00/7.00      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_4557,c_1675]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_8055,plain,
% 52.00/7.00      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 52.00/7.00      | v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,X1,k6_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK1),X0,sK0(X1,k6_tmap_1(sK1,sK2),X0)),X1) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK1)))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(X1) != iProver_top
% 52.00/7.00      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 52.00/7.00      inference(light_normalisation,[status(thm)],[c_8046,c_4557]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_8056,plain,
% 52.00/7.00      ( k2_struct_0(sK1) = k1_xboole_0
% 52.00/7.00      | v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,X1,k6_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK1),X0,sK0(X1,k6_tmap_1(sK1,sK2),X0)),X1) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK1)))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(X1) != iProver_top
% 52.00/7.00      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 52.00/7.00      inference(demodulation,[status(thm)],[c_8055,c_7350]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_48260,plain,
% 52.00/7.00      ( l1_pre_topc(X1) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK1)))) != iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK1),X0,sK0(X1,k6_tmap_1(sK1,sK2),X0)),X1) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,X1,k6_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK1)) != iProver_top
% 52.00/7.00      | k2_struct_0(sK1) = k1_xboole_0 ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_8056,c_42,c_43,c_44,c_45,c_2213]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_48261,plain,
% 52.00/7.00      ( k2_struct_0(sK1) = k1_xboole_0
% 52.00/7.00      | v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,X1,k6_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK1),X0,sK0(X1,k6_tmap_1(sK1,sK2),X0)),X1) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK1)))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(X1) != iProver_top ),
% 52.00/7.00      inference(renaming,[status(thm)],[c_48260]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_48276,plain,
% 52.00/7.00      ( k2_struct_0(sK1) = k1_xboole_0
% 52.00/7.00      | v1_funct_2(X0,u1_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0,sK0(sK1,k6_tmap_1(sK1,sK2),X0)),sK1) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(sK1) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_2461,c_48261]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_48309,plain,
% 52.00/7.00      ( k2_struct_0(sK1) = k1_xboole_0
% 52.00/7.00      | v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0,sK0(sK1,k6_tmap_1(sK1,sK2),X0)),sK1) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(sK1) != iProver_top ),
% 52.00/7.00      inference(light_normalisation,[status(thm)],[c_48276,c_2461]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_8043,plain,
% 52.00/7.00      ( k2_struct_0(X0) = k1_xboole_0
% 52.00/7.00      | v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X1,sK1,X0) = iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0),X1,sK0(sK1,X0,X1)),sK1) != iProver_top
% 52.00/7.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) != iProver_top
% 52.00/7.00      | v1_funct_1(X1) != iProver_top
% 52.00/7.00      | l1_pre_topc(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(sK1) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_2461,c_1675]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_8107,plain,
% 52.00/7.00      ( k2_struct_0(X0) = k1_xboole_0
% 52.00/7.00      | v1_funct_2(X1,k2_struct_0(sK1),u1_struct_0(X0)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X1,sK1,X0) = iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0),X1,sK0(sK1,X0,X1)),sK1) != iProver_top
% 52.00/7.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0)))) != iProver_top
% 52.00/7.00      | v1_funct_1(X1) != iProver_top
% 52.00/7.00      | l1_pre_topc(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(sK1) != iProver_top ),
% 52.00/7.00      inference(light_normalisation,[status(thm)],[c_8043,c_2461]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_18263,plain,
% 52.00/7.00      ( l1_pre_topc(X0) != iProver_top
% 52.00/7.00      | v1_funct_1(X1) != iProver_top
% 52.00/7.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0)))) != iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0),X1,sK0(sK1,X0,X1)),sK1) != iProver_top
% 52.00/7.00      | v5_pre_topc(X1,sK1,X0) = iProver_top
% 52.00/7.00      | v1_funct_2(X1,k2_struct_0(sK1),u1_struct_0(X0)) != iProver_top
% 52.00/7.00      | k2_struct_0(X0) = k1_xboole_0 ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_8107,c_44]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_18264,plain,
% 52.00/7.00      ( k2_struct_0(X0) = k1_xboole_0
% 52.00/7.00      | v1_funct_2(X1,k2_struct_0(sK1),u1_struct_0(X0)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X1,sK1,X0) = iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0),X1,sK0(sK1,X0,X1)),sK1) != iProver_top
% 52.00/7.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0)))) != iProver_top
% 52.00/7.00      | v1_funct_1(X1) != iProver_top
% 52.00/7.00      | l1_pre_topc(X0) != iProver_top ),
% 52.00/7.00      inference(renaming,[status(thm)],[c_18263]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_18276,plain,
% 52.00/7.00      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 52.00/7.00      | v1_funct_2(X0,k2_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0,sK0(sK1,k6_tmap_1(sK1,sK2),X0)),sK1) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_4557,c_18264]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_18300,plain,
% 52.00/7.00      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 52.00/7.00      | v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0,sK0(sK1,k6_tmap_1(sK1,sK2),X0)),sK1) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 52.00/7.00      inference(light_normalisation,[status(thm)],[c_18276,c_4557]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_18301,plain,
% 52.00/7.00      ( k2_struct_0(sK1) = k1_xboole_0
% 52.00/7.00      | v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0,sK0(sK1,k6_tmap_1(sK1,sK2),X0)),sK1) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 52.00/7.00      inference(demodulation,[status(thm)],[c_18300,c_7350]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_48807,plain,
% 52.00/7.00      ( v1_funct_1(X0) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0,sK0(sK1,k6_tmap_1(sK1,sK2),X0)),sK1) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 52.00/7.00      | k2_struct_0(sK1) = k1_xboole_0 ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_48309,c_42,c_43,c_44,c_45,c_2213,c_18301]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_48808,plain,
% 52.00/7.00      ( k2_struct_0(sK1) = k1_xboole_0
% 52.00/7.00      | v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0,sK0(sK1,k6_tmap_1(sK1,sK2),X0)),sK1) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top ),
% 52.00/7.00      inference(renaming,[status(thm)],[c_48807]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_48822,plain,
% 52.00/7.00      ( k2_struct_0(sK1) = k1_xboole_0
% 52.00/7.00      | v1_funct_2(k6_partfun1(k2_struct_0(sK1)),k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK1)),sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))),sK1) != iProver_top
% 52.00/7.00      | m1_subset_1(k6_partfun1(k2_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 52.00/7.00      | v1_funct_1(k6_partfun1(k2_struct_0(sK1))) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_8341,c_48808]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_95335,plain,
% 52.00/7.00      ( k2_struct_0(sK1) = k1_xboole_0
% 52.00/7.00      | v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK1)),sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))),sK1) != iProver_top ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_48822,c_42,c_43,c_44,c_2701,c_5196,c_8343,c_8344,
% 52.00/7.00                 c_8345,c_8347,c_35453]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_95341,plain,
% 52.00/7.00      ( k2_struct_0(sK1) = k1_xboole_0
% 52.00/7.00      | v3_pre_topc(sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),sK1) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_51830,c_95335]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_14,plain,
% 52.00/7.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 52.00/7.00      | v5_pre_topc(X0,X1,X2)
% 52.00/7.00      | v3_pre_topc(sK0(X1,X2,X0),X2)
% 52.00/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 52.00/7.00      | ~ v1_funct_1(X0)
% 52.00/7.00      | ~ l1_pre_topc(X1)
% 52.00/7.00      | ~ l1_pre_topc(X2)
% 52.00/7.00      | k2_struct_0(X2) = k1_xboole_0 ),
% 52.00/7.00      inference(cnf_transformation,[],[f71]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_1673,plain,
% 52.00/7.00      ( k2_struct_0(X0) = k1_xboole_0
% 52.00/7.00      | v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X0)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X1,X2,X0) = iProver_top
% 52.00/7.00      | v3_pre_topc(sK0(X2,X0,X1),X0) = iProver_top
% 52.00/7.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) != iProver_top
% 52.00/7.00      | v1_funct_1(X1) != iProver_top
% 52.00/7.00      | l1_pre_topc(X2) != iProver_top
% 52.00/7.00      | l1_pre_topc(X0) != iProver_top ),
% 52.00/7.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_6551,plain,
% 52.00/7.00      ( k2_struct_0(k6_tmap_1(X0,X1)) = k1_xboole_0
% 52.00/7.00      | v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) != iProver_top
% 52.00/7.00      | v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) = iProver_top
% 52.00/7.00      | v3_pre_topc(sK0(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1)),k6_tmap_1(X0,X1)) = iProver_top
% 52.00/7.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 52.00/7.00      | v2_struct_0(X0) = iProver_top
% 52.00/7.00      | v2_pre_topc(X0) != iProver_top
% 52.00/7.00      | v1_funct_1(k7_tmap_1(X0,X1)) != iProver_top
% 52.00/7.00      | l1_pre_topc(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(k6_tmap_1(X0,X1)) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_1665,c_1673]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_33511,plain,
% 52.00/7.00      ( k2_struct_0(k6_tmap_1(X0,X1)) = k1_xboole_0
% 52.00/7.00      | v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) = iProver_top
% 52.00/7.00      | v3_pre_topc(sK0(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1)),k6_tmap_1(X0,X1)) = iProver_top
% 52.00/7.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 52.00/7.00      | v2_struct_0(X0) = iProver_top
% 52.00/7.00      | v2_pre_topc(X0) != iProver_top
% 52.00/7.00      | v1_funct_1(k7_tmap_1(X0,X1)) != iProver_top
% 52.00/7.00      | l1_pre_topc(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(k6_tmap_1(X0,X1)) != iProver_top ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_6551,c_78]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_33526,plain,
% 52.00/7.00      ( k2_struct_0(k6_tmap_1(X0,X1)) = k1_xboole_0
% 52.00/7.00      | v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) = iProver_top
% 52.00/7.00      | v3_pre_topc(sK0(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1)),k6_tmap_1(X0,X1)) = iProver_top
% 52.00/7.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 52.00/7.00      | v2_struct_0(X0) = iProver_top
% 52.00/7.00      | v2_pre_topc(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(X0) != iProver_top ),
% 52.00/7.00      inference(forward_subsumption_resolution,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_33511,c_1667,c_1663]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_33530,plain,
% 52.00/7.00      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 52.00/7.00      | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | v3_pre_topc(sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k6_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 52.00/7.00      | v2_struct_0(sK1) = iProver_top
% 52.00/7.00      | v2_pre_topc(sK1) != iProver_top
% 52.00/7.00      | l1_pre_topc(sK1) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_8328,c_33526]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_33610,plain,
% 52.00/7.00      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 52.00/7.00      | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | v3_pre_topc(sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k6_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 52.00/7.00      | v2_struct_0(sK1) = iProver_top
% 52.00/7.00      | v2_pre_topc(sK1) != iProver_top
% 52.00/7.00      | l1_pre_topc(sK1) != iProver_top ),
% 52.00/7.00      inference(light_normalisation,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_33530,c_2461,c_8328]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_33611,plain,
% 52.00/7.00      ( k2_struct_0(sK1) = k1_xboole_0
% 52.00/7.00      | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | v3_pre_topc(sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k6_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 52.00/7.00      | v2_struct_0(sK1) = iProver_top
% 52.00/7.00      | v2_pre_topc(sK1) != iProver_top
% 52.00/7.00      | l1_pre_topc(sK1) != iProver_top ),
% 52.00/7.00      inference(demodulation,[status(thm)],[c_33610,c_7350]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_49147,plain,
% 52.00/7.00      ( k2_struct_0(sK1) = k1_xboole_0
% 52.00/7.00      | v3_pre_topc(sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k6_tmap_1(sK1,sK2)) = iProver_top ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_33611,c_42,c_43,c_44,c_2701,c_5196,c_8343,c_8344,
% 52.00/7.00                 c_8345,c_8347,c_35453]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_49153,plain,
% 52.00/7.00      ( k2_struct_0(sK1) = k1_xboole_0
% 52.00/7.00      | r2_hidden(sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k5_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | r1_tarski(sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k2_struct_0(sK1)) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_49147,c_13918]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_49154,plain,
% 52.00/7.00      ( k2_struct_0(sK1) = k1_xboole_0
% 52.00/7.00      | r2_hidden(sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k5_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | m1_subset_1(sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_49147,c_10269]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_49170,plain,
% 52.00/7.00      ( r2_hidden(sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k5_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | k2_struct_0(sK1) = k1_xboole_0 ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_49153,c_42,c_43,c_44,c_2701,c_5196,c_8343,c_8344,
% 52.00/7.00                 c_8345,c_8347,c_35453,c_41288,c_49154]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_49171,plain,
% 52.00/7.00      ( k2_struct_0(sK1) = k1_xboole_0
% 52.00/7.00      | r2_hidden(sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k5_tmap_1(sK1,sK2)) = iProver_top ),
% 52.00/7.00      inference(renaming,[status(thm)],[c_49170]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_114703,plain,
% 52.00/7.00      ( k2_struct_0(sK1) = k1_xboole_0
% 52.00/7.00      | r2_hidden(sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),u1_pre_topc(sK1)) = iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_114380,c_49171]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_114963,plain,
% 52.00/7.00      ( k2_struct_0(sK1) = k1_xboole_0 ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_114707,c_49618,c_95341,c_114703]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_115324,plain,
% 52.00/7.00      ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 52.00/7.00      inference(demodulation,[status(thm)],[c_114963,c_8343]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_115345,plain,
% 52.00/7.00      ( u1_struct_0(sK1) = k1_xboole_0 ),
% 52.00/7.00      inference(demodulation,[status(thm)],[c_114963,c_2461]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_15,plain,
% 52.00/7.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 52.00/7.00      | v5_pre_topc(X0,X1,X2)
% 52.00/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 52.00/7.00      | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
% 52.00/7.00      | ~ v1_funct_1(X0)
% 52.00/7.00      | ~ l1_pre_topc(X1)
% 52.00/7.00      | ~ l1_pre_topc(X2)
% 52.00/7.00      | k2_struct_0(X1) != k1_xboole_0 ),
% 52.00/7.00      inference(cnf_transformation,[],[f70]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_1672,plain,
% 52.00/7.00      ( k2_struct_0(X0) != k1_xboole_0
% 52.00/7.00      | v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(X2)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X1,X0,X2) = iProver_top
% 52.00/7.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) != iProver_top
% 52.00/7.00      | m1_subset_1(sK0(X0,X2,X1),k1_zfmisc_1(u1_struct_0(X2))) = iProver_top
% 52.00/7.00      | v1_funct_1(X1) != iProver_top
% 52.00/7.00      | l1_pre_topc(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(X2) != iProver_top ),
% 52.00/7.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_116997,plain,
% 52.00/7.00      ( v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,X1) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) != iProver_top
% 52.00/7.00      | m1_subset_1(sK0(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(X1) != iProver_top
% 52.00/7.00      | l1_pre_topc(sK1) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_114963,c_1672]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_121528,plain,
% 52.00/7.00      ( l1_pre_topc(X1) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | m1_subset_1(sK0(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,X1) = iProver_top
% 52.00/7.00      | v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) != iProver_top ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_116997,c_44]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_121529,plain,
% 52.00/7.00      ( v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,X1) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) != iProver_top
% 52.00/7.00      | m1_subset_1(sK0(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(X1) != iProver_top ),
% 52.00/7.00      inference(renaming,[status(thm)],[c_121528]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_121532,plain,
% 52.00/7.00      ( v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,X1) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X1)))) != iProver_top
% 52.00/7.00      | m1_subset_1(sK0(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(X1) != iProver_top ),
% 52.00/7.00      inference(light_normalisation,[status(thm)],[c_121529,c_115345]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_121544,plain,
% 52.00/7.00      ( v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,X1) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X1)))) != iProver_top
% 52.00/7.00      | r1_tarski(sK0(sK1,X1,X0),u1_struct_0(X1)) = iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(X1) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_121532,c_1682]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_122063,plain,
% 52.00/7.00      ( v1_funct_2(X0,k1_xboole_0,u1_struct_0(sK1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,sK1) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 52.00/7.00      | r1_tarski(sK0(sK1,sK1,X0),u1_struct_0(sK1)) = iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(sK1) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_115345,c_121544]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_122084,plain,
% 52.00/7.00      ( v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,sK1) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 52.00/7.00      | r1_tarski(sK0(sK1,sK1,X0),k1_xboole_0) = iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(sK1) != iProver_top ),
% 52.00/7.00      inference(light_normalisation,[status(thm)],[c_122063,c_115345]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_134344,plain,
% 52.00/7.00      ( v1_funct_1(X0) != iProver_top
% 52.00/7.00      | r1_tarski(sK0(sK1,sK1,X0),k1_xboole_0) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,sK1) = iProver_top
% 52.00/7.00      | v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_122084,c_44]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_134345,plain,
% 52.00/7.00      ( v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,sK1) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 52.00/7.00      | r1_tarski(sK0(sK1,sK1,X0),k1_xboole_0) = iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top ),
% 52.00/7.00      inference(renaming,[status(thm)],[c_134344]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_134356,plain,
% 52.00/7.00      ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) != iProver_top
% 52.00/7.00      | v5_pre_topc(k6_partfun1(k1_xboole_0),sK1,sK1) = iProver_top
% 52.00/7.00      | r1_tarski(sK0(sK1,sK1,k6_partfun1(k1_xboole_0)),k1_xboole_0) = iProver_top
% 52.00/7.00      | v1_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_115324,c_134345]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_4299,plain,
% 52.00/7.00      ( r2_hidden(sK2,u1_pre_topc(sK1)) != iProver_top
% 52.00/7.00      | v3_pre_topc(sK2,sK1) = iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_2701,c_4290]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_28,plain,
% 52.00/7.00      ( r2_hidden(X0,u1_pre_topc(X1))
% 52.00/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 52.00/7.00      | v2_struct_0(X1)
% 52.00/7.00      | ~ v2_pre_topc(X1)
% 52.00/7.00      | ~ l1_pre_topc(X1)
% 52.00/7.00      | k5_tmap_1(X1,X0) != u1_pre_topc(X1) ),
% 52.00/7.00      inference(cnf_transformation,[],[f85]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_6847,plain,
% 52.00/7.00      ( r2_hidden(sK2,u1_pre_topc(sK1))
% 52.00/7.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 52.00/7.00      | v2_struct_0(sK1)
% 52.00/7.00      | ~ v2_pre_topc(sK1)
% 52.00/7.00      | ~ l1_pre_topc(sK1)
% 52.00/7.00      | k5_tmap_1(sK1,sK2) != u1_pre_topc(sK1) ),
% 52.00/7.00      inference(instantiation,[status(thm)],[c_28]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_6848,plain,
% 52.00/7.00      ( k5_tmap_1(sK1,sK2) != u1_pre_topc(sK1)
% 52.00/7.00      | r2_hidden(sK2,u1_pre_topc(sK1)) = iProver_top
% 52.00/7.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 52.00/7.00      | v2_struct_0(sK1) = iProver_top
% 52.00/7.00      | v2_pre_topc(sK1) != iProver_top
% 52.00/7.00      | l1_pre_topc(sK1) != iProver_top ),
% 52.00/7.00      inference(predicate_to_equality,[status(thm)],[c_6847]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_12937,plain,
% 52.00/7.00      ( ~ v3_pre_topc(sK2,sK1) | k5_tmap_1(sK1,sK2) = u1_pre_topc(sK1) ),
% 52.00/7.00      inference(predicate_to_equality_rev,[status(thm)],[c_12936]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_115326,plain,
% 52.00/7.00      ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) = iProver_top ),
% 52.00/7.00      inference(demodulation,[status(thm)],[c_114963,c_8344]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_115327,plain,
% 52.00/7.00      ( v5_pre_topc(k6_partfun1(k1_xboole_0),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v3_pre_topc(sK2,sK1) != iProver_top ),
% 52.00/7.00      inference(demodulation,[status(thm)],[c_114963,c_8345]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_115329,plain,
% 52.00/7.00      ( v1_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
% 52.00/7.00      inference(demodulation,[status(thm)],[c_114963,c_8347]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_743,plain,
% 52.00/7.00      ( ~ v5_pre_topc(X0,X1,X2)
% 52.00/7.00      | v5_pre_topc(X3,X4,X5)
% 52.00/7.00      | X3 != X0
% 52.00/7.00      | X4 != X1
% 52.00/7.00      | X5 != X2 ),
% 52.00/7.00      theory(equality) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_749,plain,
% 52.00/7.00      ( X0 != X1 | X2 != X3 | k6_tmap_1(X0,X2) = k6_tmap_1(X1,X3) ),
% 52.00/7.00      theory(equality) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_102316,plain,
% 52.00/7.00      ( ~ v5_pre_topc(X0,X1,k6_tmap_1(X2,X3))
% 52.00/7.00      | v5_pre_topc(X4,X5,k6_tmap_1(X6,X7))
% 52.00/7.00      | X4 != X0
% 52.00/7.00      | X5 != X1
% 52.00/7.00      | X6 != X2
% 52.00/7.00      | X7 != X3 ),
% 52.00/7.00      inference(resolution,[status(thm)],[c_743,c_749]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_165921,plain,
% 52.00/7.00      ( v5_pre_topc(X0,X1,k6_tmap_1(X2,X3))
% 52.00/7.00      | v3_pre_topc(sK2,sK1)
% 52.00/7.00      | X0 != k7_tmap_1(sK1,sK2)
% 52.00/7.00      | X3 != sK2
% 52.00/7.00      | X1 != sK1
% 52.00/7.00      | X2 != sK1 ),
% 52.00/7.00      inference(resolution,[status(thm)],[c_102316,c_35]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_2716,plain,
% 52.00/7.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) ),
% 52.00/7.00      inference(predicate_to_equality_rev,[status(thm)],[c_2701]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_5307,plain,
% 52.00/7.00      ( v3_pre_topc(sK2,k6_tmap_1(sK1,sK2))
% 52.00/7.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1)))
% 52.00/7.00      | v2_struct_0(sK1)
% 52.00/7.00      | ~ v2_pre_topc(sK1)
% 52.00/7.00      | ~ l1_pre_topc(sK1) ),
% 52.00/7.00      inference(predicate_to_equality_rev,[status(thm)],[c_5196]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_116952,plain,
% 52.00/7.00      ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
% 52.00/7.00      inference(predicate_to_equality_rev,[status(thm)],[c_115324]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_116954,plain,
% 52.00/7.00      ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) ),
% 52.00/7.00      inference(predicate_to_equality_rev,[status(thm)],[c_115326]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_115328,plain,
% 52.00/7.00      ( v5_pre_topc(k6_partfun1(k1_xboole_0),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | v3_pre_topc(sK2,sK1) = iProver_top ),
% 52.00/7.00      inference(demodulation,[status(thm)],[c_114963,c_8346]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_116956,plain,
% 52.00/7.00      ( v5_pre_topc(k6_partfun1(k1_xboole_0),sK1,k6_tmap_1(sK1,sK2))
% 52.00/7.00      | v3_pre_topc(sK2,sK1) ),
% 52.00/7.00      inference(predicate_to_equality_rev,[status(thm)],[c_115328]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_116957,plain,
% 52.00/7.00      ( v1_funct_1(k6_partfun1(k1_xboole_0)) ),
% 52.00/7.00      inference(predicate_to_equality_rev,[status(thm)],[c_115329]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_115344,plain,
% 52.00/7.00      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 52.00/7.00      inference(demodulation,[status(thm)],[c_114963,c_2701]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_116982,plain,
% 52.00/7.00      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
% 52.00/7.00      inference(predicate_to_equality_rev,[status(thm)],[c_115344]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_115341,plain,
% 52.00/7.00      ( k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK2) = sK2 ),
% 52.00/7.00      inference(demodulation,[status(thm)],[c_114963,c_3547]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_115336,plain,
% 52.00/7.00      ( u1_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0 ),
% 52.00/7.00      inference(demodulation,[status(thm)],[c_114963,c_4557]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_17,plain,
% 52.00/7.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 52.00/7.00      | ~ v5_pre_topc(X0,X1,X2)
% 52.00/7.00      | ~ v3_pre_topc(X3,X2)
% 52.00/7.00      | v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
% 52.00/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 52.00/7.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 52.00/7.00      | ~ v1_funct_1(X0)
% 52.00/7.00      | ~ l1_pre_topc(X1)
% 52.00/7.00      | ~ l1_pre_topc(X2)
% 52.00/7.00      | k2_struct_0(X1) != k1_xboole_0 ),
% 52.00/7.00      inference(cnf_transformation,[],[f68]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_1670,plain,
% 52.00/7.00      ( k2_struct_0(X0) != k1_xboole_0
% 52.00/7.00      | v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(X2)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X1,X0,X2) != iProver_top
% 52.00/7.00      | v3_pre_topc(X3,X2) != iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X3),X0) = iProver_top
% 52.00/7.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) != iProver_top
% 52.00/7.00      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
% 52.00/7.00      | v1_funct_1(X1) != iProver_top
% 52.00/7.00      | l1_pre_topc(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(X2) != iProver_top ),
% 52.00/7.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_116996,plain,
% 52.00/7.00      ( v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,X1) != iProver_top
% 52.00/7.00      | v3_pre_topc(X2,X1) != iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X0,X2),sK1) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) != iProver_top
% 52.00/7.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(X1) != iProver_top
% 52.00/7.00      | l1_pre_topc(sK1) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_114963,c_1670]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_148047,plain,
% 52.00/7.00      ( l1_pre_topc(X1) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) != iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X0,X2),sK1) = iProver_top
% 52.00/7.00      | v3_pre_topc(X2,X1) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,X1) != iProver_top
% 52.00/7.00      | v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) != iProver_top ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_116996,c_44]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_148048,plain,
% 52.00/7.00      ( v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,X1) != iProver_top
% 52.00/7.00      | v3_pre_topc(X2,X1) != iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X0,X2),sK1) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) != iProver_top
% 52.00/7.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(X1) != iProver_top ),
% 52.00/7.00      inference(renaming,[status(thm)],[c_148047]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_148051,plain,
% 52.00/7.00      ( v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,X1) != iProver_top
% 52.00/7.00      | v3_pre_topc(X2,X1) != iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X1),X0,X2),sK1) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X1)))) != iProver_top
% 52.00/7.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(X1) != iProver_top ),
% 52.00/7.00      inference(light_normalisation,[status(thm)],[c_148048,c_115345]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_148065,plain,
% 52.00/7.00      ( v1_funct_2(X0,k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v3_pre_topc(X1,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0,X1),sK1) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
% 52.00/7.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_115336,c_148051]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_148075,plain,
% 52.00/7.00      ( v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v3_pre_topc(X1,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0,X1),sK1) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 52.00/7.00      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 52.00/7.00      inference(light_normalisation,[status(thm)],[c_148065,c_115336]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_148974,plain,
% 52.00/7.00      ( v1_funct_1(X0) != iProver_top
% 52.00/7.00      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0,X1),sK1) = iProver_top
% 52.00/7.00      | v3_pre_topc(X1,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_148075,c_42,c_43,c_44,c_45,c_2213]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_148975,plain,
% 52.00/7.00      ( v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v3_pre_topc(X1,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0,X1),sK1) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 52.00/7.00      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top ),
% 52.00/7.00      inference(renaming,[status(thm)],[c_148974]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_148990,plain,
% 52.00/7.00      ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) != iProver_top
% 52.00/7.00      | v5_pre_topc(k6_partfun1(k1_xboole_0),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v3_pre_topc(sK2,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v3_pre_topc(sK2,sK1) = iProver_top
% 52.00/7.00      | m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 52.00/7.00      | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 52.00/7.00      | v1_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_115341,c_148975]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_149070,plain,
% 52.00/7.00      ( ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
% 52.00/7.00      | ~ v5_pre_topc(k6_partfun1(k1_xboole_0),sK1,k6_tmap_1(sK1,sK2))
% 52.00/7.00      | ~ v3_pre_topc(sK2,k6_tmap_1(sK1,sK2))
% 52.00/7.00      | v3_pre_topc(sK2,sK1)
% 52.00/7.00      | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
% 52.00/7.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
% 52.00/7.00      | ~ v1_funct_1(k6_partfun1(k1_xboole_0)) ),
% 52.00/7.00      inference(predicate_to_equality_rev,[status(thm)],[c_148990]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_166127,plain,
% 52.00/7.00      ( v3_pre_topc(sK2,sK1) ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_165921,c_41,c_40,c_39,c_2716,c_5307,c_116952,c_116954,
% 52.00/7.00                 c_116956,c_116957,c_116982,c_149070]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_148064,plain,
% 52.00/7.00      ( v1_funct_2(X0,k1_xboole_0,u1_struct_0(sK1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,sK1) != iProver_top
% 52.00/7.00      | v3_pre_topc(X1,sK1) != iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0,X1),sK1) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) != iProver_top
% 52.00/7.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(sK1) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_115345,c_148051]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_148092,plain,
% 52.00/7.00      ( v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,sK1) != iProver_top
% 52.00/7.00      | v3_pre_topc(X1,sK1) != iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0,X1),sK1) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 52.00/7.00      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(sK1) != iProver_top ),
% 52.00/7.00      inference(light_normalisation,[status(thm)],[c_148064,c_115345]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_148818,plain,
% 52.00/7.00      ( v1_funct_1(X0) != iProver_top
% 52.00/7.00      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0,X1),sK1) = iProver_top
% 52.00/7.00      | v3_pre_topc(X1,sK1) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,sK1) != iProver_top
% 52.00/7.00      | v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_148092,c_44]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_148819,plain,
% 52.00/7.00      ( v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,sK1) != iProver_top
% 52.00/7.00      | v3_pre_topc(X1,sK1) != iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0,X1),sK1) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 52.00/7.00      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top ),
% 52.00/7.00      inference(renaming,[status(thm)],[c_148818]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_11,plain,
% 52.00/7.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 52.00/7.00      | v5_pre_topc(X0,X1,X2)
% 52.00/7.00      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0)),X1)
% 52.00/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 52.00/7.00      | ~ v1_funct_1(X0)
% 52.00/7.00      | ~ l1_pre_topc(X1)
% 52.00/7.00      | ~ l1_pre_topc(X2)
% 52.00/7.00      | k2_struct_0(X1) != k1_xboole_0 ),
% 52.00/7.00      inference(cnf_transformation,[],[f74]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_1676,plain,
% 52.00/7.00      ( k2_struct_0(X0) != k1_xboole_0
% 52.00/7.00      | v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(X2)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X1,X0,X2) = iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,sK0(X0,X2,X1)),X0) != iProver_top
% 52.00/7.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) != iProver_top
% 52.00/7.00      | v1_funct_1(X1) != iProver_top
% 52.00/7.00      | l1_pre_topc(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(X2) != iProver_top ),
% 52.00/7.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_116995,plain,
% 52.00/7.00      ( v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,X1) = iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X0,sK0(sK1,X1,X0)),sK1) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(X1) != iProver_top
% 52.00/7.00      | l1_pre_topc(sK1) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_114963,c_1676]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_128802,plain,
% 52.00/7.00      ( l1_pre_topc(X1) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) != iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X0,sK0(sK1,X1,X0)),sK1) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,X1) = iProver_top
% 52.00/7.00      | v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) != iProver_top ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_116995,c_44]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_128803,plain,
% 52.00/7.00      ( v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,X1) = iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X0,sK0(sK1,X1,X0)),sK1) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(X1) != iProver_top ),
% 52.00/7.00      inference(renaming,[status(thm)],[c_128802]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_128806,plain,
% 52.00/7.00      ( v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,X1) = iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X1),X0,sK0(sK1,X1,X0)),sK1) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X1)))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(X1) != iProver_top ),
% 52.00/7.00      inference(light_normalisation,[status(thm)],[c_128803,c_115345]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_128818,plain,
% 52.00/7.00      ( v1_funct_2(X0,k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0,sK0(sK1,k6_tmap_1(sK1,sK2),X0)),sK1) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_115336,c_128806]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_128825,plain,
% 52.00/7.00      ( v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0,sK0(sK1,k6_tmap_1(sK1,sK2),X0)),sK1) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 52.00/7.00      inference(light_normalisation,[status(thm)],[c_128818,c_115336]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_129618,plain,
% 52.00/7.00      ( v1_funct_1(X0) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0,sK0(sK1,k6_tmap_1(sK1,sK2),X0)),sK1) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_128825,c_42,c_43,c_44,c_45,c_2213]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_129619,plain,
% 52.00/7.00      ( v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0,sK0(sK1,k6_tmap_1(sK1,sK2),X0)),sK1) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top ),
% 52.00/7.00      inference(renaming,[status(thm)],[c_129618]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_148836,plain,
% 52.00/7.00      ( v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,sK1) != iProver_top
% 52.00/7.00      | v3_pre_topc(sK0(sK1,k6_tmap_1(sK1,sK2),X0),sK1) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 52.00/7.00      | m1_subset_1(sK0(sK1,k6_tmap_1(sK1,sK2),X0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_148819,c_129619]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_121543,plain,
% 52.00/7.00      ( v1_funct_2(X0,k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
% 52.00/7.00      | m1_subset_1(sK0(sK1,k6_tmap_1(sK1,sK2),X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_115336,c_121532]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_121731,plain,
% 52.00/7.00      ( v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 52.00/7.00      | m1_subset_1(sK0(sK1,k6_tmap_1(sK1,sK2),X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 52.00/7.00      inference(light_normalisation,[status(thm)],[c_121543,c_115336]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_122064,plain,
% 52.00/7.00      ( v1_funct_2(X0,k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 52.00/7.00      | r1_tarski(sK0(sK1,k6_tmap_1(sK1,sK2),X0),u1_struct_0(k6_tmap_1(sK1,sK2))) = iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_115336,c_121544]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_122071,plain,
% 52.00/7.00      ( v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 52.00/7.00      | r1_tarski(sK0(sK1,k6_tmap_1(sK1,sK2),X0),k1_xboole_0) = iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 52.00/7.00      inference(light_normalisation,[status(thm)],[c_122064,c_115336]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_1,plain,
% 52.00/7.00      ( r1_tarski(X0,X0) ),
% 52.00/7.00      inference(cnf_transformation,[],[f98]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_1684,plain,
% 52.00/7.00      ( r1_tarski(X0,X0) = iProver_top ),
% 52.00/7.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_3545,plain,
% 52.00/7.00      ( k8_relset_1(X0,X0,k6_partfun1(X0),X0) = X0 ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_1684,c_1645]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_148988,plain,
% 52.00/7.00      ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) != iProver_top
% 52.00/7.00      | v5_pre_topc(k6_partfun1(k1_xboole_0),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v3_pre_topc(k1_xboole_0,k6_tmap_1(sK1,sK2)) != iProver_top
% 52.00/7.00      | v3_pre_topc(k1_xboole_0,sK1) = iProver_top
% 52.00/7.00      | m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 52.00/7.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 52.00/7.00      | v1_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_3545,c_148975]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_171517,plain,
% 52.00/7.00      ( v5_pre_topc(k6_partfun1(k1_xboole_0),sK1,k6_tmap_1(sK1,sK2)) != iProver_top ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_148988,c_41,c_42,c_40,c_43,c_39,c_44,c_45,c_2716,
% 52.00/7.00                 c_4299,c_5307,c_6848,c_12937,c_116952,c_116954,c_115327,
% 52.00/7.00                 c_116956,c_116957,c_116982,c_149070]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_171527,plain,
% 52.00/7.00      ( v3_pre_topc(sK2,sK1) = iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_115328,c_171517]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_171701,plain,
% 52.00/7.00      ( k5_tmap_1(sK1,sK2) = u1_pre_topc(sK1) ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_171527,c_12936]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_121554,plain,
% 52.00/7.00      ( v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,X1) = iProver_top
% 52.00/7.00      | r2_hidden(sK0(sK1,X1,X0),u1_pre_topc(X1)) = iProver_top
% 52.00/7.00      | v3_pre_topc(sK0(sK1,X1,X0),X1) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X1)))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(X1) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_121532,c_1678]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_13,plain,
% 52.00/7.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 52.00/7.00      | v5_pre_topc(X0,X1,X2)
% 52.00/7.00      | v3_pre_topc(sK0(X1,X2,X0),X2)
% 52.00/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 52.00/7.00      | ~ v1_funct_1(X0)
% 52.00/7.00      | ~ l1_pre_topc(X1)
% 52.00/7.00      | ~ l1_pre_topc(X2)
% 52.00/7.00      | k2_struct_0(X1) != k1_xboole_0 ),
% 52.00/7.00      inference(cnf_transformation,[],[f72]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_1674,plain,
% 52.00/7.00      ( k2_struct_0(X0) != k1_xboole_0
% 52.00/7.00      | v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(X2)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X1,X0,X2) = iProver_top
% 52.00/7.00      | v3_pre_topc(sK0(X0,X2,X1),X2) = iProver_top
% 52.00/7.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) != iProver_top
% 52.00/7.00      | v1_funct_1(X1) != iProver_top
% 52.00/7.00      | l1_pre_topc(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(X2) != iProver_top ),
% 52.00/7.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_116998,plain,
% 52.00/7.00      ( v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,X1) = iProver_top
% 52.00/7.00      | v3_pre_topc(sK0(sK1,X1,X0),X1) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(X1) != iProver_top
% 52.00/7.00      | l1_pre_topc(sK1) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_114963,c_1674]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_117656,plain,
% 52.00/7.00      ( l1_pre_topc(X1) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) != iProver_top
% 52.00/7.00      | v3_pre_topc(sK0(sK1,X1,X0),X1) = iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,X1) = iProver_top
% 52.00/7.00      | v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) != iProver_top ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_116998,c_44]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_117657,plain,
% 52.00/7.00      ( v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,X1) = iProver_top
% 52.00/7.00      | v3_pre_topc(sK0(sK1,X1,X0),X1) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(X1) != iProver_top ),
% 52.00/7.00      inference(renaming,[status(thm)],[c_117656]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_118405,plain,
% 52.00/7.00      ( v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,X1) = iProver_top
% 52.00/7.00      | v3_pre_topc(sK0(sK1,X1,X0),X1) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X1)))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(X1) != iProver_top ),
% 52.00/7.00      inference(demodulation,[status(thm)],[c_115345,c_117657]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_123853,plain,
% 52.00/7.00      ( r2_hidden(sK0(sK1,X1,X0),u1_pre_topc(X1)) = iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,X1) = iProver_top
% 52.00/7.00      | v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X1)))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(X1) != iProver_top ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_121554,c_118405]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_123854,plain,
% 52.00/7.00      ( v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,X1) = iProver_top
% 52.00/7.00      | r2_hidden(sK0(sK1,X1,X0),u1_pre_topc(X1)) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X1)))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(X1) != iProver_top ),
% 52.00/7.00      inference(renaming,[status(thm)],[c_123853]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_123867,plain,
% 52.00/7.00      ( v1_funct_2(X0,k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | r2_hidden(sK0(sK1,k6_tmap_1(sK1,sK2),X0),u1_pre_topc(k6_tmap_1(sK1,sK2))) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_115336,c_123854]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_123874,plain,
% 52.00/7.00      ( v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | r2_hidden(sK0(sK1,k6_tmap_1(sK1,sK2),X0),k5_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 52.00/7.00      inference(light_normalisation,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_123867,c_10092,c_115336]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_124110,plain,
% 52.00/7.00      ( v1_funct_1(X0) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 52.00/7.00      | r2_hidden(sK0(sK1,k6_tmap_1(sK1,sK2),X0),k5_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_123874,c_42,c_43,c_44,c_45,c_2213]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_124111,plain,
% 52.00/7.00      ( v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | r2_hidden(sK0(sK1,k6_tmap_1(sK1,sK2),X0),k5_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top ),
% 52.00/7.00      inference(renaming,[status(thm)],[c_124110]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_171726,plain,
% 52.00/7.00      ( v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | r2_hidden(sK0(sK1,k6_tmap_1(sK1,sK2),X0),u1_pre_topc(sK1)) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top ),
% 52.00/7.00      inference(demodulation,[status(thm)],[c_171701,c_124111]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_4298,plain,
% 52.00/7.00      ( r2_hidden(X0,u1_pre_topc(sK1)) != iProver_top
% 52.00/7.00      | v3_pre_topc(X0,sK1) = iProver_top
% 52.00/7.00      | r1_tarski(X0,k2_struct_0(sK1)) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_1683,c_4290]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_115281,plain,
% 52.00/7.00      ( r2_hidden(X0,u1_pre_topc(sK1)) != iProver_top
% 52.00/7.00      | v3_pre_topc(X0,sK1) = iProver_top
% 52.00/7.00      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 52.00/7.00      inference(demodulation,[status(thm)],[c_114963,c_4298]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_172510,plain,
% 52.00/7.00      ( v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | v3_pre_topc(sK0(sK1,k6_tmap_1(sK1,sK2),X0),sK1) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 52.00/7.00      | r1_tarski(sK0(sK1,k6_tmap_1(sK1,sK2),X0),k1_xboole_0) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_171726,c_115281]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_176976,plain,
% 52.00/7.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 52.00/7.00      | v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,sK1) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_148836,c_42,c_43,c_44,c_45,c_2213,c_121731,c_122071,
% 52.00/7.00                 c_172510]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_176977,plain,
% 52.00/7.00      ( v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,sK1) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top ),
% 52.00/7.00      inference(renaming,[status(thm)],[c_176976]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_176988,plain,
% 52.00/7.00      ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) != iProver_top
% 52.00/7.00      | v5_pre_topc(k6_partfun1(k1_xboole_0),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 52.00/7.00      | v5_pre_topc(k6_partfun1(k1_xboole_0),sK1,sK1) != iProver_top
% 52.00/7.00      | v1_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_115324,c_176977]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_187327,plain,
% 52.00/7.00      ( r1_tarski(sK0(sK1,sK1,k6_partfun1(k1_xboole_0)),k1_xboole_0) = iProver_top ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_134356,c_41,c_42,c_40,c_43,c_39,c_44,c_45,c_2716,
% 52.00/7.00                 c_4299,c_5307,c_6848,c_12937,c_116952,c_115326,c_116954,
% 52.00/7.00                 c_115327,c_116956,c_115329,c_116957,c_116982,c_149070,
% 52.00/7.00                 c_176988]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_187332,plain,
% 52.00/7.00      ( k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK0(sK1,sK1,k6_partfun1(k1_xboole_0))) = sK0(sK1,sK1,k6_partfun1(k1_xboole_0)) ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_187327,c_1645]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_128817,plain,
% 52.00/7.00      ( v1_funct_2(X0,k1_xboole_0,u1_struct_0(sK1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,sK1) = iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0,sK0(sK1,sK1,X0)),sK1) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(sK1) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_115345,c_128806]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_128838,plain,
% 52.00/7.00      ( v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,sK1) = iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0,sK0(sK1,sK1,X0)),sK1) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(sK1) != iProver_top ),
% 52.00/7.00      inference(light_normalisation,[status(thm)],[c_128817,c_115345]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_129397,plain,
% 52.00/7.00      ( v1_funct_1(X0) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0,sK0(sK1,sK1,X0)),sK1) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,sK1) = iProver_top
% 52.00/7.00      | v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_128838,c_44]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_129398,plain,
% 52.00/7.00      ( v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,sK1) = iProver_top
% 52.00/7.00      | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0,sK0(sK1,sK1,X0)),sK1) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top ),
% 52.00/7.00      inference(renaming,[status(thm)],[c_129397]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_188496,plain,
% 52.00/7.00      ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) != iProver_top
% 52.00/7.00      | v5_pre_topc(k6_partfun1(k1_xboole_0),sK1,sK1) = iProver_top
% 52.00/7.00      | v3_pre_topc(sK0(sK1,sK1,k6_partfun1(k1_xboole_0)),sK1) != iProver_top
% 52.00/7.00      | m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 52.00/7.00      | v1_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_187332,c_129398]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_136185,plain,
% 52.00/7.00      ( v1_funct_2(X0,k1_xboole_0,u1_struct_0(sK1)) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,sK1) = iProver_top
% 52.00/7.00      | v3_pre_topc(sK0(sK1,sK1,X0),sK1) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(sK1) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_115345,c_118405]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_136206,plain,
% 52.00/7.00      ( v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,sK1) = iProver_top
% 52.00/7.00      | v3_pre_topc(sK0(sK1,sK1,X0),sK1) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top
% 52.00/7.00      | l1_pre_topc(sK1) != iProver_top ),
% 52.00/7.00      inference(light_normalisation,[status(thm)],[c_136185,c_115345]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_136528,plain,
% 52.00/7.00      ( v1_funct_1(X0) != iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 52.00/7.00      | v3_pre_topc(sK0(sK1,sK1,X0),sK1) = iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,sK1) = iProver_top
% 52.00/7.00      | v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 52.00/7.00      inference(global_propositional_subsumption,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_136206,c_44]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_136529,plain,
% 52.00/7.00      ( v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
% 52.00/7.00      | v5_pre_topc(X0,sK1,sK1) = iProver_top
% 52.00/7.00      | v3_pre_topc(sK0(sK1,sK1,X0),sK1) = iProver_top
% 52.00/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 52.00/7.00      | v1_funct_1(X0) != iProver_top ),
% 52.00/7.00      inference(renaming,[status(thm)],[c_136528]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(c_136540,plain,
% 52.00/7.00      ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) != iProver_top
% 52.00/7.00      | v5_pre_topc(k6_partfun1(k1_xboole_0),sK1,sK1) = iProver_top
% 52.00/7.00      | v3_pre_topc(sK0(sK1,sK1,k6_partfun1(k1_xboole_0)),sK1) = iProver_top
% 52.00/7.00      | v1_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top ),
% 52.00/7.00      inference(superposition,[status(thm)],[c_115324,c_136529]) ).
% 52.00/7.00  
% 52.00/7.00  cnf(contradiction,plain,
% 52.00/7.00      ( $false ),
% 52.00/7.00      inference(minisat,
% 52.00/7.00                [status(thm)],
% 52.00/7.00                [c_188496,c_176988,c_166127,c_136540,c_115329,c_115327,
% 52.00/7.00                 c_115326,c_115324,c_12937,c_6848,c_4299,c_45,c_44,c_43,
% 52.00/7.00                 c_42]) ).
% 52.00/7.00  
% 52.00/7.00  
% 52.00/7.00  % SZS output end CNFRefutation for theBenchmark.p
% 52.00/7.00  
% 52.00/7.00  ------                               Statistics
% 52.00/7.00  
% 52.00/7.00  ------ Selected
% 52.00/7.00  
% 52.00/7.00  total_time:                             6.429
% 52.00/7.00  
%------------------------------------------------------------------------------
