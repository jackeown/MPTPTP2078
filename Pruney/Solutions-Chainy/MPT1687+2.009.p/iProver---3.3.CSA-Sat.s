%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:14 EST 2020

% Result     : CounterSatisfiable 3.74s
% Output     : Saturation 3.74s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_8111)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v23_waybel_0(X2,X0,X1)
               => ( k2_relat_1(k2_funct_1(X2)) = u1_struct_0(X0)
                  & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(k2_funct_1(X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( v23_waybel_0(X2,X0,X1)
                 => ( k2_relat_1(k2_funct_1(X2)) = u1_struct_0(X0)
                    & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(k2_funct_1(X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f16,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( k2_relat_1(k2_funct_1(X2)) = u1_struct_0(X0)
                  & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(k2_funct_1(X2)) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0)
                | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                | ~ v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
                | ~ v1_funct_1(k2_funct_1(X2)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0)
                | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                | ~ v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
                | ~ v1_funct_1(k2_funct_1(X2)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0)
            | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            | ~ v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
            | ~ v1_funct_1(k2_funct_1(X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ( k2_relat_1(k2_funct_1(sK3)) != u1_struct_0(X0)
          | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          | ~ v1_funct_2(k2_funct_1(sK3),u1_struct_0(X1),u1_struct_0(X0))
          | ~ v1_funct_1(k2_funct_1(sK3)) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0)
                | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                | ~ v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
                | ~ v1_funct_1(k2_funct_1(X2)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ( k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0)
              | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
              | ~ v1_funct_2(k2_funct_1(X2),u1_struct_0(sK2),u1_struct_0(X0))
              | ~ v1_funct_1(k2_funct_1(X2)) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK2))
            & v1_funct_1(X2) )
        & l1_orders_2(sK2)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0)
                  | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  | ~ v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
                  | ~ v1_funct_1(k2_funct_1(X2)) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_orders_2(X1)
            & ~ v2_struct_0(X1) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( k2_relat_1(k2_funct_1(X2)) != u1_struct_0(sK1)
                | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
                | ~ v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(sK1))
                | ~ v1_funct_1(k2_funct_1(X2)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ( k2_relat_1(k2_funct_1(sK3)) != u1_struct_0(sK1)
      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | ~ v1_funct_2(k2_funct_1(sK3),u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ v1_funct_1(k2_funct_1(sK3)) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    & v1_funct_1(sK3)
    & l1_orders_2(sK2)
    & ~ v2_struct_0(sK2)
    & l1_orders_2(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f35,f41,f40,f39])).

fof(f65,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f42])).

fof(f66,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f42])).

fof(f64,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f60,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f61,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f59,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_partfun1(X1,X0)
      | k1_relat_1(X1) != X0
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f68,plain,(
    ! [X1] :
      ( v1_partfun1(X1,k1_relat_1(X1))
      | ~ v4_relat_1(X1,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f52])).

fof(f67,plain,
    ( k2_relat_1(k2_funct_1(sK3)) != u1_struct_0(sK1)
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_funct_1(sK3),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f42])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f36])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f46,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f47,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f69,plain,(
    ! [X2,X1] :
      ( v1_partfun1(X2,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f54])).

fof(f63,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f62,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_208,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_13,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_8052,plain,
    ( arAF0_v1_funct_2_0_1_2(X0,k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ iProver_ARSWP_151
    | ~ arAF0_r1_tarski_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_13])).

cnf(c_8543,plain,
    ( arAF0_v1_funct_2_0_1_2(X0,k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | iProver_ARSWP_151 != iProver_top
    | arAF0_r1_tarski_0 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8052])).

cnf(c_12,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_8051,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(arAF0_k2_zfmisc_1_0_1(k1_relat_1(X0))))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ iProver_ARSWP_150
    | ~ arAF0_r1_tarski_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_12])).

cnf(c_8544,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(arAF0_k2_zfmisc_1_0_1(k1_relat_1(X0)))) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | iProver_ARSWP_150 != iProver_top
    | arAF0_r1_tarski_0 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8051])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_8050,plain,
    ( ~ arAF0_v1_funct_2_0_1_2(X0,X1)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(arAF0_k2_zfmisc_1_0_1(X1)))
    | ~ v1_funct_1(X0)
    | ~ iProver_ARSWP_149
    | k1_xboole_0 = X2 ),
    inference(arg_filter_abstr,[status(unp)],[c_11])).

cnf(c_8545,plain,
    ( k1_xboole_0 = X0
    | arAF0_v1_funct_2_0_1_2(X1,X2) != iProver_top
    | v1_partfun1(X1,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(arAF0_k2_zfmisc_1_0_1(X2))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | iProver_ARSWP_149 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8050])).

cnf(c_10420,plain,
    ( k1_xboole_0 = X0
    | arAF0_v1_funct_2_0_1_2(X1,k1_relat_1(X1)) != iProver_top
    | v1_partfun1(X1,k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | iProver_ARSWP_150 != iProver_top
    | iProver_ARSWP_149 != iProver_top
    | arAF0_r1_tarski_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_8544,c_8545])).

cnf(c_12505,plain,
    ( k1_xboole_0 = X0
    | v1_partfun1(X1,k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | iProver_ARSWP_151 != iProver_top
    | iProver_ARSWP_150 != iProver_top
    | iProver_ARSWP_149 != iProver_top
    | arAF0_r1_tarski_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_8543,c_10420])).

cnf(c_19,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_8055,negated_conjecture,
    ( arAF0_v1_funct_2_0_1_2(sK3,u1_struct_0(sK1))
    | ~ iProver_ARSWP_154 ),
    inference(arg_filter_abstr,[status(unp)],[c_19])).

cnf(c_8540,plain,
    ( arAF0_v1_funct_2_0_1_2(sK3,u1_struct_0(sK1)) = iProver_top
    | iProver_ARSWP_154 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8055])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_8054,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(arAF0_k2_zfmisc_1_0_1(u1_struct_0(sK1))))
    | ~ iProver_ARSWP_153 ),
    inference(arg_filter_abstr,[status(unp)],[c_18])).

cnf(c_8541,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(arAF0_k2_zfmisc_1_0_1(u1_struct_0(sK1)))) = iProver_top
    | iProver_ARSWP_153 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8054])).

cnf(c_10419,plain,
    ( k1_xboole_0 = X0
    | arAF0_v1_funct_2_0_1_2(sK3,u1_struct_0(sK1)) != iProver_top
    | v1_partfun1(sK3,u1_struct_0(sK1)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | iProver_ARSWP_153 != iProver_top
    | iProver_ARSWP_149 != iProver_top ),
    inference(superposition,[status(thm)],[c_8541,c_8545])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_29,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_10719,plain,
    ( v1_partfun1(sK3,u1_struct_0(sK1)) = iProver_top
    | arAF0_v1_funct_2_0_1_2(sK3,u1_struct_0(sK1)) != iProver_top
    | k1_xboole_0 = X0
    | iProver_ARSWP_153 != iProver_top
    | iProver_ARSWP_149 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10419,c_29])).

cnf(c_10720,plain,
    ( k1_xboole_0 = X0
    | arAF0_v1_funct_2_0_1_2(sK3,u1_struct_0(sK1)) != iProver_top
    | v1_partfun1(sK3,u1_struct_0(sK1)) = iProver_top
    | iProver_ARSWP_153 != iProver_top
    | iProver_ARSWP_149 != iProver_top ),
    inference(renaming,[status(thm)],[c_10719])).

cnf(c_10730,plain,
    ( k1_xboole_0 = X0
    | v1_partfun1(sK3,u1_struct_0(sK1)) = iProver_top
    | iProver_ARSWP_154 != iProver_top
    | iProver_ARSWP_153 != iProver_top
    | iProver_ARSWP_149 != iProver_top ),
    inference(superposition,[status(thm)],[c_8540,c_10720])).

cnf(c_9,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_8569,plain,
    ( k1_relat_1(X0) = X1
    | v1_partfun1(X0,X1) != iProver_top
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_10740,plain,
    ( u1_struct_0(sK1) = k1_relat_1(sK3)
    | k1_xboole_0 = X0
    | v4_relat_1(sK3,u1_struct_0(sK1)) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | iProver_ARSWP_154 != iProver_top
    | iProver_ARSWP_153 != iProver_top
    | iProver_ARSWP_149 != iProver_top ),
    inference(superposition,[status(thm)],[c_10730,c_8569])).

cnf(c_31,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2126,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2127,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2126])).

cnf(c_6,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2129,plain,
    ( v4_relat_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2130,plain,
    ( v4_relat_1(sK3,u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2129])).

cnf(c_350,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3186,plain,
    ( X0 != X1
    | u1_struct_0(X2) != X1
    | u1_struct_0(X2) = X0 ),
    inference(instantiation,[status(thm)],[c_350])).

cnf(c_3202,plain,
    ( X0 != u1_struct_0(X1)
    | u1_struct_0(X1) = X0
    | u1_struct_0(X1) != u1_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_3186])).

cnf(c_3203,plain,
    ( X0 != u1_struct_0(X1)
    | u1_struct_0(X1) = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_3202])).

cnf(c_3336,plain,
    ( u1_struct_0(X0) = k1_relat_1(sK3)
    | k1_relat_1(sK3) != u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_3203])).

cnf(c_3339,plain,
    ( u1_struct_0(sK1) = k1_relat_1(sK3)
    | k1_relat_1(sK3) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_3336])).

cnf(c_4969,plain,
    ( ~ v1_partfun1(sK3,X0)
    | ~ v4_relat_1(sK3,X0)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) = X0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_5293,plain,
    ( ~ v1_partfun1(sK3,u1_struct_0(X0))
    | ~ v4_relat_1(sK3,u1_struct_0(X0))
    | ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) = u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_4969])).

cnf(c_5294,plain,
    ( k1_relat_1(sK3) = u1_struct_0(X0)
    | v1_partfun1(sK3,u1_struct_0(X0)) != iProver_top
    | v4_relat_1(sK3,u1_struct_0(X0)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5293])).

cnf(c_5296,plain,
    ( k1_relat_1(sK3) = u1_struct_0(sK1)
    | v1_partfun1(sK3,u1_struct_0(sK1)) != iProver_top
    | v4_relat_1(sK3,u1_struct_0(sK1)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5294])).

cnf(c_10834,plain,
    ( u1_struct_0(sK1) = k1_relat_1(sK3)
    | k1_xboole_0 = X0
    | iProver_ARSWP_154 != iProver_top
    | iProver_ARSWP_153 != iProver_top
    | iProver_ARSWP_149 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10740,c_29,c_31,c_2127,c_2130,c_3339,c_5296,c_8111,c_10419])).

cnf(c_10848,plain,
    ( X0 = X1
    | u1_struct_0(sK1) = k1_relat_1(sK3)
    | iProver_ARSWP_154 != iProver_top
    | iProver_ARSWP_153 != iProver_top
    | iProver_ARSWP_149 != iProver_top ),
    inference(superposition,[status(thm)],[c_10834,c_10834])).

cnf(c_11667,plain,
    ( u1_struct_0(sK1) = k1_relat_1(sK3)
    | k1_relat_1(sK3) != X0
    | iProver_ARSWP_154 != iProver_top
    | iProver_ARSWP_153 != iProver_top
    | iProver_ARSWP_149 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_10848])).

cnf(c_11697,plain,
    ( u1_struct_0(sK1) = k1_relat_1(sK3)
    | iProver_ARSWP_154 != iProver_top
    | iProver_ARSWP_153 != iProver_top
    | iProver_ARSWP_149 != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11667,c_10848])).

cnf(c_15,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_8568,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_11835,plain,
    ( v2_struct_0(sK1) = iProver_top
    | l1_struct_0(sK1) != iProver_top
    | v1_xboole_0(k1_relat_1(sK3)) != iProver_top
    | iProver_ARSWP_154 != iProver_top
    | iProver_ARSWP_153 != iProver_top
    | iProver_ARSWP_149 != iProver_top ),
    inference(superposition,[status(thm)],[c_11697,c_8568])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_25,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_26,plain,
    ( l1_orders_2(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_16,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_33,plain,
    ( l1_orders_2(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_35,plain,
    ( l1_orders_2(sK1) != iProver_top
    | l1_struct_0(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_12340,plain,
    ( v1_xboole_0(k1_relat_1(sK3)) != iProver_top
    | iProver_ARSWP_154 != iProver_top
    | iProver_ARSWP_153 != iProver_top
    | iProver_ARSWP_149 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11835,c_25,c_26,c_35,c_38,c_3343,c_11697])).

cnf(c_8047,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(arAF0_k2_zfmisc_1_0_1(X1)))
    | ~ iProver_ARSWP_146 ),
    inference(arg_filter_abstr,[status(unp)],[c_6])).

cnf(c_8548,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(arAF0_k2_zfmisc_1_0_1(X1))) != iProver_top
    | iProver_ARSWP_146 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8047])).

cnf(c_9627,plain,
    ( v4_relat_1(sK3,u1_struct_0(sK1)) = iProver_top
    | iProver_ARSWP_153 != iProver_top
    | iProver_ARSWP_146 != iProver_top ),
    inference(superposition,[status(thm)],[c_8541,c_8548])).

cnf(c_9977,plain,
    ( v4_relat_1(sK3,u1_struct_0(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9627,c_31,c_2130])).

cnf(c_11838,plain,
    ( v4_relat_1(sK3,k1_relat_1(sK3)) = iProver_top
    | iProver_ARSWP_154 != iProver_top
    | iProver_ARSWP_153 != iProver_top
    | iProver_ARSWP_149 != iProver_top ),
    inference(superposition,[status(thm)],[c_11697,c_9977])).

cnf(c_8,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ v4_relat_1(X0,k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_8570,plain,
    ( v1_partfun1(X0,k1_relat_1(X0)) = iProver_top
    | v4_relat_1(X0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_12201,plain,
    ( v1_partfun1(sK3,k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | iProver_ARSWP_154 != iProver_top
    | iProver_ARSWP_153 != iProver_top
    | iProver_ARSWP_149 != iProver_top ),
    inference(superposition,[status(thm)],[c_11838,c_8570])).

cnf(c_12329,plain,
    ( v1_partfun1(sK3,k1_relat_1(sK3)) = iProver_top
    | iProver_ARSWP_154 != iProver_top
    | iProver_ARSWP_153 != iProver_top
    | iProver_ARSWP_149 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12201,c_31,c_2127,c_2130,c_3431,c_4128,c_9272,c_11697])).

cnf(c_11841,plain,
    ( arAF0_v1_funct_2_0_1_2(sK3,k1_relat_1(sK3)) = iProver_top
    | iProver_ARSWP_154 != iProver_top
    | iProver_ARSWP_153 != iProver_top
    | iProver_ARSWP_149 != iProver_top ),
    inference(superposition,[status(thm)],[c_11697,c_8540])).

cnf(c_11840,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(arAF0_k2_zfmisc_1_0_1(k1_relat_1(sK3)))) = iProver_top
    | iProver_ARSWP_154 != iProver_top
    | iProver_ARSWP_153 != iProver_top
    | iProver_ARSWP_149 != iProver_top ),
    inference(superposition,[status(thm)],[c_11697,c_8541])).

cnf(c_17,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK3),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k2_relat_1(k2_funct_1(sK3)) != u1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_8053,negated_conjecture,
    ( ~ arAF0_v1_funct_2_0_1_2(arAF0_k2_funct_1_0,u1_struct_0(sK2))
    | ~ m1_subset_1(arAF0_k2_funct_1_0,k1_zfmisc_1(arAF0_k2_zfmisc_1_0_1(u1_struct_0(sK2))))
    | ~ v1_funct_1(arAF0_k2_funct_1_0)
    | ~ iProver_ARSWP_152
    | arAF0_k2_relat_1_0 != u1_struct_0(sK1) ),
    inference(arg_filter_abstr,[status(unp)],[c_17])).

cnf(c_8542,plain,
    ( arAF0_k2_relat_1_0 != u1_struct_0(sK1)
    | arAF0_v1_funct_2_0_1_2(arAF0_k2_funct_1_0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(arAF0_k2_funct_1_0,k1_zfmisc_1(arAF0_k2_zfmisc_1_0_1(u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(arAF0_k2_funct_1_0) != iProver_top
    | iProver_ARSWP_152 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8053])).

cnf(c_11839,plain,
    ( k1_relat_1(sK3) != arAF0_k2_relat_1_0
    | arAF0_v1_funct_2_0_1_2(arAF0_k2_funct_1_0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(arAF0_k2_funct_1_0,k1_zfmisc_1(arAF0_k2_zfmisc_1_0_1(u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(arAF0_k2_funct_1_0) != iProver_top
    | iProver_ARSWP_154 != iProver_top
    | iProver_ARSWP_153 != iProver_top
    | iProver_ARSWP_152 != iProver_top
    | iProver_ARSWP_149 != iProver_top ),
    inference(superposition,[status(thm)],[c_11697,c_8542])).

cnf(c_11669,plain,
    ( u1_struct_0(sK1) = X0
    | k1_relat_1(sK3) != X0
    | iProver_ARSWP_154 != iProver_top
    | iProver_ARSWP_153 != iProver_top
    | iProver_ARSWP_149 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_10848])).

cnf(c_11668,plain,
    ( u1_struct_0(sK1) != X0
    | k1_relat_1(sK3) = X0
    | iProver_ARSWP_154 != iProver_top
    | iProver_ARSWP_153 != iProver_top
    | iProver_ARSWP_149 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_10848])).

cnf(c_9635,plain,
    ( v4_relat_1(X0,k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | iProver_ARSWP_150 != iProver_top
    | iProver_ARSWP_146 != iProver_top
    | arAF0_r1_tarski_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_8544,c_8548])).

cnf(c_10585,plain,
    ( v1_partfun1(X0,k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | iProver_ARSWP_150 != iProver_top
    | iProver_ARSWP_146 != iProver_top
    | arAF0_r1_tarski_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_9635,c_8570])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_8043,plain,
    ( ~ iProver_ARSWP_142
    | arAF0_r1_tarski_0
    | arAF0_r2_hidden_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_1])).

cnf(c_8552,plain,
    ( iProver_ARSWP_142 != iProver_top
    | arAF0_r1_tarski_0 = iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8043])).

cnf(c_8046,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(arAF0_k2_zfmisc_1_0_1(X1)))
    | v1_relat_1(X0)
    | ~ iProver_ARSWP_145 ),
    inference(arg_filter_abstr,[status(unp)],[c_5])).

cnf(c_8549,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(arAF0_k2_zfmisc_1_0_1(X1))) != iProver_top
    | v1_relat_1(X0) = iProver_top
    | iProver_ARSWP_145 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8046])).

cnf(c_9525,plain,
    ( v1_relat_1(sK3) = iProver_top
    | iProver_ARSWP_153 != iProver_top
    | iProver_ARSWP_145 != iProver_top ),
    inference(superposition,[status(thm)],[c_8541,c_8549])).

cnf(c_9528,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9525,c_31,c_2127])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_8048,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(arAF0_k2_zfmisc_1_0_1(X1)))
    | ~ iProver_ARSWP_147
    | arAF0_k2_relset_1_0 = arAF0_k2_relat_1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_7])).

cnf(c_8547,plain,
    ( arAF0_k2_relset_1_0 = arAF0_k2_relat_1_0
    | m1_subset_1(X0,k1_zfmisc_1(arAF0_k2_zfmisc_1_0_1(X1))) != iProver_top
    | iProver_ARSWP_147 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8048])).

cnf(c_9637,plain,
    ( arAF0_k2_relat_1_0 = arAF0_k2_relset_1_0
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | iProver_ARSWP_150 != iProver_top
    | iProver_ARSWP_147 != iProver_top
    | arAF0_r1_tarski_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_8544,c_8547])).

cnf(c_9989,plain,
    ( arAF0_k2_relat_1_0 = arAF0_k2_relset_1_0
    | v1_funct_1(sK3) != iProver_top
    | iProver_ARSWP_150 != iProver_top
    | iProver_ARSWP_147 != iProver_top
    | arAF0_r1_tarski_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_9528,c_9637])).

cnf(c_10154,plain,
    ( arAF0_k2_relat_1_0 = arAF0_k2_relset_1_0
    | iProver_ARSWP_150 != iProver_top
    | iProver_ARSWP_147 != iProver_top
    | arAF0_r1_tarski_0 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9989,c_29])).

cnf(c_10162,plain,
    ( arAF0_k2_relat_1_0 = arAF0_k2_relset_1_0
    | iProver_ARSWP_150 != iProver_top
    | iProver_ARSWP_147 != iProver_top
    | iProver_ARSWP_142 != iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_8552,c_10154])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_8042,plain,
    ( ~ iProver_ARSWP_141
    | arAF0_r1_tarski_0
    | ~ arAF0_r2_hidden_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_0])).

cnf(c_8553,plain,
    ( iProver_ARSWP_141 != iProver_top
    | arAF0_r1_tarski_0 = iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8042])).

cnf(c_10170,plain,
    ( arAF0_k2_relat_1_0 = arAF0_k2_relset_1_0
    | iProver_ARSWP_150 != iProver_top
    | iProver_ARSWP_147 != iProver_top
    | iProver_ARSWP_142 != iProver_top
    | iProver_ARSWP_141 != iProver_top
    | arAF0_r1_tarski_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_10162,c_8553])).

cnf(c_8080,plain,
    ( iProver_ARSWP_141 != iProver_top
    | arAF0_r1_tarski_0 = iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8042])).

cnf(c_8081,plain,
    ( iProver_ARSWP_142 != iProver_top
    | arAF0_r1_tarski_0 = iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8043])).

cnf(c_10267,plain,
    ( iProver_ARSWP_142 != iProver_top
    | iProver_ARSWP_141 != iProver_top
    | arAF0_r1_tarski_0 = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10170,c_8080,c_8081])).

cnf(c_10274,plain,
    ( arAF0_k2_relat_1_0 = arAF0_k2_relset_1_0
    | iProver_ARSWP_150 != iProver_top
    | iProver_ARSWP_147 != iProver_top
    | iProver_ARSWP_142 != iProver_top
    | iProver_ARSWP_141 != iProver_top ),
    inference(superposition,[status(thm)],[c_10267,c_10154])).

cnf(c_9429,plain,
    ( arAF0_k2_relat_1_0 = arAF0_k2_relset_1_0
    | iProver_ARSWP_153 != iProver_top
    | iProver_ARSWP_147 != iProver_top ),
    inference(superposition,[status(thm)],[c_8541,c_8547])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_8045,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(arAF0_k2_funct_1_0)
    | ~ v1_funct_1(X0)
    | ~ iProver_ARSWP_144 ),
    inference(arg_filter_abstr,[status(unp)],[c_4])).

cnf(c_8550,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(arAF0_k2_funct_1_0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | iProver_ARSWP_144 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8045])).

cnf(c_8893,plain,
    ( v1_relat_1(arAF0_k2_funct_1_0)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ iProver_ARSWP_144 ),
    inference(instantiation,[status(thm)],[c_8045])).

cnf(c_9194,plain,
    ( v1_relat_1(arAF0_k2_funct_1_0)
    | ~ iProver_ARSWP_144 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8045,c_20,c_18,c_2126,c_8893])).

cnf(c_9196,plain,
    ( v1_relat_1(arAF0_k2_funct_1_0) = iProver_top
    | iProver_ARSWP_144 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9194])).

cnf(c_9852,plain,
    ( v1_relat_1(arAF0_k2_funct_1_0) = iProver_top
    | iProver_ARSWP_144 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8550,c_9196])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_8044,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(arAF0_k2_funct_1_0)
    | ~ iProver_ARSWP_143 ),
    inference(arg_filter_abstr,[status(unp)],[c_3])).

cnf(c_8551,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(arAF0_k2_funct_1_0) = iProver_top
    | iProver_ARSWP_143 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8044])).

cnf(c_8894,plain,
    ( ~ v1_relat_1(sK3)
    | v1_funct_1(arAF0_k2_funct_1_0)
    | ~ v1_funct_1(sK3)
    | ~ iProver_ARSWP_143 ),
    inference(instantiation,[status(thm)],[c_8044])).

cnf(c_9116,plain,
    ( v1_funct_1(arAF0_k2_funct_1_0)
    | ~ iProver_ARSWP_143 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8044,c_20,c_18,c_2126,c_8894])).

cnf(c_9118,plain,
    ( v1_funct_1(arAF0_k2_funct_1_0) = iProver_top
    | iProver_ARSWP_143 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9116])).

cnf(c_9859,plain,
    ( v1_funct_1(arAF0_k2_funct_1_0) = iProver_top
    | iProver_ARSWP_143 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8551,c_9118])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | v1_partfun1(X0,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_8049,plain,
    ( ~ arAF0_v1_funct_2_0_1_2(X0,k1_xboole_0)
    | v1_partfun1(X0,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(arAF0_k2_zfmisc_1_0_1(k1_xboole_0)))
    | ~ v1_funct_1(X0)
    | ~ iProver_ARSWP_148 ),
    inference(arg_filter_abstr,[status(unp)],[c_10])).

cnf(c_8546,plain,
    ( arAF0_v1_funct_2_0_1_2(X0,k1_xboole_0) != iProver_top
    | v1_partfun1(X0,k1_xboole_0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(arAF0_k2_zfmisc_1_0_1(k1_xboole_0))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | iProver_ARSWP_148 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8049])).

cnf(c_21,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_8565,plain,
    ( l1_orders_2(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_8567,plain,
    ( l1_orders_2(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_9094,plain,
    ( l1_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_8565,c_8567])).

cnf(c_8563,plain,
    ( l1_orders_2(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_9095,plain,
    ( l1_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_8563,c_8567])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_8571,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_8566,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_8564,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_8562,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:22:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.74/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.74/0.99  
% 3.74/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.74/0.99  
% 3.74/0.99  ------  iProver source info
% 3.74/0.99  
% 3.74/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.74/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.74/0.99  git: non_committed_changes: false
% 3.74/0.99  git: last_make_outside_of_git: false
% 3.74/0.99  
% 3.74/0.99  ------ 
% 3.74/0.99  ------ Parsing...
% 3.74/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.74/0.99  
% 3.74/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.74/0.99  
% 3.74/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.74/0.99  
% 3.74/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.74/0.99  ------ Proving...
% 3.74/0.99  ------ Problem Properties 
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  clauses                                 24
% 3.74/0.99  conjectures                             8
% 3.74/0.99  EPR                                     7
% 3.74/0.99  Horn                                    22
% 3.74/0.99  unary                                   8
% 3.74/0.99  binary                                  6
% 3.74/0.99  lits                                    57
% 3.74/0.99  lits eq                                 4
% 3.74/0.99  fd_pure                                 0
% 3.74/0.99  fd_pseudo                               0
% 3.74/0.99  fd_cond                                 1
% 3.74/0.99  fd_pseudo_cond                          1
% 3.74/0.99  AC symbols                              0
% 3.74/0.99  
% 3.74/0.99  ------ Input Options Time Limit: Unbounded
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  ------ Preprocessing...
% 3.74/0.99  
% 3.74/0.99  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.74/0.99  Current options:
% 3.74/0.99  ------ 
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  ------ Proving...
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.74/0.99  
% 3.74/0.99  ------ Proving...
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.74/0.99  
% 3.74/0.99  ------ Proving...
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.74/0.99  
% 3.74/0.99  ------ Proving...
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.74/0.99  
% 3.74/0.99  ------ Proving...
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.74/0.99  
% 3.74/0.99  ------ Proving...
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.74/0.99  
% 3.74/0.99  ------ Proving...
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.74/0.99  
% 3.74/0.99  ------ Proving...
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.74/0.99  
% 3.74/0.99  ------ Proving...
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.74/0.99  
% 3.74/0.99  ------ Proving...
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.74/0.99  
% 3.74/0.99  ------ Proving...
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.74/0.99  
% 3.74/0.99  ------ Proving...
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.74/0.99  
% 3.74/0.99  ------ Proving...
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  % SZS status CounterSatisfiable for theBenchmark.p
% 3.74/0.99  
% 3.74/0.99  % SZS output start Saturation for theBenchmark.p
% 3.74/0.99  
% 3.74/0.99  fof(f10,axiom,(
% 3.74/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 3.74/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f29,plain,(
% 3.74/0.99    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.74/0.99    inference(ennf_transformation,[],[f10])).
% 3.74/0.99  
% 3.74/0.99  fof(f30,plain,(
% 3.74/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.74/0.99    inference(flattening,[],[f29])).
% 3.74/0.99  
% 3.74/0.99  fof(f56,plain,(
% 3.74/0.99    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.74/0.99    inference(cnf_transformation,[],[f30])).
% 3.74/0.99  
% 3.74/0.99  fof(f57,plain,(
% 3.74/0.99    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.74/0.99    inference(cnf_transformation,[],[f30])).
% 3.74/0.99  
% 3.74/0.99  fof(f9,axiom,(
% 3.74/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.74/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f27,plain,(
% 3.74/0.99    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.74/0.99    inference(ennf_transformation,[],[f9])).
% 3.74/0.99  
% 3.74/0.99  fof(f28,plain,(
% 3.74/0.99    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.74/0.99    inference(flattening,[],[f27])).
% 3.74/0.99  
% 3.74/0.99  fof(f53,plain,(
% 3.74/0.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.74/0.99    inference(cnf_transformation,[],[f28])).
% 3.74/0.99  
% 3.74/0.99  fof(f13,conjecture,(
% 3.74/0.99    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v23_waybel_0(X2,X0,X1) => (k2_relat_1(k2_funct_1(X2)) = u1_struct_0(X0) & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_funct_1(X2)))))))),
% 3.74/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f14,negated_conjecture,(
% 3.74/0.99    ~! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v23_waybel_0(X2,X0,X1) => (k2_relat_1(k2_funct_1(X2)) = u1_struct_0(X0) & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_funct_1(X2)))))))),
% 3.74/0.99    inference(negated_conjecture,[],[f13])).
% 3.74/0.99  
% 3.74/0.99  fof(f16,plain,(
% 3.74/0.99    ~! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (k2_relat_1(k2_funct_1(X2)) = u1_struct_0(X0) & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_funct_1(X2))))))),
% 3.74/0.99    inference(pure_predicate_removal,[],[f14])).
% 3.74/0.99  
% 3.74/0.99  fof(f34,plain,(
% 3.74/0.99    ? [X0] : (? [X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_orders_2(X1) & ~v2_struct_0(X1))) & (l1_orders_2(X0) & ~v2_struct_0(X0)))),
% 3.74/0.99    inference(ennf_transformation,[],[f16])).
% 3.74/0.99  
% 3.74/0.99  fof(f35,plain,(
% 3.74/0.99    ? [X0] : (? [X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_orders_2(X1) & ~v2_struct_0(X1)) & l1_orders_2(X0) & ~v2_struct_0(X0))),
% 3.74/0.99    inference(flattening,[],[f34])).
% 3.74/0.99  
% 3.74/0.99  fof(f41,plain,(
% 3.74/0.99    ( ! [X0,X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_relat_1(k2_funct_1(sK3)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(sK3),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(sK3))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK3))) )),
% 3.74/0.99    introduced(choice_axiom,[])).
% 3.74/0.99  
% 3.74/0.99  fof(f40,plain,(
% 3.74/0.99    ( ! [X0] : (? [X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_orders_2(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK2)) & v1_funct_1(X2)) & l1_orders_2(sK2) & ~v2_struct_0(sK2))) )),
% 3.74/0.99    introduced(choice_axiom,[])).
% 3.74/0.99  
% 3.74/0.99  fof(f39,plain,(
% 3.74/0.99    ? [X0] : (? [X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_orders_2(X1) & ~v2_struct_0(X1)) & l1_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(sK1) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(sK1)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_orders_2(X1) & ~v2_struct_0(X1)) & l1_orders_2(sK1) & ~v2_struct_0(sK1))),
% 3.74/0.99    introduced(choice_axiom,[])).
% 3.74/0.99  
% 3.74/0.99  fof(f42,plain,(
% 3.74/0.99    (((k2_relat_1(k2_funct_1(sK3)) != u1_struct_0(sK1) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(k2_funct_1(sK3),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k2_funct_1(sK3))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK3)) & l1_orders_2(sK2) & ~v2_struct_0(sK2)) & l1_orders_2(sK1) & ~v2_struct_0(sK1)),
% 3.74/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f35,f41,f40,f39])).
% 3.74/0.99  
% 3.74/0.99  fof(f65,plain,(
% 3.74/0.99    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))),
% 3.74/0.99    inference(cnf_transformation,[],[f42])).
% 3.74/0.99  
% 3.74/0.99  fof(f66,plain,(
% 3.74/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))),
% 3.74/0.99    inference(cnf_transformation,[],[f42])).
% 3.74/0.99  
% 3.74/0.99  fof(f64,plain,(
% 3.74/0.99    v1_funct_1(sK3)),
% 3.74/0.99    inference(cnf_transformation,[],[f42])).
% 3.74/0.99  
% 3.74/0.99  fof(f8,axiom,(
% 3.74/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 3.74/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f25,plain,(
% 3.74/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.74/0.99    inference(ennf_transformation,[],[f8])).
% 3.74/0.99  
% 3.74/0.99  fof(f26,plain,(
% 3.74/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.74/0.99    inference(flattening,[],[f25])).
% 3.74/0.99  
% 3.74/0.99  fof(f38,plain,(
% 3.74/0.99    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.74/0.99    inference(nnf_transformation,[],[f26])).
% 3.74/0.99  
% 3.74/0.99  fof(f51,plain,(
% 3.74/0.99    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.74/0.99    inference(cnf_transformation,[],[f38])).
% 3.74/0.99  
% 3.74/0.99  fof(f5,axiom,(
% 3.74/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.74/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f22,plain,(
% 3.74/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.74/0.99    inference(ennf_transformation,[],[f5])).
% 3.74/0.99  
% 3.74/0.99  fof(f48,plain,(
% 3.74/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.74/0.99    inference(cnf_transformation,[],[f22])).
% 3.74/0.99  
% 3.74/0.99  fof(f6,axiom,(
% 3.74/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.74/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f17,plain,(
% 3.74/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.74/0.99    inference(pure_predicate_removal,[],[f6])).
% 3.74/0.99  
% 3.74/0.99  fof(f23,plain,(
% 3.74/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.74/0.99    inference(ennf_transformation,[],[f17])).
% 3.74/0.99  
% 3.74/0.99  fof(f49,plain,(
% 3.74/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.74/0.99    inference(cnf_transformation,[],[f23])).
% 3.74/0.99  
% 3.74/0.99  fof(f11,axiom,(
% 3.74/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.74/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f31,plain,(
% 3.74/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.74/0.99    inference(ennf_transformation,[],[f11])).
% 3.74/0.99  
% 3.74/0.99  fof(f32,plain,(
% 3.74/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.74/0.99    inference(flattening,[],[f31])).
% 3.74/0.99  
% 3.74/0.99  fof(f58,plain,(
% 3.74/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.74/0.99    inference(cnf_transformation,[],[f32])).
% 3.74/0.99  
% 3.74/0.99  fof(f60,plain,(
% 3.74/0.99    ~v2_struct_0(sK1)),
% 3.74/0.99    inference(cnf_transformation,[],[f42])).
% 3.74/0.99  
% 3.74/0.99  fof(f61,plain,(
% 3.74/0.99    l1_orders_2(sK1)),
% 3.74/0.99    inference(cnf_transformation,[],[f42])).
% 3.74/0.99  
% 3.74/0.99  fof(f12,axiom,(
% 3.74/0.99    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 3.74/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f33,plain,(
% 3.74/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 3.74/0.99    inference(ennf_transformation,[],[f12])).
% 3.74/0.99  
% 3.74/0.99  fof(f59,plain,(
% 3.74/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 3.74/0.99    inference(cnf_transformation,[],[f33])).
% 3.74/0.99  
% 3.74/0.99  fof(f52,plain,(
% 3.74/0.99    ( ! [X0,X1] : (v1_partfun1(X1,X0) | k1_relat_1(X1) != X0 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.74/0.99    inference(cnf_transformation,[],[f38])).
% 3.74/0.99  
% 3.74/0.99  fof(f68,plain,(
% 3.74/0.99    ( ! [X1] : (v1_partfun1(X1,k1_relat_1(X1)) | ~v4_relat_1(X1,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.74/0.99    inference(equality_resolution,[],[f52])).
% 3.74/0.99  
% 3.74/0.99  fof(f67,plain,(
% 3.74/0.99    k2_relat_1(k2_funct_1(sK3)) != u1_struct_0(sK1) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(k2_funct_1(sK3),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k2_funct_1(sK3))),
% 3.74/0.99    inference(cnf_transformation,[],[f42])).
% 3.74/0.99  
% 3.74/0.99  fof(f1,axiom,(
% 3.74/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.74/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f15,plain,(
% 3.74/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 3.74/0.99    inference(unused_predicate_definition_removal,[],[f1])).
% 3.74/0.99  
% 3.74/0.99  fof(f19,plain,(
% 3.74/0.99    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 3.74/0.99    inference(ennf_transformation,[],[f15])).
% 3.74/0.99  
% 3.74/0.99  fof(f36,plain,(
% 3.74/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.74/0.99    introduced(choice_axiom,[])).
% 3.74/0.99  
% 3.74/0.99  fof(f37,plain,(
% 3.74/0.99    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.74/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f36])).
% 3.74/0.99  
% 3.74/0.99  fof(f43,plain,(
% 3.74/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.74/0.99    inference(cnf_transformation,[],[f37])).
% 3.74/0.99  
% 3.74/0.99  fof(f7,axiom,(
% 3.74/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.74/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f24,plain,(
% 3.74/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.74/0.99    inference(ennf_transformation,[],[f7])).
% 3.74/0.99  
% 3.74/0.99  fof(f50,plain,(
% 3.74/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.74/0.99    inference(cnf_transformation,[],[f24])).
% 3.74/0.99  
% 3.74/0.99  fof(f44,plain,(
% 3.74/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.74/0.99    inference(cnf_transformation,[],[f37])).
% 3.74/0.99  
% 3.74/0.99  fof(f3,axiom,(
% 3.74/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.74/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f20,plain,(
% 3.74/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.74/0.99    inference(ennf_transformation,[],[f3])).
% 3.74/0.99  
% 3.74/0.99  fof(f21,plain,(
% 3.74/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.74/0.99    inference(flattening,[],[f20])).
% 3.74/0.99  
% 3.74/0.99  fof(f46,plain,(
% 3.74/0.99    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.74/0.99    inference(cnf_transformation,[],[f21])).
% 3.74/0.99  
% 3.74/0.99  fof(f47,plain,(
% 3.74/0.99    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.74/0.99    inference(cnf_transformation,[],[f21])).
% 3.74/0.99  
% 3.74/0.99  fof(f54,plain,(
% 3.74/0.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.74/0.99    inference(cnf_transformation,[],[f28])).
% 3.74/0.99  
% 3.74/0.99  fof(f69,plain,(
% 3.74/0.99    ( ! [X2,X1] : (v1_partfun1(X2,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X2)) )),
% 3.74/0.99    inference(equality_resolution,[],[f54])).
% 3.74/0.99  
% 3.74/0.99  fof(f63,plain,(
% 3.74/0.99    l1_orders_2(sK2)),
% 3.74/0.99    inference(cnf_transformation,[],[f42])).
% 3.74/0.99  
% 3.74/0.99  fof(f2,axiom,(
% 3.74/0.99    v1_xboole_0(k1_xboole_0)),
% 3.74/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f45,plain,(
% 3.74/0.99    v1_xboole_0(k1_xboole_0)),
% 3.74/0.99    inference(cnf_transformation,[],[f2])).
% 3.74/0.99  
% 3.74/0.99  fof(f62,plain,(
% 3.74/0.99    ~v2_struct_0(sK2)),
% 3.74/0.99    inference(cnf_transformation,[],[f42])).
% 3.74/0.99  
% 3.74/0.99  cnf(c_208,plain,( X0_2 = X0_2 ),theory(equality) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_13,plain,
% 3.74/0.99      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.74/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.74/0.99      | ~ v1_relat_1(X0)
% 3.74/0.99      | ~ v1_funct_1(X0) ),
% 3.74/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_8052,plain,
% 3.74/0.99      ( arAF0_v1_funct_2_0_1_2(X0,k1_relat_1(X0))
% 3.74/0.99      | ~ v1_relat_1(X0)
% 3.74/0.99      | ~ v1_funct_1(X0)
% 3.74/0.99      | ~ iProver_ARSWP_151
% 3.74/0.99      | ~ arAF0_r1_tarski_0 ),
% 3.74/0.99      inference(arg_filter_abstr,[status(unp)],[c_13]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_8543,plain,
% 3.74/0.99      ( arAF0_v1_funct_2_0_1_2(X0,k1_relat_1(X0)) = iProver_top
% 3.74/0.99      | v1_relat_1(X0) != iProver_top
% 3.74/0.99      | v1_funct_1(X0) != iProver_top
% 3.74/0.99      | iProver_ARSWP_151 != iProver_top
% 3.74/0.99      | arAF0_r1_tarski_0 != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_8052]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_12,plain,
% 3.74/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.74/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.74/0.99      | ~ v1_relat_1(X0)
% 3.74/0.99      | ~ v1_funct_1(X0) ),
% 3.74/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_8051,plain,
% 3.74/0.99      ( m1_subset_1(X0,k1_zfmisc_1(arAF0_k2_zfmisc_1_0_1(k1_relat_1(X0))))
% 3.74/0.99      | ~ v1_relat_1(X0)
% 3.74/0.99      | ~ v1_funct_1(X0)
% 3.74/0.99      | ~ iProver_ARSWP_150
% 3.74/0.99      | ~ arAF0_r1_tarski_0 ),
% 3.74/0.99      inference(arg_filter_abstr,[status(unp)],[c_12]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_8544,plain,
% 3.74/0.99      ( m1_subset_1(X0,k1_zfmisc_1(arAF0_k2_zfmisc_1_0_1(k1_relat_1(X0)))) = iProver_top
% 3.74/0.99      | v1_relat_1(X0) != iProver_top
% 3.74/0.99      | v1_funct_1(X0) != iProver_top
% 3.74/0.99      | iProver_ARSWP_150 != iProver_top
% 3.74/0.99      | arAF0_r1_tarski_0 != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_8051]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_11,plain,
% 3.74/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.74/0.99      | v1_partfun1(X0,X1)
% 3.74/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.74/0.99      | ~ v1_funct_1(X0)
% 3.74/0.99      | k1_xboole_0 = X2 ),
% 3.74/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_8050,plain,
% 3.74/0.99      ( ~ arAF0_v1_funct_2_0_1_2(X0,X1)
% 3.74/0.99      | v1_partfun1(X0,X1)
% 3.74/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(arAF0_k2_zfmisc_1_0_1(X1)))
% 3.74/0.99      | ~ v1_funct_1(X0)
% 3.74/0.99      | ~ iProver_ARSWP_149
% 3.74/0.99      | k1_xboole_0 = X2 ),
% 3.74/0.99      inference(arg_filter_abstr,[status(unp)],[c_11]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_8545,plain,
% 3.74/0.99      ( k1_xboole_0 = X0
% 3.74/0.99      | arAF0_v1_funct_2_0_1_2(X1,X2) != iProver_top
% 3.74/0.99      | v1_partfun1(X1,X2) = iProver_top
% 3.74/0.99      | m1_subset_1(X1,k1_zfmisc_1(arAF0_k2_zfmisc_1_0_1(X2))) != iProver_top
% 3.74/0.99      | v1_funct_1(X1) != iProver_top
% 3.74/0.99      | iProver_ARSWP_149 != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_8050]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_10420,plain,
% 3.74/0.99      ( k1_xboole_0 = X0
% 3.74/0.99      | arAF0_v1_funct_2_0_1_2(X1,k1_relat_1(X1)) != iProver_top
% 3.74/0.99      | v1_partfun1(X1,k1_relat_1(X1)) = iProver_top
% 3.74/0.99      | v1_relat_1(X1) != iProver_top
% 3.74/0.99      | v1_funct_1(X1) != iProver_top
% 3.74/0.99      | iProver_ARSWP_150 != iProver_top
% 3.74/0.99      | iProver_ARSWP_149 != iProver_top
% 3.74/0.99      | arAF0_r1_tarski_0 != iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_8544,c_8545]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_12505,plain,
% 3.74/0.99      ( k1_xboole_0 = X0
% 3.74/0.99      | v1_partfun1(X1,k1_relat_1(X1)) = iProver_top
% 3.74/0.99      | v1_relat_1(X1) != iProver_top
% 3.74/0.99      | v1_funct_1(X1) != iProver_top
% 3.74/0.99      | iProver_ARSWP_151 != iProver_top
% 3.74/0.99      | iProver_ARSWP_150 != iProver_top
% 3.74/0.99      | iProver_ARSWP_149 != iProver_top
% 3.74/0.99      | arAF0_r1_tarski_0 != iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_8543,c_10420]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_19,negated_conjecture,
% 3.74/0.99      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 3.74/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_8055,negated_conjecture,
% 3.74/0.99      ( arAF0_v1_funct_2_0_1_2(sK3,u1_struct_0(sK1)) | ~ iProver_ARSWP_154 ),
% 3.74/0.99      inference(arg_filter_abstr,[status(unp)],[c_19]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_8540,plain,
% 3.74/0.99      ( arAF0_v1_funct_2_0_1_2(sK3,u1_struct_0(sK1)) = iProver_top
% 3.74/0.99      | iProver_ARSWP_154 != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_8055]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_18,negated_conjecture,
% 3.74/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
% 3.74/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_8054,negated_conjecture,
% 3.74/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(arAF0_k2_zfmisc_1_0_1(u1_struct_0(sK1))))
% 3.74/0.99      | ~ iProver_ARSWP_153 ),
% 3.74/0.99      inference(arg_filter_abstr,[status(unp)],[c_18]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_8541,plain,
% 3.74/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(arAF0_k2_zfmisc_1_0_1(u1_struct_0(sK1)))) = iProver_top
% 3.74/0.99      | iProver_ARSWP_153 != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_8054]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_10419,plain,
% 3.74/0.99      ( k1_xboole_0 = X0
% 3.74/0.99      | arAF0_v1_funct_2_0_1_2(sK3,u1_struct_0(sK1)) != iProver_top
% 3.74/0.99      | v1_partfun1(sK3,u1_struct_0(sK1)) = iProver_top
% 3.74/0.99      | v1_funct_1(sK3) != iProver_top
% 3.74/0.99      | iProver_ARSWP_153 != iProver_top
% 3.74/0.99      | iProver_ARSWP_149 != iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_8541,c_8545]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_20,negated_conjecture,
% 3.74/0.99      ( v1_funct_1(sK3) ),
% 3.74/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_29,plain,
% 3.74/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_10719,plain,
% 3.74/0.99      ( v1_partfun1(sK3,u1_struct_0(sK1)) = iProver_top
% 3.74/0.99      | arAF0_v1_funct_2_0_1_2(sK3,u1_struct_0(sK1)) != iProver_top
% 3.74/0.99      | k1_xboole_0 = X0
% 3.74/0.99      | iProver_ARSWP_153 != iProver_top
% 3.74/0.99      | iProver_ARSWP_149 != iProver_top ),
% 3.74/0.99      inference(global_propositional_subsumption,[status(thm)],[c_10419,c_29]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_10720,plain,
% 3.74/0.99      ( k1_xboole_0 = X0
% 3.74/0.99      | arAF0_v1_funct_2_0_1_2(sK3,u1_struct_0(sK1)) != iProver_top
% 3.74/0.99      | v1_partfun1(sK3,u1_struct_0(sK1)) = iProver_top
% 3.74/0.99      | iProver_ARSWP_153 != iProver_top
% 3.74/0.99      | iProver_ARSWP_149 != iProver_top ),
% 3.74/0.99      inference(renaming,[status(thm)],[c_10719]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_10730,plain,
% 3.74/0.99      ( k1_xboole_0 = X0
% 3.74/0.99      | v1_partfun1(sK3,u1_struct_0(sK1)) = iProver_top
% 3.74/0.99      | iProver_ARSWP_154 != iProver_top
% 3.74/0.99      | iProver_ARSWP_153 != iProver_top
% 3.74/0.99      | iProver_ARSWP_149 != iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_8540,c_10720]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_9,plain,
% 3.74/0.99      ( ~ v1_partfun1(X0,X1)
% 3.74/0.99      | ~ v4_relat_1(X0,X1)
% 3.74/0.99      | ~ v1_relat_1(X0)
% 3.74/0.99      | k1_relat_1(X0) = X1 ),
% 3.74/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_8569,plain,
% 3.74/0.99      ( k1_relat_1(X0) = X1
% 3.74/0.99      | v1_partfun1(X0,X1) != iProver_top
% 3.74/0.99      | v4_relat_1(X0,X1) != iProver_top
% 3.74/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_10740,plain,
% 3.74/0.99      ( u1_struct_0(sK1) = k1_relat_1(sK3)
% 3.74/0.99      | k1_xboole_0 = X0
% 3.74/0.99      | v4_relat_1(sK3,u1_struct_0(sK1)) != iProver_top
% 3.74/0.99      | v1_relat_1(sK3) != iProver_top
% 3.74/0.99      | iProver_ARSWP_154 != iProver_top
% 3.74/0.99      | iProver_ARSWP_153 != iProver_top
% 3.74/0.99      | iProver_ARSWP_149 != iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_10730,c_8569]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_31,plain,
% 3.74/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_5,plain,
% 3.74/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.74/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_2126,plain,
% 3.74/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 3.74/0.99      | v1_relat_1(sK3) ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_2127,plain,
% 3.74/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 3.74/0.99      | v1_relat_1(sK3) = iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_2126]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_6,plain,
% 3.74/0.99      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.74/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_2129,plain,
% 3.74/0.99      ( v4_relat_1(sK3,u1_struct_0(sK1))
% 3.74/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_2130,plain,
% 3.74/0.99      ( v4_relat_1(sK3,u1_struct_0(sK1)) = iProver_top
% 3.74/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_2129]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_350,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_3186,plain,
% 3.74/0.99      ( X0 != X1 | u1_struct_0(X2) != X1 | u1_struct_0(X2) = X0 ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_350]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_3202,plain,
% 3.74/0.99      ( X0 != u1_struct_0(X1)
% 3.74/0.99      | u1_struct_0(X1) = X0
% 3.74/0.99      | u1_struct_0(X1) != u1_struct_0(X1) ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_3186]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_3203,plain,
% 3.74/0.99      ( X0 != u1_struct_0(X1) | u1_struct_0(X1) = X0 ),
% 3.74/0.99      inference(equality_resolution_simp,[status(thm)],[c_3202]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_3336,plain,
% 3.74/0.99      ( u1_struct_0(X0) = k1_relat_1(sK3)
% 3.74/0.99      | k1_relat_1(sK3) != u1_struct_0(X0) ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_3203]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_3339,plain,
% 3.74/0.99      ( u1_struct_0(sK1) = k1_relat_1(sK3)
% 3.74/0.99      | k1_relat_1(sK3) != u1_struct_0(sK1) ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_3336]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_4969,plain,
% 3.74/0.99      ( ~ v1_partfun1(sK3,X0)
% 3.74/0.99      | ~ v4_relat_1(sK3,X0)
% 3.74/0.99      | ~ v1_relat_1(sK3)
% 3.74/0.99      | k1_relat_1(sK3) = X0 ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_5293,plain,
% 3.74/0.99      ( ~ v1_partfun1(sK3,u1_struct_0(X0))
% 3.74/0.99      | ~ v4_relat_1(sK3,u1_struct_0(X0))
% 3.74/0.99      | ~ v1_relat_1(sK3)
% 3.74/0.99      | k1_relat_1(sK3) = u1_struct_0(X0) ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_4969]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_5294,plain,
% 3.74/0.99      ( k1_relat_1(sK3) = u1_struct_0(X0)
% 3.74/0.99      | v1_partfun1(sK3,u1_struct_0(X0)) != iProver_top
% 3.74/0.99      | v4_relat_1(sK3,u1_struct_0(X0)) != iProver_top
% 3.74/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_5293]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_5296,plain,
% 3.74/0.99      ( k1_relat_1(sK3) = u1_struct_0(sK1)
% 3.74/0.99      | v1_partfun1(sK3,u1_struct_0(sK1)) != iProver_top
% 3.74/0.99      | v4_relat_1(sK3,u1_struct_0(sK1)) != iProver_top
% 3.74/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_5294]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_10834,plain,
% 3.74/0.99      ( u1_struct_0(sK1) = k1_relat_1(sK3)
% 3.74/0.99      | k1_xboole_0 = X0
% 3.74/0.99      | iProver_ARSWP_154 != iProver_top
% 3.74/0.99      | iProver_ARSWP_153 != iProver_top
% 3.74/0.99      | iProver_ARSWP_149 != iProver_top ),
% 3.74/0.99      inference(global_propositional_subsumption,
% 3.74/0.99                [status(thm)],
% 3.74/0.99                [c_10740,c_29,c_31,c_2127,c_2130,c_3339,c_5296,c_8111,c_10419]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_10848,plain,
% 3.74/0.99      ( X0 = X1
% 3.74/0.99      | u1_struct_0(sK1) = k1_relat_1(sK3)
% 3.74/0.99      | iProver_ARSWP_154 != iProver_top
% 3.74/0.99      | iProver_ARSWP_153 != iProver_top
% 3.74/0.99      | iProver_ARSWP_149 != iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_10834,c_10834]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_11667,plain,
% 3.74/0.99      ( u1_struct_0(sK1) = k1_relat_1(sK3)
% 3.74/0.99      | k1_relat_1(sK3) != X0
% 3.74/0.99      | iProver_ARSWP_154 != iProver_top
% 3.74/0.99      | iProver_ARSWP_153 != iProver_top
% 3.74/0.99      | iProver_ARSWP_149 != iProver_top ),
% 3.74/0.99      inference(equality_factoring,[status(thm)],[c_10848]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_11697,plain,
% 3.74/0.99      ( u1_struct_0(sK1) = k1_relat_1(sK3)
% 3.74/0.99      | iProver_ARSWP_154 != iProver_top
% 3.74/0.99      | iProver_ARSWP_153 != iProver_top
% 3.74/0.99      | iProver_ARSWP_149 != iProver_top ),
% 3.74/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_11667,c_10848]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_15,plain,
% 3.74/0.99      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.74/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_8568,plain,
% 3.74/0.99      ( v2_struct_0(X0) = iProver_top
% 3.74/0.99      | l1_struct_0(X0) != iProver_top
% 3.74/0.99      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_11835,plain,
% 3.74/0.99      ( v2_struct_0(sK1) = iProver_top
% 3.74/0.99      | l1_struct_0(sK1) != iProver_top
% 3.74/0.99      | v1_xboole_0(k1_relat_1(sK3)) != iProver_top
% 3.74/0.99      | iProver_ARSWP_154 != iProver_top
% 3.74/0.99      | iProver_ARSWP_153 != iProver_top
% 3.74/0.99      | iProver_ARSWP_149 != iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_11697,c_8568]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_24,negated_conjecture,
% 3.74/0.99      ( ~ v2_struct_0(sK1) ),
% 3.74/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_25,plain,
% 3.74/0.99      ( v2_struct_0(sK1) != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_23,negated_conjecture,
% 3.74/0.99      ( l1_orders_2(sK1) ),
% 3.74/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_26,plain,
% 3.74/0.99      ( l1_orders_2(sK1) = iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_16,plain,
% 3.74/0.99      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 3.74/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_33,plain,
% 3.74/0.99      ( l1_orders_2(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_35,plain,
% 3.74/0.99      ( l1_orders_2(sK1) != iProver_top | l1_struct_0(sK1) = iProver_top ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_33]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_12340,plain,
% 3.74/0.99      ( v1_xboole_0(k1_relat_1(sK3)) != iProver_top
% 3.74/0.99      | iProver_ARSWP_154 != iProver_top
% 3.74/0.99      | iProver_ARSWP_153 != iProver_top
% 3.74/0.99      | iProver_ARSWP_149 != iProver_top ),
% 3.74/0.99      inference(global_propositional_subsumption,
% 3.74/0.99                [status(thm)],
% 3.74/0.99                [c_11835,c_25,c_26,c_35,c_38,c_3343,c_11697]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_8047,plain,
% 3.74/0.99      ( v4_relat_1(X0,X1)
% 3.74/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(arAF0_k2_zfmisc_1_0_1(X1)))
% 3.74/0.99      | ~ iProver_ARSWP_146 ),
% 3.74/0.99      inference(arg_filter_abstr,[status(unp)],[c_6]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_8548,plain,
% 3.74/0.99      ( v4_relat_1(X0,X1) = iProver_top
% 3.74/0.99      | m1_subset_1(X0,k1_zfmisc_1(arAF0_k2_zfmisc_1_0_1(X1))) != iProver_top
% 3.74/0.99      | iProver_ARSWP_146 != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_8047]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_9627,plain,
% 3.74/0.99      ( v4_relat_1(sK3,u1_struct_0(sK1)) = iProver_top
% 3.74/0.99      | iProver_ARSWP_153 != iProver_top
% 3.74/0.99      | iProver_ARSWP_146 != iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_8541,c_8548]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_9977,plain,
% 3.74/0.99      ( v4_relat_1(sK3,u1_struct_0(sK1)) = iProver_top ),
% 3.74/0.99      inference(global_propositional_subsumption,
% 3.74/0.99                [status(thm)],
% 3.74/0.99                [c_9627,c_31,c_2130]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_11838,plain,
% 3.74/0.99      ( v4_relat_1(sK3,k1_relat_1(sK3)) = iProver_top
% 3.74/0.99      | iProver_ARSWP_154 != iProver_top
% 3.74/0.99      | iProver_ARSWP_153 != iProver_top
% 3.74/0.99      | iProver_ARSWP_149 != iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_11697,c_9977]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_8,plain,
% 3.74/0.99      ( v1_partfun1(X0,k1_relat_1(X0))
% 3.74/0.99      | ~ v4_relat_1(X0,k1_relat_1(X0))
% 3.74/0.99      | ~ v1_relat_1(X0) ),
% 3.74/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_8570,plain,
% 3.74/0.99      ( v1_partfun1(X0,k1_relat_1(X0)) = iProver_top
% 3.74/0.99      | v4_relat_1(X0,k1_relat_1(X0)) != iProver_top
% 3.74/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_12201,plain,
% 3.74/0.99      ( v1_partfun1(sK3,k1_relat_1(sK3)) = iProver_top
% 3.74/0.99      | v1_relat_1(sK3) != iProver_top
% 3.74/0.99      | iProver_ARSWP_154 != iProver_top
% 3.74/0.99      | iProver_ARSWP_153 != iProver_top
% 3.74/0.99      | iProver_ARSWP_149 != iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_11838,c_8570]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_12329,plain,
% 3.74/0.99      ( v1_partfun1(sK3,k1_relat_1(sK3)) = iProver_top
% 3.74/0.99      | iProver_ARSWP_154 != iProver_top
% 3.74/0.99      | iProver_ARSWP_153 != iProver_top
% 3.74/0.99      | iProver_ARSWP_149 != iProver_top ),
% 3.74/0.99      inference(global_propositional_subsumption,
% 3.74/0.99                [status(thm)],
% 3.74/0.99                [c_12201,c_31,c_2127,c_2130,c_3431,c_4128,c_9272,c_11697]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_11841,plain,
% 3.74/0.99      ( arAF0_v1_funct_2_0_1_2(sK3,k1_relat_1(sK3)) = iProver_top
% 3.74/0.99      | iProver_ARSWP_154 != iProver_top
% 3.74/0.99      | iProver_ARSWP_153 != iProver_top
% 3.74/0.99      | iProver_ARSWP_149 != iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_11697,c_8540]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_11840,plain,
% 3.74/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(arAF0_k2_zfmisc_1_0_1(k1_relat_1(sK3)))) = iProver_top
% 3.74/0.99      | iProver_ARSWP_154 != iProver_top
% 3.74/0.99      | iProver_ARSWP_153 != iProver_top
% 3.74/0.99      | iProver_ARSWP_149 != iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_11697,c_8541]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_17,negated_conjecture,
% 3.74/0.99      ( ~ v1_funct_2(k2_funct_1(sK3),u1_struct_0(sK2),u1_struct_0(sK1))
% 3.74/0.99      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 3.74/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.74/0.99      | k2_relat_1(k2_funct_1(sK3)) != u1_struct_0(sK1) ),
% 3.74/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_8053,negated_conjecture,
% 3.74/0.99      ( ~ arAF0_v1_funct_2_0_1_2(arAF0_k2_funct_1_0,u1_struct_0(sK2))
% 3.74/0.99      | ~ m1_subset_1(arAF0_k2_funct_1_0,k1_zfmisc_1(arAF0_k2_zfmisc_1_0_1(u1_struct_0(sK2))))
% 3.74/0.99      | ~ v1_funct_1(arAF0_k2_funct_1_0)
% 3.74/0.99      | ~ iProver_ARSWP_152
% 3.74/0.99      | arAF0_k2_relat_1_0 != u1_struct_0(sK1) ),
% 3.74/0.99      inference(arg_filter_abstr,[status(unp)],[c_17]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_8542,plain,
% 3.74/0.99      ( arAF0_k2_relat_1_0 != u1_struct_0(sK1)
% 3.74/0.99      | arAF0_v1_funct_2_0_1_2(arAF0_k2_funct_1_0,u1_struct_0(sK2)) != iProver_top
% 3.74/0.99      | m1_subset_1(arAF0_k2_funct_1_0,k1_zfmisc_1(arAF0_k2_zfmisc_1_0_1(u1_struct_0(sK2)))) != iProver_top
% 3.74/0.99      | v1_funct_1(arAF0_k2_funct_1_0) != iProver_top
% 3.74/0.99      | iProver_ARSWP_152 != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_8053]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_11839,plain,
% 3.74/0.99      ( k1_relat_1(sK3) != arAF0_k2_relat_1_0
% 3.74/0.99      | arAF0_v1_funct_2_0_1_2(arAF0_k2_funct_1_0,u1_struct_0(sK2)) != iProver_top
% 3.74/0.99      | m1_subset_1(arAF0_k2_funct_1_0,k1_zfmisc_1(arAF0_k2_zfmisc_1_0_1(u1_struct_0(sK2)))) != iProver_top
% 3.74/0.99      | v1_funct_1(arAF0_k2_funct_1_0) != iProver_top
% 3.74/0.99      | iProver_ARSWP_154 != iProver_top
% 3.74/0.99      | iProver_ARSWP_153 != iProver_top
% 3.74/0.99      | iProver_ARSWP_152 != iProver_top
% 3.74/0.99      | iProver_ARSWP_149 != iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_11697,c_8542]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_11669,plain,
% 3.74/0.99      ( u1_struct_0(sK1) = X0
% 3.74/0.99      | k1_relat_1(sK3) != X0
% 3.74/0.99      | iProver_ARSWP_154 != iProver_top
% 3.74/0.99      | iProver_ARSWP_153 != iProver_top
% 3.74/0.99      | iProver_ARSWP_149 != iProver_top ),
% 3.74/0.99      inference(equality_factoring,[status(thm)],[c_10848]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_11668,plain,
% 3.74/0.99      ( u1_struct_0(sK1) != X0
% 3.74/0.99      | k1_relat_1(sK3) = X0
% 3.74/0.99      | iProver_ARSWP_154 != iProver_top
% 3.74/0.99      | iProver_ARSWP_153 != iProver_top
% 3.74/0.99      | iProver_ARSWP_149 != iProver_top ),
% 3.74/0.99      inference(equality_factoring,[status(thm)],[c_10848]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_9635,plain,
% 3.74/0.99      ( v4_relat_1(X0,k1_relat_1(X0)) = iProver_top
% 3.74/0.99      | v1_relat_1(X0) != iProver_top
% 3.74/0.99      | v1_funct_1(X0) != iProver_top
% 3.74/0.99      | iProver_ARSWP_150 != iProver_top
% 3.74/0.99      | iProver_ARSWP_146 != iProver_top
% 3.74/0.99      | arAF0_r1_tarski_0 != iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_8544,c_8548]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_10585,plain,
% 3.74/0.99      ( v1_partfun1(X0,k1_relat_1(X0)) = iProver_top
% 3.74/0.99      | v1_relat_1(X0) != iProver_top
% 3.74/0.99      | v1_funct_1(X0) != iProver_top
% 3.74/0.99      | iProver_ARSWP_150 != iProver_top
% 3.74/0.99      | iProver_ARSWP_146 != iProver_top
% 3.74/0.99      | arAF0_r1_tarski_0 != iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_9635,c_8570]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_1,plain,
% 3.74/0.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.74/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_8043,plain,
% 3.74/0.99      ( ~ iProver_ARSWP_142 | arAF0_r1_tarski_0 | arAF0_r2_hidden_0 ),
% 3.74/0.99      inference(arg_filter_abstr,[status(unp)],[c_1]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_8552,plain,
% 3.74/0.99      ( iProver_ARSWP_142 != iProver_top
% 3.74/0.99      | arAF0_r1_tarski_0 = iProver_top
% 3.74/0.99      | arAF0_r2_hidden_0 = iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_8043]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_8046,plain,
% 3.74/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(arAF0_k2_zfmisc_1_0_1(X1)))
% 3.74/0.99      | v1_relat_1(X0)
% 3.74/0.99      | ~ iProver_ARSWP_145 ),
% 3.74/0.99      inference(arg_filter_abstr,[status(unp)],[c_5]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_8549,plain,
% 3.74/0.99      ( m1_subset_1(X0,k1_zfmisc_1(arAF0_k2_zfmisc_1_0_1(X1))) != iProver_top
% 3.74/0.99      | v1_relat_1(X0) = iProver_top
% 3.74/0.99      | iProver_ARSWP_145 != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_8046]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_9525,plain,
% 3.74/0.99      ( v1_relat_1(sK3) = iProver_top
% 3.74/0.99      | iProver_ARSWP_153 != iProver_top
% 3.74/0.99      | iProver_ARSWP_145 != iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_8541,c_8549]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_9528,plain,
% 3.74/0.99      ( v1_relat_1(sK3) = iProver_top ),
% 3.74/0.99      inference(global_propositional_subsumption,
% 3.74/0.99                [status(thm)],
% 3.74/0.99                [c_9525,c_31,c_2127]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_7,plain,
% 3.74/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.74/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.74/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_8048,plain,
% 3.74/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(arAF0_k2_zfmisc_1_0_1(X1)))
% 3.74/0.99      | ~ iProver_ARSWP_147
% 3.74/0.99      | arAF0_k2_relset_1_0 = arAF0_k2_relat_1_0 ),
% 3.74/0.99      inference(arg_filter_abstr,[status(unp)],[c_7]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_8547,plain,
% 3.74/0.99      ( arAF0_k2_relset_1_0 = arAF0_k2_relat_1_0
% 3.74/0.99      | m1_subset_1(X0,k1_zfmisc_1(arAF0_k2_zfmisc_1_0_1(X1))) != iProver_top
% 3.74/0.99      | iProver_ARSWP_147 != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_8048]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_9637,plain,
% 3.74/0.99      ( arAF0_k2_relat_1_0 = arAF0_k2_relset_1_0
% 3.74/0.99      | v1_relat_1(X0) != iProver_top
% 3.74/0.99      | v1_funct_1(X0) != iProver_top
% 3.74/0.99      | iProver_ARSWP_150 != iProver_top
% 3.74/0.99      | iProver_ARSWP_147 != iProver_top
% 3.74/0.99      | arAF0_r1_tarski_0 != iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_8544,c_8547]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_9989,plain,
% 3.74/0.99      ( arAF0_k2_relat_1_0 = arAF0_k2_relset_1_0
% 3.74/0.99      | v1_funct_1(sK3) != iProver_top
% 3.74/0.99      | iProver_ARSWP_150 != iProver_top
% 3.74/0.99      | iProver_ARSWP_147 != iProver_top
% 3.74/0.99      | arAF0_r1_tarski_0 != iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_9528,c_9637]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_10154,plain,
% 3.74/0.99      ( arAF0_k2_relat_1_0 = arAF0_k2_relset_1_0
% 3.74/0.99      | iProver_ARSWP_150 != iProver_top
% 3.74/0.99      | iProver_ARSWP_147 != iProver_top
% 3.74/0.99      | arAF0_r1_tarski_0 != iProver_top ),
% 3.74/0.99      inference(global_propositional_subsumption,[status(thm)],[c_9989,c_29]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_10162,plain,
% 3.74/0.99      ( arAF0_k2_relat_1_0 = arAF0_k2_relset_1_0
% 3.74/0.99      | iProver_ARSWP_150 != iProver_top
% 3.74/0.99      | iProver_ARSWP_147 != iProver_top
% 3.74/0.99      | iProver_ARSWP_142 != iProver_top
% 3.74/0.99      | arAF0_r2_hidden_0 = iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_8552,c_10154]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_0,plain,
% 3.74/0.99      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.74/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_8042,plain,
% 3.74/0.99      ( ~ iProver_ARSWP_141 | arAF0_r1_tarski_0 | ~ arAF0_r2_hidden_0 ),
% 3.74/0.99      inference(arg_filter_abstr,[status(unp)],[c_0]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_8553,plain,
% 3.74/0.99      ( iProver_ARSWP_141 != iProver_top
% 3.74/0.99      | arAF0_r1_tarski_0 = iProver_top
% 3.74/0.99      | arAF0_r2_hidden_0 != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_8042]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_10170,plain,
% 3.74/0.99      ( arAF0_k2_relat_1_0 = arAF0_k2_relset_1_0
% 3.74/0.99      | iProver_ARSWP_150 != iProver_top
% 3.74/0.99      | iProver_ARSWP_147 != iProver_top
% 3.74/0.99      | iProver_ARSWP_142 != iProver_top
% 3.74/0.99      | iProver_ARSWP_141 != iProver_top
% 3.74/0.99      | arAF0_r1_tarski_0 = iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_10162,c_8553]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_8080,plain,
% 3.74/0.99      ( iProver_ARSWP_141 != iProver_top
% 3.74/0.99      | arAF0_r1_tarski_0 = iProver_top
% 3.74/0.99      | arAF0_r2_hidden_0 != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_8042]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_8081,plain,
% 3.74/0.99      ( iProver_ARSWP_142 != iProver_top
% 3.74/0.99      | arAF0_r1_tarski_0 = iProver_top
% 3.74/0.99      | arAF0_r2_hidden_0 = iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_8043]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_10267,plain,
% 3.74/0.99      ( iProver_ARSWP_142 != iProver_top
% 3.74/0.99      | iProver_ARSWP_141 != iProver_top
% 3.74/0.99      | arAF0_r1_tarski_0 = iProver_top ),
% 3.74/0.99      inference(global_propositional_subsumption,
% 3.74/0.99                [status(thm)],
% 3.74/0.99                [c_10170,c_8080,c_8081]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_10274,plain,
% 3.74/0.99      ( arAF0_k2_relat_1_0 = arAF0_k2_relset_1_0
% 3.74/0.99      | iProver_ARSWP_150 != iProver_top
% 3.74/0.99      | iProver_ARSWP_147 != iProver_top
% 3.74/0.99      | iProver_ARSWP_142 != iProver_top
% 3.74/0.99      | iProver_ARSWP_141 != iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_10267,c_10154]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_9429,plain,
% 3.74/0.99      ( arAF0_k2_relat_1_0 = arAF0_k2_relset_1_0
% 3.74/0.99      | iProver_ARSWP_153 != iProver_top
% 3.74/0.99      | iProver_ARSWP_147 != iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_8541,c_8547]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_4,plain,
% 3.74/0.99      ( ~ v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)) | ~ v1_funct_1(X0) ),
% 3.74/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_8045,plain,
% 3.74/0.99      ( ~ v1_relat_1(X0)
% 3.74/0.99      | v1_relat_1(arAF0_k2_funct_1_0)
% 3.74/0.99      | ~ v1_funct_1(X0)
% 3.74/0.99      | ~ iProver_ARSWP_144 ),
% 3.74/0.99      inference(arg_filter_abstr,[status(unp)],[c_4]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_8550,plain,
% 3.74/0.99      ( v1_relat_1(X0) != iProver_top
% 3.74/0.99      | v1_relat_1(arAF0_k2_funct_1_0) = iProver_top
% 3.74/0.99      | v1_funct_1(X0) != iProver_top
% 3.74/0.99      | iProver_ARSWP_144 != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_8045]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_8893,plain,
% 3.74/0.99      ( v1_relat_1(arAF0_k2_funct_1_0)
% 3.74/0.99      | ~ v1_relat_1(sK3)
% 3.74/0.99      | ~ v1_funct_1(sK3)
% 3.74/0.99      | ~ iProver_ARSWP_144 ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_8045]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_9194,plain,
% 3.74/0.99      ( v1_relat_1(arAF0_k2_funct_1_0) | ~ iProver_ARSWP_144 ),
% 3.74/0.99      inference(global_propositional_subsumption,
% 3.74/0.99                [status(thm)],
% 3.74/0.99                [c_8045,c_20,c_18,c_2126,c_8893]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_9196,plain,
% 3.74/0.99      ( v1_relat_1(arAF0_k2_funct_1_0) = iProver_top
% 3.74/0.99      | iProver_ARSWP_144 != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_9194]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_9852,plain,
% 3.74/0.99      ( v1_relat_1(arAF0_k2_funct_1_0) = iProver_top
% 3.74/0.99      | iProver_ARSWP_144 != iProver_top ),
% 3.74/0.99      inference(global_propositional_subsumption,[status(thm)],[c_8550,c_9196]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_3,plain,
% 3.74/0.99      ( ~ v1_relat_1(X0) | ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) ),
% 3.74/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_8044,plain,
% 3.74/0.99      ( ~ v1_relat_1(X0)
% 3.74/0.99      | ~ v1_funct_1(X0)
% 3.74/0.99      | v1_funct_1(arAF0_k2_funct_1_0)
% 3.74/0.99      | ~ iProver_ARSWP_143 ),
% 3.74/0.99      inference(arg_filter_abstr,[status(unp)],[c_3]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_8551,plain,
% 3.74/0.99      ( v1_relat_1(X0) != iProver_top
% 3.74/0.99      | v1_funct_1(X0) != iProver_top
% 3.74/0.99      | v1_funct_1(arAF0_k2_funct_1_0) = iProver_top
% 3.74/0.99      | iProver_ARSWP_143 != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_8044]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_8894,plain,
% 3.74/0.99      ( ~ v1_relat_1(sK3)
% 3.74/0.99      | v1_funct_1(arAF0_k2_funct_1_0)
% 3.74/0.99      | ~ v1_funct_1(sK3)
% 3.74/0.99      | ~ iProver_ARSWP_143 ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_8044]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_9116,plain,
% 3.74/0.99      ( v1_funct_1(arAF0_k2_funct_1_0) | ~ iProver_ARSWP_143 ),
% 3.74/0.99      inference(global_propositional_subsumption,
% 3.74/0.99                [status(thm)],
% 3.74/0.99                [c_8044,c_20,c_18,c_2126,c_8894]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_9118,plain,
% 3.74/0.99      ( v1_funct_1(arAF0_k2_funct_1_0) = iProver_top
% 3.74/0.99      | iProver_ARSWP_143 != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_9116]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_9859,plain,
% 3.74/0.99      ( v1_funct_1(arAF0_k2_funct_1_0) = iProver_top
% 3.74/0.99      | iProver_ARSWP_143 != iProver_top ),
% 3.74/0.99      inference(global_propositional_subsumption,[status(thm)],[c_8551,c_9118]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_10,plain,
% 3.74/0.99      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.74/0.99      | v1_partfun1(X0,k1_xboole_0)
% 3.74/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.74/0.99      | ~ v1_funct_1(X0) ),
% 3.74/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_8049,plain,
% 3.74/0.99      ( ~ arAF0_v1_funct_2_0_1_2(X0,k1_xboole_0)
% 3.74/0.99      | v1_partfun1(X0,k1_xboole_0)
% 3.74/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(arAF0_k2_zfmisc_1_0_1(k1_xboole_0)))
% 3.74/0.99      | ~ v1_funct_1(X0)
% 3.74/0.99      | ~ iProver_ARSWP_148 ),
% 3.74/0.99      inference(arg_filter_abstr,[status(unp)],[c_10]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_8546,plain,
% 3.74/0.99      ( arAF0_v1_funct_2_0_1_2(X0,k1_xboole_0) != iProver_top
% 3.74/0.99      | v1_partfun1(X0,k1_xboole_0) = iProver_top
% 3.74/0.99      | m1_subset_1(X0,k1_zfmisc_1(arAF0_k2_zfmisc_1_0_1(k1_xboole_0))) != iProver_top
% 3.74/0.99      | v1_funct_1(X0) != iProver_top
% 3.74/0.99      | iProver_ARSWP_148 != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_8049]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_21,negated_conjecture,
% 3.74/0.99      ( l1_orders_2(sK2) ),
% 3.74/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_8565,plain,
% 3.74/0.99      ( l1_orders_2(sK2) = iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_8567,plain,
% 3.74/0.99      ( l1_orders_2(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_9094,plain,
% 3.74/0.99      ( l1_struct_0(sK2) = iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_8565,c_8567]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_8563,plain,
% 3.74/0.99      ( l1_orders_2(sK1) = iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_9095,plain,
% 3.74/0.99      ( l1_struct_0(sK1) = iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_8563,c_8567]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_2,plain,
% 3.74/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.74/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_8571,plain,
% 3.74/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_8566,plain,
% 3.74/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_22,negated_conjecture,
% 3.74/0.99      ( ~ v2_struct_0(sK2) ),
% 3.74/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_8564,plain,
% 3.74/0.99      ( v2_struct_0(sK2) != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_8562,plain,
% 3.74/0.99      ( v2_struct_0(sK1) != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  % SZS output end Saturation for theBenchmark.p
% 3.74/0.99  
% 3.74/0.99  ------                               Statistics
% 3.74/0.99  
% 3.74/0.99  ------ Selected
% 3.74/0.99  
% 3.74/0.99  total_time:                             0.315
% 3.74/0.99  
%------------------------------------------------------------------------------
