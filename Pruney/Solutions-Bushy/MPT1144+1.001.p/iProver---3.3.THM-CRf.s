%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1144+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:00 EST 2020

% Result     : Theorem 19.60s
% Output     : CNFRefutation 19.60s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_2186)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
                & ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
                  | ~ r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r7_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ~ ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                & ~ r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r7_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r7_relat_2(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                & ~ r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X3,X2),X0)
                | r2_hidden(k4_tarski(X2,X3),X0)
                | ~ r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X1) )
            | ~ r7_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r7_relat_2(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                & ~ r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X5,X4),X0)
                | r2_hidden(k4_tarski(X4,X5),X0)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X1) )
            | ~ r7_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f43])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X3,X2),X0)
          & ~ r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
        & ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
        & r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r7_relat_2(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
              & ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
              & r2_hidden(sK2(X0,X1),X1)
              & r2_hidden(sK1(X0,X1),X1) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X5,X4),X0)
                | r2_hidden(k4_tarski(X4,X5),X0)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X1) )
            | ~ r7_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f44,f45])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r7_relat_2(X0,X1)
      | r2_hidden(sK2(X0,X1),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f38])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK0(X0,X1,X2) != X1
            & sK0(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( sK0(X0,X1,X2) = X1
          | sK0(X0,X1,X2) = X0
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK0(X0,X1,X2) != X1
              & sK0(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( sK0(X0,X1,X2) = X1
            | sK0(X0,X1,X2) = X0
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f94,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f59])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                  & v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) )
              <=> ( r3_orders_2(X0,X2,X1)
                  | r3_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( ( m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                    & v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) )
                <=> ( r3_orders_2(X0,X2,X1)
                    | r3_orders_2(X0,X1,X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                  & v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) )
              <~> ( r3_orders_2(X0,X2,X1)
                  | r3_orders_2(X0,X1,X2) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                  & v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) )
              <~> ( r3_orders_2(X0,X2,X1)
                  | r3_orders_2(X0,X1,X2) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( ~ r3_orders_2(X0,X2,X1)
                  & ~ r3_orders_2(X0,X1,X2) )
                | ~ m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                | ~ v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) )
              & ( r3_orders_2(X0,X2,X1)
                | r3_orders_2(X0,X1,X2)
                | ( m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                  & v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( ~ r3_orders_2(X0,X2,X1)
                  & ~ r3_orders_2(X0,X1,X2) )
                | ~ m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                | ~ v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) )
              & ( r3_orders_2(X0,X2,X1)
                | r3_orders_2(X0,X1,X2)
                | ( m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                  & v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ( ~ r3_orders_2(X0,X2,X1)
              & ~ r3_orders_2(X0,X1,X2) )
            | ~ m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) )
          & ( r3_orders_2(X0,X2,X1)
            | r3_orders_2(X0,X1,X2)
            | ( m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
              & v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) ) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ( ~ r3_orders_2(X0,sK5,X1)
            & ~ r3_orders_2(X0,X1,sK5) )
          | ~ m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,sK5),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,sK5),X0) )
        & ( r3_orders_2(X0,sK5,X1)
          | r3_orders_2(X0,X1,sK5)
          | ( m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,sK5),k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,sK5),X0) ) )
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( ~ r3_orders_2(X0,X2,X1)
                  & ~ r3_orders_2(X0,X1,X2) )
                | ~ m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                | ~ v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) )
              & ( r3_orders_2(X0,X2,X1)
                | r3_orders_2(X0,X1,X2)
                | ( m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                  & v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ( ( ~ r3_orders_2(X0,X2,sK4)
                & ~ r3_orders_2(X0,sK4,X2) )
              | ~ m1_subset_1(k7_domain_1(u1_struct_0(X0),sK4,X2),k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(k7_domain_1(u1_struct_0(X0),sK4,X2),X0) )
            & ( r3_orders_2(X0,X2,sK4)
              | r3_orders_2(X0,sK4,X2)
              | ( m1_subset_1(k7_domain_1(u1_struct_0(X0),sK4,X2),k1_zfmisc_1(u1_struct_0(X0)))
                & v6_orders_2(k7_domain_1(u1_struct_0(X0),sK4,X2),X0) ) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ( ~ r3_orders_2(X0,X2,X1)
                    & ~ r3_orders_2(X0,X1,X2) )
                  | ~ m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) )
                & ( r3_orders_2(X0,X2,X1)
                  | r3_orders_2(X0,X1,X2)
                  | ( m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                    & v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) ) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ( ~ r3_orders_2(sK3,X2,X1)
                  & ~ r3_orders_2(sK3,X1,X2) )
                | ~ m1_subset_1(k7_domain_1(u1_struct_0(sK3),X1,X2),k1_zfmisc_1(u1_struct_0(sK3)))
                | ~ v6_orders_2(k7_domain_1(u1_struct_0(sK3),X1,X2),sK3) )
              & ( r3_orders_2(sK3,X2,X1)
                | r3_orders_2(sK3,X1,X2)
                | ( m1_subset_1(k7_domain_1(u1_struct_0(sK3),X1,X2),k1_zfmisc_1(u1_struct_0(sK3)))
                  & v6_orders_2(k7_domain_1(u1_struct_0(sK3),X1,X2),sK3) ) )
              & m1_subset_1(X2,u1_struct_0(sK3)) )
          & m1_subset_1(X1,u1_struct_0(sK3)) )
      & l1_orders_2(sK3)
      & v3_orders_2(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ( ( ~ r3_orders_2(sK3,sK5,sK4)
        & ~ r3_orders_2(sK3,sK4,sK5) )
      | ~ m1_subset_1(k7_domain_1(u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ v6_orders_2(k7_domain_1(u1_struct_0(sK3),sK4,sK5),sK3) )
    & ( r3_orders_2(sK3,sK5,sK4)
      | r3_orders_2(sK3,sK4,sK5)
      | ( m1_subset_1(k7_domain_1(u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
        & v6_orders_2(k7_domain_1(u1_struct_0(sK3),sK4,sK5),sK3) ) )
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l1_orders_2(sK3)
    & v3_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f50,f53,f52,f51])).

fof(f85,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f54])).

fof(f84,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f54])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f81,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f83,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f73,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_orders_2(X1,X0)
              | ~ r7_relat_2(u1_orders_2(X0),X1) )
            & ( r7_relat_2(u1_orders_2(X0),X1)
              | ~ v6_orders_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v6_orders_2(X1,X0)
      | ~ r7_relat_2(u1_orders_2(X0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f74,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f87,plain,
    ( r3_orders_2(sK3,sK5,sK4)
    | r3_orders_2(sK3,sK4,sK5)
    | m1_subset_1(k7_domain_1(u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f54])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r7_relat_2(u1_orders_2(X0),X1)
      | ~ v6_orders_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f92,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f60])).

fof(f93,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f92])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f90,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f61])).

fof(f91,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f90])).

fof(f65,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X4),X0)
      | r2_hidden(k4_tarski(X4,X5),X0)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ r7_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f82,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f88,plain,
    ( ~ r3_orders_2(sK3,sK4,sK5)
    | ~ m1_subset_1(k7_domain_1(u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v6_orders_2(k7_domain_1(u1_struct_0(sK3),sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f89,plain,
    ( ~ r3_orders_2(sK3,sK5,sK4)
    | ~ m1_subset_1(k7_domain_1(u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v6_orders_2(k7_domain_1(u1_struct_0(sK3),sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r7_relat_2(X0,X1)
      | r2_hidden(sK1(X0,X1),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r7_relat_2(X0,X1)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r7_relat_2(X0,X1)
      | ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f86,plain,
    ( r3_orders_2(sK3,sK5,sK4)
    | r3_orders_2(sK3,sK4,sK5)
    | v6_orders_2(k7_domain_1(u1_struct_0(sK3),sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_16,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_911,plain,
    ( r1_orders_2(X0,X1,X2) != iProver_top
    | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_12,plain,
    ( r2_hidden(sK2(X0,X1),X1)
    | r7_relat_2(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_915,plain,
    ( r2_hidden(sK2(X0,X1),X1) = iProver_top
    | r7_relat_2(X0,X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_918,plain,
    ( X0 = X1
    | X0 = X2
    | r2_hidden(X0,k2_tarski(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1941,plain,
    ( sK2(X0,k2_tarski(X1,X2)) = X1
    | sK2(X0,k2_tarski(X1,X2)) = X2
    | r7_relat_2(X0,k2_tarski(X1,X2)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_915,c_918])).

cnf(c_11093,plain,
    ( sK2(X0,k2_tarski(X1,X2)) = X1
    | sK2(X0,k2_tarski(X1,X2)) = X2
    | r7_relat_2(X0,k2_tarski(X2,X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_1941])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_897,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_896,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | v1_xboole_0(X1)
    | k7_domain_1(X1,X2,X0) = k2_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_906,plain,
    ( k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2368,plain,
    ( k7_domain_1(u1_struct_0(sK3),X0,sK4) = k2_tarski(X0,sK4)
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_896,c_906])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_35,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_32,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_37,plain,
    ( l1_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_20,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_57,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_59,plain,
    ( v2_struct_0(sK3) = iProver_top
    | l1_struct_0(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_57])).

cnf(c_18,plain,
    ( l1_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_63,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_65,plain,
    ( l1_struct_0(sK3) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_63])).

cnf(c_4704,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | k7_domain_1(u1_struct_0(sK3),X0,sK4) = k2_tarski(X0,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2368,c_35,c_37,c_59,c_65])).

cnf(c_4705,plain,
    ( k7_domain_1(u1_struct_0(sK3),X0,sK4) = k2_tarski(X0,sK4)
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4704])).

cnf(c_4712,plain,
    ( k7_domain_1(u1_struct_0(sK3),sK5,sK4) = k2_tarski(sK5,sK4) ),
    inference(superposition,[status(thm)],[c_897,c_4705])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | m1_subset_1(k7_domain_1(X1,X2,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_910,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(X2,X1) != iProver_top
    | m1_subset_1(k7_domain_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4719,plain,
    ( m1_subset_1(k2_tarski(sK5,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4712,c_910])).

cnf(c_38,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_39,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_12153,plain,
    ( m1_subset_1(k2_tarski(sK5,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4719,c_35,c_37,c_38,c_39,c_59,c_65])).

cnf(c_2,plain,
    ( ~ r7_relat_2(u1_orders_2(X0),X1)
    | v6_orders_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_925,plain,
    ( r7_relat_2(u1_orders_2(X0),X1) != iProver_top
    | v6_orders_2(X1,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_12158,plain,
    ( r7_relat_2(u1_orders_2(sK3),k2_tarski(sK5,sK4)) != iProver_top
    | v6_orders_2(k2_tarski(sK5,sK4),sK3) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_12153,c_925])).

cnf(c_12514,plain,
    ( v6_orders_2(k2_tarski(sK5,sK4),sK3) = iProver_top
    | r7_relat_2(u1_orders_2(sK3),k2_tarski(sK5,sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12158,c_37])).

cnf(c_12515,plain,
    ( r7_relat_2(u1_orders_2(sK3),k2_tarski(sK5,sK4)) != iProver_top
    | v6_orders_2(k2_tarski(sK5,sK4),sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_12514])).

cnf(c_12523,plain,
    ( sK2(u1_orders_2(sK3),k2_tarski(sK4,sK5)) = sK4
    | sK2(u1_orders_2(sK3),k2_tarski(sK4,sK5)) = sK5
    | v6_orders_2(k2_tarski(sK5,sK4),sK3) = iProver_top
    | v1_relat_1(u1_orders_2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11093,c_12515])).

cnf(c_19,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_60,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_62,plain,
    ( m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_60])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1253,plain,
    ( ~ m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | v1_relat_1(u1_orders_2(X0)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1254,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) != iProver_top
    | v1_relat_1(u1_orders_2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1253])).

cnf(c_1256,plain,
    ( m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) != iProver_top
    | v1_relat_1(u1_orders_2(sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1254])).

cnf(c_28,negated_conjecture,
    ( r3_orders_2(sK3,sK4,sK5)
    | r3_orders_2(sK3,sK5,sK4)
    | m1_subset_1(k7_domain_1(u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_899,plain,
    ( r3_orders_2(sK3,sK4,sK5) = iProver_top
    | r3_orders_2(sK3,sK5,sK4) = iProver_top
    | m1_subset_1(k7_domain_1(u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1311,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(k7_domain_1(u1_struct_0(sK3),sK4,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1489,plain,
    ( m1_subset_1(k7_domain_1(u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1311])).

cnf(c_1490,plain,
    ( m1_subset_1(k7_domain_1(u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1489])).

cnf(c_1777,plain,
    ( m1_subset_1(k7_domain_1(u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_899,c_35,c_37,c_38,c_39,c_59,c_65,c_1490])).

cnf(c_2639,plain,
    ( r7_relat_2(u1_orders_2(sK3),k7_domain_1(u1_struct_0(sK3),sK4,sK5)) != iProver_top
    | v6_orders_2(k7_domain_1(u1_struct_0(sK3),sK4,sK5),sK3) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1777,c_925])).

cnf(c_2111,plain,
    ( ~ r7_relat_2(u1_orders_2(sK3),k7_domain_1(u1_struct_0(sK3),sK4,sK5))
    | v6_orders_2(k7_domain_1(u1_struct_0(sK3),sK4,sK5),sK3)
    | ~ m1_subset_1(k7_domain_1(u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2112,plain,
    ( r7_relat_2(u1_orders_2(sK3),k7_domain_1(u1_struct_0(sK3),sK4,sK5)) != iProver_top
    | v6_orders_2(k7_domain_1(u1_struct_0(sK3),sK4,sK5),sK3) = iProver_top
    | m1_subset_1(k7_domain_1(u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2111])).

cnf(c_7748,plain,
    ( v6_orders_2(k7_domain_1(u1_struct_0(sK3),sK4,sK5),sK3) = iProver_top
    | r7_relat_2(u1_orders_2(sK3),k7_domain_1(u1_struct_0(sK3),sK4,sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2639,c_35,c_37,c_38,c_39,c_59,c_65,c_1490,c_2112])).

cnf(c_7749,plain,
    ( r7_relat_2(u1_orders_2(sK3),k7_domain_1(u1_struct_0(sK3),sK4,sK5)) != iProver_top
    | v6_orders_2(k7_domain_1(u1_struct_0(sK3),sK4,sK5),sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_7748])).

cnf(c_2367,plain,
    ( k7_domain_1(u1_struct_0(sK3),X0,sK5) = k2_tarski(X0,sK5)
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_897,c_906])).

cnf(c_3779,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | k7_domain_1(u1_struct_0(sK3),X0,sK5) = k2_tarski(X0,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2367,c_35,c_37,c_59,c_65])).

cnf(c_3780,plain,
    ( k7_domain_1(u1_struct_0(sK3),X0,sK5) = k2_tarski(X0,sK5)
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3779])).

cnf(c_3788,plain,
    ( k7_domain_1(u1_struct_0(sK3),sK4,sK5) = k2_tarski(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_896,c_3780])).

cnf(c_7752,plain,
    ( r7_relat_2(u1_orders_2(sK3),k2_tarski(sK4,sK5)) != iProver_top
    | v6_orders_2(k2_tarski(sK4,sK5),sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7749,c_3788])).

cnf(c_11097,plain,
    ( sK2(u1_orders_2(sK3),k2_tarski(sK4,sK5)) = sK4
    | sK2(u1_orders_2(sK3),k2_tarski(sK4,sK5)) = sK5
    | v6_orders_2(k2_tarski(sK4,sK5),sK3) = iProver_top
    | v1_relat_1(u1_orders_2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1941,c_7752])).

cnf(c_3,plain,
    ( r7_relat_2(u1_orders_2(X0),X1)
    | ~ v6_orders_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_924,plain,
    ( r7_relat_2(u1_orders_2(X0),X1) = iProver_top
    | v6_orders_2(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2610,plain,
    ( r7_relat_2(u1_orders_2(sK3),k7_domain_1(u1_struct_0(sK3),sK4,sK5)) = iProver_top
    | v6_orders_2(k7_domain_1(u1_struct_0(sK3),sK4,sK5),sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1777,c_924])).

cnf(c_7571,plain,
    ( v6_orders_2(k7_domain_1(u1_struct_0(sK3),sK4,sK5),sK3) != iProver_top
    | r7_relat_2(u1_orders_2(sK3),k7_domain_1(u1_struct_0(sK3),sK4,sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2610,c_37])).

cnf(c_7572,plain,
    ( r7_relat_2(u1_orders_2(sK3),k7_domain_1(u1_struct_0(sK3),sK4,sK5)) = iProver_top
    | v6_orders_2(k7_domain_1(u1_struct_0(sK3),sK4,sK5),sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_7571])).

cnf(c_7575,plain,
    ( r7_relat_2(u1_orders_2(sK3),k2_tarski(sK4,sK5)) = iProver_top
    | v6_orders_2(k2_tarski(sK4,sK5),sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7572,c_3788])).

cnf(c_7579,plain,
    ( r7_relat_2(u1_orders_2(sK3),k2_tarski(sK5,sK4)) = iProver_top
    | v6_orders_2(k2_tarski(sK4,sK5),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_7575])).

cnf(c_12522,plain,
    ( v6_orders_2(k2_tarski(sK4,sK5),sK3) != iProver_top
    | v6_orders_2(k2_tarski(sK5,sK4),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_7579,c_12515])).

cnf(c_17859,plain,
    ( v6_orders_2(k2_tarski(sK5,sK4),sK3) = iProver_top
    | sK2(u1_orders_2(sK3),k2_tarski(sK4,sK5)) = sK5
    | sK2(u1_orders_2(sK3),k2_tarski(sK4,sK5)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12523,c_37,c_62,c_1256,c_11097,c_12522])).

cnf(c_17860,plain,
    ( sK2(u1_orders_2(sK3),k2_tarski(sK4,sK5)) = sK4
    | sK2(u1_orders_2(sK3),k2_tarski(sK4,sK5)) = sK5
    | v6_orders_2(k2_tarski(sK5,sK4),sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_17859])).

cnf(c_8,plain,
    ( r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_919,plain,
    ( r2_hidden(X0,k2_tarski(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_7,plain,
    ( r2_hidden(X0,k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_920,plain,
    ( r2_hidden(X0,k2_tarski(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r2_hidden(k4_tarski(X2,X0),X3)
    | r2_hidden(k4_tarski(X0,X2),X3)
    | ~ r7_relat_2(X3,X1)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_913,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),X3) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X3) = iProver_top
    | r7_relat_2(X3,X1) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2987,plain,
    ( r2_hidden(X0,k2_tarski(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),X3) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X3) = iProver_top
    | r7_relat_2(X3,k2_tarski(X1,X2)) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_920,c_913])).

cnf(c_24960,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),X2) = iProver_top
    | r7_relat_2(X2,k2_tarski(X1,X0)) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_919,c_2987])).

cnf(c_32113,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),u1_orders_2(sK3)) = iProver_top
    | r2_hidden(k4_tarski(sK5,sK4),u1_orders_2(sK3)) = iProver_top
    | v6_orders_2(k2_tarski(sK4,sK5),sK3) != iProver_top
    | v1_relat_1(u1_orders_2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7579,c_24960])).

cnf(c_33,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_36,plain,
    ( v3_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_22,plain,
    ( r3_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1763,plain,
    ( r3_orders_2(sK3,sK4,sK5)
    | ~ r1_orders_2(sK3,sK4,sK5)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1767,plain,
    ( r3_orders_2(sK3,sK4,sK5) = iProver_top
    | r1_orders_2(sK3,sK4,sK5) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1763])).

cnf(c_15,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2206,plain,
    ( r1_orders_2(sK3,sK4,sK5)
    | ~ r2_hidden(k4_tarski(sK4,sK5),u1_orders_2(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2207,plain,
    ( r1_orders_2(sK3,sK4,sK5) = iProver_top
    | r2_hidden(k4_tarski(sK4,sK5),u1_orders_2(sK3)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2206])).

cnf(c_27,negated_conjecture,
    ( ~ r3_orders_2(sK3,sK4,sK5)
    | ~ v6_orders_2(k7_domain_1(u1_struct_0(sK3),sK4,sK5),sK3)
    | ~ m1_subset_1(k7_domain_1(u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_900,plain,
    ( r3_orders_2(sK3,sK4,sK5) != iProver_top
    | v6_orders_2(k7_domain_1(u1_struct_0(sK3),sK4,sK5),sK3) != iProver_top
    | m1_subset_1(k7_domain_1(u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_42,plain,
    ( r3_orders_2(sK3,sK4,sK5) != iProver_top
    | v6_orders_2(k7_domain_1(u1_struct_0(sK3),sK4,sK5),sK3) != iProver_top
    | m1_subset_1(k7_domain_1(u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2148,plain,
    ( v6_orders_2(k7_domain_1(u1_struct_0(sK3),sK4,sK5),sK3) != iProver_top
    | r3_orders_2(sK3,sK4,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_900,c_35,c_37,c_38,c_39,c_42,c_59,c_65,c_1490])).

cnf(c_2149,plain,
    ( r3_orders_2(sK3,sK4,sK5) != iProver_top
    | v6_orders_2(k7_domain_1(u1_struct_0(sK3),sK4,sK5),sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_2148])).

cnf(c_4020,plain,
    ( r3_orders_2(sK3,sK4,sK5) != iProver_top
    | v6_orders_2(k2_tarski(sK4,sK5),sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3788,c_2149])).

cnf(c_34255,plain,
    ( v6_orders_2(k2_tarski(sK4,sK5),sK3) != iProver_top
    | r2_hidden(k4_tarski(sK5,sK4),u1_orders_2(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_32113,c_35,c_36,c_37,c_38,c_39,c_62,c_1256,c_1767,c_2207,c_4020])).

cnf(c_34256,plain,
    ( r2_hidden(k4_tarski(sK5,sK4),u1_orders_2(sK3)) = iProver_top
    | v6_orders_2(k2_tarski(sK4,sK5),sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_34255])).

cnf(c_912,plain,
    ( r1_orders_2(X0,X1,X2) = iProver_top
    | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_34262,plain,
    ( r1_orders_2(sK3,sK5,sK4) = iProver_top
    | v6_orders_2(k2_tarski(sK4,sK5),sK3) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_34256,c_912])).

cnf(c_26,negated_conjecture,
    ( ~ r3_orders_2(sK3,sK5,sK4)
    | ~ v6_orders_2(k7_domain_1(u1_struct_0(sK3),sK4,sK5),sK3)
    | ~ m1_subset_1(k7_domain_1(u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_901,plain,
    ( r3_orders_2(sK3,sK5,sK4) != iProver_top
    | v6_orders_2(k7_domain_1(u1_struct_0(sK3),sK4,sK5),sK3) != iProver_top
    | m1_subset_1(k7_domain_1(u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_43,plain,
    ( r3_orders_2(sK3,sK5,sK4) != iProver_top
    | v6_orders_2(k7_domain_1(u1_struct_0(sK3),sK4,sK5),sK3) != iProver_top
    | m1_subset_1(k7_domain_1(u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2408,plain,
    ( v6_orders_2(k7_domain_1(u1_struct_0(sK3),sK4,sK5),sK3) != iProver_top
    | r3_orders_2(sK3,sK5,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_901,c_35,c_37,c_38,c_39,c_43,c_59,c_65,c_1490])).

cnf(c_2409,plain,
    ( r3_orders_2(sK3,sK5,sK4) != iProver_top
    | v6_orders_2(k7_domain_1(u1_struct_0(sK3),sK4,sK5),sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_2408])).

cnf(c_4019,plain,
    ( r3_orders_2(sK3,sK5,sK4) != iProver_top
    | v6_orders_2(k2_tarski(sK4,sK5),sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3788,c_2409])).

cnf(c_905,plain,
    ( r3_orders_2(X0,X1,X2) = iProver_top
    | r1_orders_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v3_orders_2(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3247,plain,
    ( r3_orders_2(sK3,X0,sK4) = iProver_top
    | r1_orders_2(sK3,X0,sK4) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_896,c_905])).

cnf(c_18682,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r1_orders_2(sK3,X0,sK4) != iProver_top
    | r3_orders_2(sK3,X0,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3247,c_35,c_36,c_37])).

cnf(c_18683,plain,
    ( r3_orders_2(sK3,X0,sK4) = iProver_top
    | r1_orders_2(sK3,X0,sK4) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_18682])).

cnf(c_18691,plain,
    ( r3_orders_2(sK3,sK5,sK4) = iProver_top
    | r1_orders_2(sK3,sK5,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_897,c_18683])).

cnf(c_37178,plain,
    ( v6_orders_2(k2_tarski(sK4,sK5),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_34262,c_37,c_38,c_39,c_4019,c_18691])).

cnf(c_37186,plain,
    ( v6_orders_2(k2_tarski(sK5,sK4),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_37178])).

cnf(c_38105,plain,
    ( sK2(u1_orders_2(sK3),k2_tarski(sK4,sK5)) = sK4
    | sK2(u1_orders_2(sK3),k2_tarski(sK4,sK5)) = sK5 ),
    inference(superposition,[status(thm)],[c_17860,c_37186])).

cnf(c_38927,plain,
    ( sK2(u1_orders_2(sK3),k2_tarski(sK4,sK5)) = sK5
    | sK2(u1_orders_2(sK3),k2_tarski(sK5,sK4)) = sK4 ),
    inference(superposition,[status(thm)],[c_1,c_38105])).

cnf(c_13,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | r7_relat_2(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_914,plain,
    ( r2_hidden(sK1(X0,X1),X1) = iProver_top
    | r7_relat_2(X0,X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1932,plain,
    ( sK1(X0,k2_tarski(X1,X2)) = X1
    | sK1(X0,k2_tarski(X1,X2)) = X2
    | r7_relat_2(X0,k2_tarski(X1,X2)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_914,c_918])).

cnf(c_9158,plain,
    ( sK1(X0,k2_tarski(X1,X2)) = X1
    | sK1(X0,k2_tarski(X1,X2)) = X2
    | r7_relat_2(X0,k2_tarski(X2,X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_1932])).

cnf(c_12524,plain,
    ( sK1(u1_orders_2(sK3),k2_tarski(sK4,sK5)) = sK4
    | sK1(u1_orders_2(sK3),k2_tarski(sK4,sK5)) = sK5
    | v6_orders_2(k2_tarski(sK5,sK4),sK3) = iProver_top
    | v1_relat_1(u1_orders_2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9158,c_12515])).

cnf(c_9162,plain,
    ( sK1(u1_orders_2(sK3),k2_tarski(sK4,sK5)) = sK4
    | sK1(u1_orders_2(sK3),k2_tarski(sK4,sK5)) = sK5
    | v6_orders_2(k2_tarski(sK4,sK5),sK3) = iProver_top
    | v1_relat_1(u1_orders_2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1932,c_7752])).

cnf(c_17869,plain,
    ( v6_orders_2(k2_tarski(sK5,sK4),sK3) = iProver_top
    | sK1(u1_orders_2(sK3),k2_tarski(sK4,sK5)) = sK5
    | sK1(u1_orders_2(sK3),k2_tarski(sK4,sK5)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12524,c_37,c_62,c_1256,c_9162,c_12522])).

cnf(c_17870,plain,
    ( sK1(u1_orders_2(sK3),k2_tarski(sK4,sK5)) = sK4
    | sK1(u1_orders_2(sK3),k2_tarski(sK4,sK5)) = sK5
    | v6_orders_2(k2_tarski(sK5,sK4),sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_17869])).

cnf(c_38104,plain,
    ( sK1(u1_orders_2(sK3),k2_tarski(sK4,sK5)) = sK4
    | sK1(u1_orders_2(sK3),k2_tarski(sK4,sK5)) = sK5 ),
    inference(superposition,[status(thm)],[c_17870,c_37186])).

cnf(c_38116,plain,
    ( sK1(u1_orders_2(sK3),k2_tarski(sK4,sK5)) = sK5
    | sK1(u1_orders_2(sK3),k2_tarski(sK5,sK4)) = sK4 ),
    inference(superposition,[status(thm)],[c_1,c_38104])).

cnf(c_10,plain,
    ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
    | r7_relat_2(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_917,plain,
    ( r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0) != iProver_top
    | r7_relat_2(X0,X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_38870,plain,
    ( sK1(u1_orders_2(sK3),k2_tarski(sK5,sK4)) = sK4
    | r2_hidden(k4_tarski(sK2(u1_orders_2(sK3),k2_tarski(sK4,sK5)),sK5),u1_orders_2(sK3)) != iProver_top
    | r7_relat_2(u1_orders_2(sK3),k2_tarski(sK4,sK5)) = iProver_top
    | v1_relat_1(u1_orders_2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_38116,c_917])).

cnf(c_48488,plain,
    ( sK1(u1_orders_2(sK3),k2_tarski(sK5,sK4)) = sK4
    | r2_hidden(k4_tarski(sK2(u1_orders_2(sK3),k2_tarski(sK4,sK5)),sK5),u1_orders_2(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_38870,c_37,c_38,c_39,c_62,c_1256,c_4019,c_7752,c_18691,c_34262])).

cnf(c_48499,plain,
    ( sK1(u1_orders_2(sK3),k2_tarski(sK5,sK4)) = sK4
    | sK2(u1_orders_2(sK3),k2_tarski(sK5,sK4)) = sK4
    | r2_hidden(k4_tarski(sK5,sK5),u1_orders_2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_38927,c_48488])).

cnf(c_24,plain,
    ( r3_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1336,plain,
    ( r3_orders_2(sK3,sK5,sK5)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_1446,plain,
    ( r3_orders_2(sK3,sK5,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_1336])).

cnf(c_23,plain,
    ( ~ r3_orders_2(X0,X1,X2)
    | r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1375,plain,
    ( ~ r3_orders_2(sK3,sK5,X0)
    | r1_orders_2(sK3,sK5,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1656,plain,
    ( ~ r3_orders_2(sK3,sK5,sK5)
    | r1_orders_2(sK3,sK5,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_1375])).

cnf(c_2185,plain,
    ( ~ r1_orders_2(sK3,sK5,sK5)
    | r2_hidden(k4_tarski(sK5,sK5),u1_orders_2(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_48574,plain,
    ( ~ r2_hidden(k4_tarski(sK5,sK5),u1_orders_2(sK3))
    | sK1(u1_orders_2(sK3),k2_tarski(sK5,sK4)) = sK4
    | sK2(u1_orders_2(sK3),k2_tarski(sK5,sK4)) = sK4 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_48499])).

cnf(c_50987,plain,
    ( sK2(u1_orders_2(sK3),k2_tarski(sK5,sK4)) = sK4
    | sK1(u1_orders_2(sK3),k2_tarski(sK5,sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_48499,c_35,c_36,c_37,c_39,c_1447,c_1657,c_2186])).

cnf(c_50988,plain,
    ( sK1(u1_orders_2(sK3),k2_tarski(sK5,sK4)) = sK4
    | sK2(u1_orders_2(sK3),k2_tarski(sK5,sK4)) = sK4 ),
    inference(renaming,[status(thm)],[c_50987])).

cnf(c_11,plain,
    ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
    | r7_relat_2(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_916,plain,
    ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) != iProver_top
    | r7_relat_2(X0,X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_38119,plain,
    ( sK1(u1_orders_2(sK3),k2_tarski(sK4,sK5)) = sK5
    | r2_hidden(k4_tarski(sK4,sK2(u1_orders_2(sK3),k2_tarski(sK4,sK5))),u1_orders_2(sK3)) != iProver_top
    | r7_relat_2(u1_orders_2(sK3),k2_tarski(sK4,sK5)) = iProver_top
    | v1_relat_1(u1_orders_2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_38104,c_916])).

cnf(c_46322,plain,
    ( sK1(u1_orders_2(sK3),k2_tarski(sK4,sK5)) = sK5
    | r2_hidden(k4_tarski(sK4,sK2(u1_orders_2(sK3),k2_tarski(sK4,sK5))),u1_orders_2(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_38119,c_37,c_38,c_39,c_62,c_1256,c_4019,c_7752,c_18691,c_34262])).

cnf(c_46333,plain,
    ( sK1(u1_orders_2(sK3),k2_tarski(sK4,sK5)) = sK5
    | sK2(u1_orders_2(sK3),k2_tarski(sK5,sK4)) = sK4
    | r2_hidden(k4_tarski(sK4,sK5),u1_orders_2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_38927,c_46322])).

cnf(c_1764,plain,
    ( ~ r1_orders_2(sK3,sK4,sK5)
    | r2_hidden(k4_tarski(sK4,sK5),u1_orders_2(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_29,negated_conjecture,
    ( r3_orders_2(sK3,sK4,sK5)
    | r3_orders_2(sK3,sK5,sK4)
    | v6_orders_2(k7_domain_1(u1_struct_0(sK3),sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_898,plain,
    ( r3_orders_2(sK3,sK4,sK5) = iProver_top
    | r3_orders_2(sK3,sK5,sK4) = iProver_top
    | v6_orders_2(k7_domain_1(u1_struct_0(sK3),sK4,sK5),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4022,plain,
    ( r3_orders_2(sK3,sK4,sK5) = iProver_top
    | r3_orders_2(sK3,sK5,sK4) = iProver_top
    | v6_orders_2(k2_tarski(sK4,sK5),sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3788,c_898])).

cnf(c_4049,plain,
    ( r3_orders_2(sK3,sK4,sK5)
    | r3_orders_2(sK3,sK5,sK4)
    | v6_orders_2(k2_tarski(sK4,sK5),sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4022])).

cnf(c_904,plain,
    ( r3_orders_2(X0,X1,X2) != iProver_top
    | r1_orders_2(X0,X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v3_orders_2(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3206,plain,
    ( r3_orders_2(sK3,X0,sK5) != iProver_top
    | r1_orders_2(sK3,X0,sK5) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_897,c_904])).

cnf(c_14666,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r1_orders_2(sK3,X0,sK5) = iProver_top
    | r3_orders_2(sK3,X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3206,c_35,c_36,c_37])).

cnf(c_14667,plain,
    ( r3_orders_2(sK3,X0,sK5) != iProver_top
    | r1_orders_2(sK3,X0,sK5) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_14666])).

cnf(c_14676,plain,
    ( r3_orders_2(sK3,sK4,sK5) != iProver_top
    | r1_orders_2(sK3,sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_896,c_14667])).

cnf(c_14776,plain,
    ( ~ r3_orders_2(sK3,sK4,sK5)
    | r1_orders_2(sK3,sK4,sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_14676])).

cnf(c_3207,plain,
    ( r3_orders_2(sK3,X0,sK4) != iProver_top
    | r1_orders_2(sK3,X0,sK4) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_896,c_904])).

cnf(c_16206,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r1_orders_2(sK3,X0,sK4) = iProver_top
    | r3_orders_2(sK3,X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3207,c_35,c_36,c_37])).

cnf(c_16207,plain,
    ( r3_orders_2(sK3,X0,sK4) != iProver_top
    | r1_orders_2(sK3,X0,sK4) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_16206])).

cnf(c_16215,plain,
    ( r3_orders_2(sK3,sK5,sK4) != iProver_top
    | r1_orders_2(sK3,sK5,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_897,c_16207])).

cnf(c_16315,plain,
    ( ~ r3_orders_2(sK3,sK5,sK4)
    | r1_orders_2(sK3,sK5,sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_16215])).

cnf(c_37180,plain,
    ( ~ v6_orders_2(k2_tarski(sK4,sK5),sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_37178])).

cnf(c_38118,plain,
    ( sK1(u1_orders_2(sK3),k2_tarski(sK4,sK5)) = sK5
    | r2_hidden(k4_tarski(sK2(u1_orders_2(sK3),k2_tarski(sK4,sK5)),sK4),u1_orders_2(sK3)) != iProver_top
    | r7_relat_2(u1_orders_2(sK3),k2_tarski(sK4,sK5)) = iProver_top
    | v1_relat_1(u1_orders_2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_38104,c_917])).

cnf(c_44573,plain,
    ( sK1(u1_orders_2(sK3),k2_tarski(sK4,sK5)) = sK5
    | r2_hidden(k4_tarski(sK2(u1_orders_2(sK3),k2_tarski(sK4,sK5)),sK4),u1_orders_2(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_38118,c_37,c_38,c_39,c_62,c_1256,c_4019,c_7752,c_18691,c_34262])).

cnf(c_44584,plain,
    ( sK1(u1_orders_2(sK3),k2_tarski(sK4,sK5)) = sK5
    | sK2(u1_orders_2(sK3),k2_tarski(sK5,sK4)) = sK4
    | r2_hidden(k4_tarski(sK5,sK4),u1_orders_2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_38927,c_44573])).

cnf(c_45957,plain,
    ( sK1(u1_orders_2(sK3),k2_tarski(sK4,sK5)) = sK5
    | sK2(u1_orders_2(sK3),k2_tarski(sK5,sK4)) = sK4
    | r1_orders_2(sK3,sK5,sK4) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_911,c_44584])).

cnf(c_45975,plain,
    ( ~ r1_orders_2(sK3,sK5,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | sK1(u1_orders_2(sK3),k2_tarski(sK4,sK5)) = sK5
    | sK2(u1_orders_2(sK3),k2_tarski(sK5,sK4)) = sK4 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_45957])).

cnf(c_46402,plain,
    ( ~ r2_hidden(k4_tarski(sK4,sK5),u1_orders_2(sK3))
    | sK1(u1_orders_2(sK3),k2_tarski(sK4,sK5)) = sK5
    | sK2(u1_orders_2(sK3),k2_tarski(sK5,sK4)) = sK4 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_46333])).

cnf(c_47330,plain,
    ( sK2(u1_orders_2(sK3),k2_tarski(sK5,sK4)) = sK4
    | sK1(u1_orders_2(sK3),k2_tarski(sK4,sK5)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_46333,c_32,c_31,c_30,c_1764,c_4049,c_14776,c_16315,c_37180,c_45975,c_46402])).

cnf(c_47331,plain,
    ( sK1(u1_orders_2(sK3),k2_tarski(sK4,sK5)) = sK5
    | sK2(u1_orders_2(sK3),k2_tarski(sK5,sK4)) = sK4 ),
    inference(renaming,[status(thm)],[c_47330])).

cnf(c_47335,plain,
    ( sK1(u1_orders_2(sK3),k2_tarski(sK5,sK4)) = sK5
    | sK2(u1_orders_2(sK3),k2_tarski(sK5,sK4)) = sK4 ),
    inference(superposition,[status(thm)],[c_1,c_47331])).

cnf(c_51005,plain,
    ( sK2(u1_orders_2(sK3),k2_tarski(sK5,sK4)) = sK4
    | sK4 = sK5 ),
    inference(superposition,[status(thm)],[c_50988,c_47335])).

cnf(c_46335,plain,
    ( sK1(u1_orders_2(sK3),k2_tarski(sK4,sK5)) = sK5
    | r2_hidden(k4_tarski(sK4,sK2(u1_orders_2(sK3),k2_tarski(sK5,sK4))),u1_orders_2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_46322])).

cnf(c_52242,plain,
    ( sK1(u1_orders_2(sK3),k2_tarski(sK4,sK5)) = sK5
    | sK4 = sK5
    | r2_hidden(k4_tarski(sK4,sK4),u1_orders_2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_51005,c_46335])).

cnf(c_1341,plain,
    ( r3_orders_2(sK3,sK4,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_1477,plain,
    ( r3_orders_2(sK3,sK4,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_1341])).

cnf(c_1478,plain,
    ( r3_orders_2(sK3,sK4,sK4) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1477])).

cnf(c_1380,plain,
    ( ~ r3_orders_2(sK3,sK4,X0)
    | r1_orders_2(sK3,sK4,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1547,plain,
    ( ~ r3_orders_2(sK3,sK4,sK4)
    | r1_orders_2(sK3,sK4,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_1380])).

cnf(c_1548,plain,
    ( r3_orders_2(sK3,sK4,sK4) != iProver_top
    | r1_orders_2(sK3,sK4,sK4) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1547])).

cnf(c_1867,plain,
    ( ~ r1_orders_2(sK3,sK4,sK4)
    | r2_hidden(k4_tarski(sK4,sK4),u1_orders_2(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1868,plain,
    ( r1_orders_2(sK3,sK4,sK4) != iProver_top
    | r2_hidden(k4_tarski(sK4,sK4),u1_orders_2(sK3)) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1867])).

cnf(c_53203,plain,
    ( sK4 = sK5
    | sK1(u1_orders_2(sK3),k2_tarski(sK4,sK5)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_52242,c_35,c_36,c_37,c_38,c_39,c_1478,c_1548,c_1868])).

cnf(c_53204,plain,
    ( sK1(u1_orders_2(sK3),k2_tarski(sK4,sK5)) = sK5
    | sK4 = sK5 ),
    inference(renaming,[status(thm)],[c_53203])).

cnf(c_53208,plain,
    ( sK1(u1_orders_2(sK3),k2_tarski(sK5,sK4)) = sK5
    | sK4 = sK5 ),
    inference(superposition,[status(thm)],[c_1,c_53204])).

cnf(c_52229,plain,
    ( sK4 = sK5
    | r2_hidden(k4_tarski(sK1(u1_orders_2(sK3),k2_tarski(sK5,sK4)),sK4),u1_orders_2(sK3)) != iProver_top
    | r7_relat_2(u1_orders_2(sK3),k2_tarski(sK5,sK4)) = iProver_top
    | v1_relat_1(u1_orders_2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_51005,c_916])).

cnf(c_7757,plain,
    ( r7_relat_2(u1_orders_2(sK3),k2_tarski(sK5,sK4)) != iProver_top
    | v6_orders_2(k2_tarski(sK4,sK5),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_7752])).

cnf(c_56378,plain,
    ( sK4 = sK5
    | r2_hidden(k4_tarski(sK1(u1_orders_2(sK3),k2_tarski(sK5,sK4)),sK4),u1_orders_2(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_52229,c_37,c_38,c_39,c_62,c_1256,c_4019,c_7757,c_18691,c_34262])).

cnf(c_56389,plain,
    ( sK4 = sK5
    | r2_hidden(k4_tarski(sK5,sK4),u1_orders_2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_53208,c_56378])).

cnf(c_56455,plain,
    ( sK4 = sK5
    | r1_orders_2(sK3,sK5,sK4) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_911,c_56389])).

cnf(c_52228,plain,
    ( sK4 = sK5
    | r2_hidden(k4_tarski(sK4,sK1(u1_orders_2(sK3),k2_tarski(sK5,sK4))),u1_orders_2(sK3)) != iProver_top
    | r7_relat_2(u1_orders_2(sK3),k2_tarski(sK5,sK4)) = iProver_top
    | v1_relat_1(u1_orders_2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_51005,c_917])).

cnf(c_55081,plain,
    ( sK4 = sK5
    | r2_hidden(k4_tarski(sK4,sK1(u1_orders_2(sK3),k2_tarski(sK5,sK4))),u1_orders_2(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_52228,c_37,c_38,c_39,c_62,c_1256,c_4019,c_7757,c_18691,c_34262])).

cnf(c_55092,plain,
    ( sK4 = sK5
    | r2_hidden(k4_tarski(sK4,sK5),u1_orders_2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_53208,c_55081])).

cnf(c_55158,plain,
    ( sK4 = sK5
    | r1_orders_2(sK3,sK4,sK5) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_911,c_55092])).

cnf(c_55421,plain,
    ( r1_orders_2(sK3,sK4,sK5) != iProver_top
    | sK4 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_55158,c_37,c_38,c_39])).

cnf(c_55422,plain,
    ( sK4 = sK5
    | r1_orders_2(sK3,sK4,sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_55421])).

cnf(c_59138,plain,
    ( sK4 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_56455,c_37,c_38,c_39,c_4019,c_4022,c_14676,c_16215,c_18691,c_34262,c_55422])).

cnf(c_59156,plain,
    ( sK1(u1_orders_2(sK3),k2_tarski(sK5,sK5)) = sK5 ),
    inference(demodulation,[status(thm)],[c_59138,c_38116])).

cnf(c_2768,plain,
    ( r1_orders_2(X0,sK2(u1_orders_2(X0),X1),sK1(u1_orders_2(X0),X1)) != iProver_top
    | r7_relat_2(u1_orders_2(X0),X1) = iProver_top
    | m1_subset_1(sK1(u1_orders_2(X0),X1),u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK2(u1_orders_2(X0),X1),u1_struct_0(X0)) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | v1_relat_1(u1_orders_2(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_911,c_917])).

cnf(c_908,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_926,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1772,plain,
    ( l1_orders_2(X0) != iProver_top
    | v1_relat_1(u1_orders_2(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_908,c_926])).

cnf(c_11077,plain,
    ( l1_orders_2(X0) != iProver_top
    | m1_subset_1(sK2(u1_orders_2(X0),X1),u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK1(u1_orders_2(X0),X1),u1_struct_0(X0)) != iProver_top
    | r7_relat_2(u1_orders_2(X0),X1) = iProver_top
    | r1_orders_2(X0,sK2(u1_orders_2(X0),X1),sK1(u1_orders_2(X0),X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2768,c_1772])).

cnf(c_11078,plain,
    ( r1_orders_2(X0,sK2(u1_orders_2(X0),X1),sK1(u1_orders_2(X0),X1)) != iProver_top
    | r7_relat_2(u1_orders_2(X0),X1) = iProver_top
    | m1_subset_1(sK1(u1_orders_2(X0),X1),u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK2(u1_orders_2(X0),X1),u1_struct_0(X0)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_11077])).

cnf(c_59674,plain,
    ( r1_orders_2(sK3,sK2(u1_orders_2(sK3),k2_tarski(sK5,sK5)),sK5) != iProver_top
    | r7_relat_2(u1_orders_2(sK3),k2_tarski(sK5,sK5)) = iProver_top
    | m1_subset_1(sK1(u1_orders_2(sK3),k2_tarski(sK5,sK5)),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK2(u1_orders_2(sK3),k2_tarski(sK5,sK5)),u1_struct_0(sK3)) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_59156,c_11078])).

cnf(c_59154,plain,
    ( sK2(u1_orders_2(sK3),k2_tarski(sK5,sK5)) = sK5 ),
    inference(demodulation,[status(thm)],[c_59138,c_38927])).

cnf(c_59681,plain,
    ( r1_orders_2(sK3,sK5,sK5) != iProver_top
    | r7_relat_2(u1_orders_2(sK3),k2_tarski(sK5,sK5)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_59674,c_59154,c_59156])).

cnf(c_59160,plain,
    ( v6_orders_2(k2_tarski(sK5,sK5),sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_59138,c_37178])).

cnf(c_3787,plain,
    ( k7_domain_1(u1_struct_0(sK3),sK5,sK5) = k2_tarski(sK5,sK5) ),
    inference(superposition,[status(thm)],[c_897,c_3780])).

cnf(c_3794,plain,
    ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3787,c_910])).

cnf(c_5180,plain,
    ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3794,c_35,c_37,c_39,c_59,c_65])).

cnf(c_5185,plain,
    ( r7_relat_2(u1_orders_2(sK3),k2_tarski(sK5,sK5)) != iProver_top
    | v6_orders_2(k2_tarski(sK5,sK5),sK3) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5180,c_925])).

cnf(c_5748,plain,
    ( v6_orders_2(k2_tarski(sK5,sK5),sK3) = iProver_top
    | r7_relat_2(u1_orders_2(sK3),k2_tarski(sK5,sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5185,c_37])).

cnf(c_5749,plain,
    ( r7_relat_2(u1_orders_2(sK3),k2_tarski(sK5,sK5)) != iProver_top
    | v6_orders_2(k2_tarski(sK5,sK5),sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_5748])).

cnf(c_1657,plain,
    ( r3_orders_2(sK3,sK5,sK5) != iProver_top
    | r1_orders_2(sK3,sK5,sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1656])).

cnf(c_1447,plain,
    ( r3_orders_2(sK3,sK5,sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1446])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_59681,c_59160,c_5749,c_1657,c_1447,c_39,c_37,c_36,c_35])).


%------------------------------------------------------------------------------
