%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1146+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:00 EST 2020

% Result     : Theorem 3.42s
% Output     : CNFRefutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :  251 (4732 expanded)
%              Number of clauses        :  157 (1311 expanded)
%              Number of leaves         :   24 (1321 expanded)
%              Depth                    :   25
%              Number of atoms          : 1149 (43139 expanded)
%              Number of equality atoms :  298 (2280 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   22 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                  & v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) )
              <=> ( r3_orders_2(X0,X2,X1)
                  | r3_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                  & v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) )
              <=> ( r3_orders_2(X0,X2,X1)
                  | r3_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                    & v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) )
                  | ( ~ r3_orders_2(X0,X2,X1)
                    & ~ r3_orders_2(X0,X1,X2) ) )
                & ( r3_orders_2(X0,X2,X1)
                  | r3_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                    & v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) )
                  | ( ~ r3_orders_2(X0,X2,X1)
                    & ~ r3_orders_2(X0,X1,X2) ) )
                & ( r3_orders_2(X0,X2,X1)
                  | r3_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0)
      | ~ r3_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ~ ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                          & v6_orders_2(X3,X0) )
                       => ~ ( r2_hidden(X2,X3)
                            & r2_hidden(X1,X3) ) )
                    & ( r1_orders_2(X0,X2,X1)
                      | r1_orders_2(X0,X1,X2) ) )
                & ~ ( ~ r1_orders_2(X0,X2,X1)
                    & ~ r1_orders_2(X0,X1,X2)
                    & ? [X3] :
                        ( r2_hidden(X2,X3)
                        & r2_hidden(X1,X3)
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & v6_orders_2(X3,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( ~ ( ! [X3] :
                          ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                            & v6_orders_2(X3,X0) )
                         => ~ ( r2_hidden(X2,X3)
                              & r2_hidden(X1,X3) ) )
                      & ( r1_orders_2(X0,X2,X1)
                        | r1_orders_2(X0,X1,X2) ) )
                  & ~ ( ~ r1_orders_2(X0,X2,X1)
                      & ~ r1_orders_2(X0,X1,X2)
                      & ? [X3] :
                          ( r2_hidden(X2,X3)
                          & r2_hidden(X1,X3)
                          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                          & v6_orders_2(X3,X0) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f18,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( ~ ( ! [X3] :
                          ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                            & v6_orders_2(X3,X0) )
                         => ~ ( r2_hidden(X2,X3)
                              & r2_hidden(X1,X3) ) )
                      & ( r1_orders_2(X0,X2,X1)
                        | r1_orders_2(X0,X1,X2) ) )
                  & ~ ( ~ r1_orders_2(X0,X2,X1)
                      & ~ r1_orders_2(X0,X1,X2)
                      & ? [X4] :
                          ( r2_hidden(X2,X4)
                          & r2_hidden(X1,X4)
                          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                          & v6_orders_2(X4,X0) ) ) ) ) ) ) ),
    inference(rectify,[],[f17])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( ! [X3] :
                      ( ~ r2_hidden(X2,X3)
                      | ~ r2_hidden(X1,X3)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      | ~ v6_orders_2(X3,X0) )
                  & ( r1_orders_2(X0,X2,X1)
                    | r1_orders_2(X0,X1,X2) ) )
                | ( ~ r1_orders_2(X0,X2,X1)
                  & ~ r1_orders_2(X0,X1,X2)
                  & ? [X4] :
                      ( r2_hidden(X2,X4)
                      & r2_hidden(X1,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                      & v6_orders_2(X4,X0) ) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( ! [X3] :
                      ( ~ r2_hidden(X2,X3)
                      | ~ r2_hidden(X1,X3)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      | ~ v6_orders_2(X3,X0) )
                  & ( r1_orders_2(X0,X2,X1)
                    | r1_orders_2(X0,X1,X2) ) )
                | ( ~ r1_orders_2(X0,X2,X1)
                  & ~ r1_orders_2(X0,X1,X2)
                  & ? [X4] :
                      ( r2_hidden(X2,X4)
                      & r2_hidden(X1,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                      & v6_orders_2(X4,X0) ) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f37])).

fof(f39,plain,(
    ! [X1,X2,X0] :
      ( ( ~ r1_orders_2(X0,X2,X1)
        & ~ r1_orders_2(X0,X1,X2)
        & ? [X4] :
            ( r2_hidden(X2,X4)
            & r2_hidden(X1,X4)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X4,X0) ) )
      | ~ sP0(X1,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( ! [X3] :
                      ( ~ r2_hidden(X2,X3)
                      | ~ r2_hidden(X1,X3)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      | ~ v6_orders_2(X3,X0) )
                  & ( r1_orders_2(X0,X2,X1)
                    | r1_orders_2(X0,X1,X2) ) )
                | sP0(X1,X2,X0) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(definition_folding,[],[f38,f39])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ( ! [X3] :
                  ( ~ r2_hidden(X2,X3)
                  | ~ r2_hidden(X1,X3)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v6_orders_2(X3,X0) )
              & ( r1_orders_2(X0,X2,X1)
                | r1_orders_2(X0,X1,X2) ) )
            | sP0(X1,X2,X0) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ( ! [X3] :
                ( ~ r2_hidden(sK7,X3)
                | ~ r2_hidden(X1,X3)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                | ~ v6_orders_2(X3,X0) )
            & ( r1_orders_2(X0,sK7,X1)
              | r1_orders_2(X0,X1,sK7) ) )
          | sP0(X1,sK7,X0) )
        & m1_subset_1(sK7,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( ! [X3] :
                      ( ~ r2_hidden(X2,X3)
                      | ~ r2_hidden(X1,X3)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      | ~ v6_orders_2(X3,X0) )
                  & ( r1_orders_2(X0,X2,X1)
                    | r1_orders_2(X0,X1,X2) ) )
                | sP0(X1,X2,X0) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ( ( ! [X3] :
                    ( ~ r2_hidden(X2,X3)
                    | ~ r2_hidden(sK6,X3)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    | ~ v6_orders_2(X3,X0) )
                & ( r1_orders_2(X0,X2,sK6)
                  | r1_orders_2(X0,sK6,X2) ) )
              | sP0(sK6,X2,X0) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK6,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ( ! [X3] :
                        ( ~ r2_hidden(X2,X3)
                        | ~ r2_hidden(X1,X3)
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        | ~ v6_orders_2(X3,X0) )
                    & ( r1_orders_2(X0,X2,X1)
                      | r1_orders_2(X0,X1,X2) ) )
                  | sP0(X1,X2,X0) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ( ! [X3] :
                      ( ~ r2_hidden(X2,X3)
                      | ~ r2_hidden(X1,X3)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK5)))
                      | ~ v6_orders_2(X3,sK5) )
                  & ( r1_orders_2(sK5,X2,X1)
                    | r1_orders_2(sK5,X1,X2) ) )
                | sP0(X1,X2,sK5) )
              & m1_subset_1(X2,u1_struct_0(sK5)) )
          & m1_subset_1(X1,u1_struct_0(sK5)) )
      & l1_orders_2(sK5)
      & v3_orders_2(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,
    ( ( ( ! [X3] :
            ( ~ r2_hidden(sK7,X3)
            | ~ r2_hidden(sK6,X3)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK5)))
            | ~ v6_orders_2(X3,sK5) )
        & ( r1_orders_2(sK5,sK7,sK6)
          | r1_orders_2(sK5,sK6,sK7) ) )
      | sP0(sK6,sK7,sK5) )
    & m1_subset_1(sK7,u1_struct_0(sK5))
    & m1_subset_1(sK6,u1_struct_0(sK5))
    & l1_orders_2(sK5)
    & v3_orders_2(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f40,f61,f60,f59])).

fof(f100,plain,(
    v3_orders_2(sK5) ),
    inference(cnf_transformation,[],[f62])).

fof(f101,plain,(
    l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f62])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f82,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v2_struct_0(X0) )
     => v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f84,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f55,plain,(
    ! [X1,X2,X0] :
      ( ( ~ r1_orders_2(X0,X2,X1)
        & ~ r1_orders_2(X0,X1,X2)
        & ? [X4] :
            ( r2_hidden(X2,X4)
            & r2_hidden(X1,X4)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X4,X0) ) )
      | ~ sP0(X1,X2,X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_orders_2(X2,X1,X0)
        & ~ r1_orders_2(X2,X0,X1)
        & ? [X3] :
            ( r2_hidden(X1,X3)
            & r2_hidden(X0,X3)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
            & v6_orders_2(X3,X2) ) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f55])).

fof(f57,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X1,X3)
          & r2_hidden(X0,X3)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
          & v6_orders_2(X3,X2) )
     => ( r2_hidden(X1,sK4(X0,X1,X2))
        & r2_hidden(X0,sK4(X0,X1,X2))
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
        & v6_orders_2(sK4(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_orders_2(X2,X1,X0)
        & ~ r1_orders_2(X2,X0,X1)
        & r2_hidden(X1,sK4(X0,X1,X2))
        & r2_hidden(X0,sK4(X0,X1,X2))
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
        & v6_orders_2(sK4(X0,X1,X2),X2) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f56,f57])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,sK4(X0,X1,X2))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f104,plain,
    ( r1_orders_2(sK5,sK7,sK6)
    | r1_orders_2(sK5,sK6,sK7)
    | sP0(sK6,sK7,sK5) ),
    inference(cnf_transformation,[],[f62])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r7_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ~ ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                & ~ r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r7_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f48,plain,(
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
    inference(rectify,[],[f47])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X3,X2),X0)
          & ~ r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
        & ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
        & r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r7_relat_2(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
              & ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
              & r2_hidden(sK3(X0,X1),X1)
              & r2_hidden(sK2(X0,X1),X1) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X5,X4),X0)
                | r2_hidden(k4_tarski(X4,X5),X0)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X1) )
            | ~ r7_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f48,f49])).

fof(f74,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X4),X0)
      | r2_hidden(k4_tarski(X4,X5),X0)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ r7_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f102,plain,(
    m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f62])).

fof(f103,plain,(
    m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f62])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f83,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X2,X0,X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f105,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK7,X3)
      | ~ r2_hidden(sK6,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK5)))
      | ~ v6_orders_2(X3,sK5)
      | sP0(sK6,sK7,sK5) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK1(X0,X1,X2) != X1
            & sK1(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( sK1(X0,X1,X2) = X1
          | sK1(X0,X1,X2) = X0
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK1(X0,X1,X2) != X1
              & sK1(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( sK1(X0,X1,X2) = X1
            | sK1(X0,X1,X2) = X0
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f44,f45])).

fof(f70,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f106,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f70])).

fof(f107,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f106])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f15,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f69,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f108,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f69])).

fof(f109,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f108])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_orders_2(X1,X0)
              | ~ r7_relat_2(u1_orders_2(X0),X1) )
            & ( r7_relat_2(u1_orders_2(X0),X1)
              | ~ v6_orders_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r7_relat_2(u1_orders_2(X0),X1)
      | ~ v6_orders_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( v6_orders_2(sK4(X0,X1,X2),X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,sK4(X0,X1,X2))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X2,X1,X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_27,plain,
    ( ~ r3_orders_2(X0,X1,X2)
    | v6_orders_2(k7_domain_1(u1_struct_0(X0),X2,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_42,negated_conjecture,
    ( v3_orders_2(sK5) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_643,plain,
    ( ~ r3_orders_2(X0,X1,X2)
    | v6_orders_2(k7_domain_1(u1_struct_0(X0),X2,X1),X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_42])).

cnf(c_644,plain,
    ( ~ r3_orders_2(sK5,X0,X1)
    | v6_orders_2(k7_domain_1(u1_struct_0(sK5),X1,X0),sK5)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | v2_struct_0(sK5)
    | ~ l1_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_643])).

cnf(c_41,negated_conjecture,
    ( l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_646,plain,
    ( v2_struct_0(sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | v6_orders_2(k7_domain_1(u1_struct_0(sK5),X1,X0),sK5)
    | ~ r3_orders_2(sK5,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_644,c_41])).

cnf(c_647,plain,
    ( ~ r3_orders_2(sK5,X0,X1)
    | v6_orders_2(k7_domain_1(u1_struct_0(sK5),X1,X0),sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | v2_struct_0(sK5) ),
    inference(renaming,[status(thm)],[c_646])).

cnf(c_19,plain,
    ( l1_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_21,plain,
    ( ~ v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_467,plain,
    ( ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_19,c_21])).

cnf(c_814,plain,
    ( ~ v2_struct_0(X0)
    | v1_xboole_0(u1_struct_0(X0))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_467,c_41])).

cnf(c_815,plain,
    ( ~ v2_struct_0(sK5)
    | v1_xboole_0(u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_814])).

cnf(c_966,plain,
    ( ~ r3_orders_2(sK5,X0,X1)
    | v6_orders_2(k7_domain_1(u1_struct_0(sK5),X1,X0),sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | v1_xboole_0(u1_struct_0(sK5)) ),
    inference(resolution,[status(thm)],[c_647,c_815])).

cnf(c_3198,plain,
    ( ~ r3_orders_2(sK5,X0,sK6)
    | v6_orders_2(k7_domain_1(u1_struct_0(sK5),sK6,X0),sK5)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | v1_xboole_0(u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_966])).

cnf(c_11573,plain,
    ( ~ r3_orders_2(sK5,sK7,sK6)
    | v6_orders_2(k7_domain_1(u1_struct_0(sK5),sK6,sK7),sK5)
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | v1_xboole_0(u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_3198])).

cnf(c_33,plain,
    ( ~ sP0(X0,X1,X2)
    | r2_hidden(X1,sK4(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_38,negated_conjecture,
    ( sP0(sK6,sK7,sK5)
    | r1_orders_2(sK5,sK6,sK7)
    | r1_orders_2(sK5,sK7,sK6) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1165,plain,
    ( r1_orders_2(sK5,sK6,sK7)
    | r1_orders_2(sK5,sK7,sK6)
    | r2_hidden(X0,sK4(X1,X0,X2))
    | sK5 != X2
    | sK6 != X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_38])).

cnf(c_1166,plain,
    ( r1_orders_2(sK5,sK6,sK7)
    | r1_orders_2(sK5,sK7,sK6)
    | r2_hidden(sK7,sK4(sK6,sK7,sK5)) ),
    inference(unflattening,[status(thm)],[c_1165])).

cnf(c_2763,plain,
    ( r1_orders_2(sK5,sK6,sK7) = iProver_top
    | r1_orders_2(sK5,sK7,sK6) = iProver_top
    | r2_hidden(sK7,sK4(sK6,sK7,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1166])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r2_hidden(k4_tarski(X2,X0),X3)
    | r2_hidden(k4_tarski(X0,X2),X3)
    | ~ r7_relat_2(X3,X1)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2785,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),X3) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X3) = iProver_top
    | r7_relat_2(X3,X1) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_6253,plain,
    ( r1_orders_2(sK5,sK6,sK7) = iProver_top
    | r1_orders_2(sK5,sK7,sK6) = iProver_top
    | r2_hidden(X0,sK4(sK6,sK7,sK5)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK7),X1) = iProver_top
    | r2_hidden(k4_tarski(sK7,X0),X1) = iProver_top
    | r7_relat_2(X1,sK4(sK6,sK7,sK5)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2763,c_2785])).

cnf(c_44,plain,
    ( l1_orders_2(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_40,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_45,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_39,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_46,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_20,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_91,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_93,plain,
    ( m1_subset_1(u1_orders_2(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5)))) = iProver_top
    | l1_orders_2(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_91])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_3289,plain,
    ( ~ m1_subset_1(u1_orders_2(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5))))
    | v1_relat_1(u1_orders_2(sK5)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3290,plain,
    ( m1_subset_1(u1_orders_2(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5)))) != iProver_top
    | v1_relat_1(u1_orders_2(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3289])).

cnf(c_16,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_849,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_41])).

cnf(c_850,plain,
    ( r1_orders_2(sK5,X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_849])).

cnf(c_3163,plain,
    ( r1_orders_2(sK5,sK7,X0)
    | ~ r2_hidden(k4_tarski(sK7,X0),u1_orders_2(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_850])).

cnf(c_3432,plain,
    ( r1_orders_2(sK5,sK7,sK6)
    | ~ r2_hidden(k4_tarski(sK7,sK6),u1_orders_2(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_3163])).

cnf(c_3433,plain,
    ( r1_orders_2(sK5,sK7,sK6) = iProver_top
    | r2_hidden(k4_tarski(sK7,sK6),u1_orders_2(sK5)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3432])).

cnf(c_3168,plain,
    ( r1_orders_2(sK5,sK6,X0)
    | ~ r2_hidden(k4_tarski(sK6,X0),u1_orders_2(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_850])).

cnf(c_3519,plain,
    ( r1_orders_2(sK5,sK6,sK7)
    | ~ r2_hidden(k4_tarski(sK6,sK7),u1_orders_2(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_3168])).

cnf(c_3520,plain,
    ( r1_orders_2(sK5,sK6,sK7) = iProver_top
    | r2_hidden(k4_tarski(sK6,sK7),u1_orders_2(sK5)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3519])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | m1_subset_1(k7_domain_1(X1,X2,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2784,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(X2,X1) != iProver_top
    | m1_subset_1(k7_domain_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_32,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r1_orders_2(X2,X0,X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_37,negated_conjecture,
    ( sP0(sK6,sK7,sK5)
    | ~ r2_hidden(sK6,X0)
    | ~ r2_hidden(sK7,X0)
    | ~ v6_orders_2(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1201,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r2_hidden(sK6,X3)
    | ~ r2_hidden(sK7,X3)
    | ~ v6_orders_2(X3,sK5)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK5)))
    | sK5 != X0
    | sK6 != X1
    | sK7 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_37])).

cnf(c_1202,plain,
    ( ~ r1_orders_2(sK5,sK6,sK7)
    | ~ r2_hidden(sK6,X0)
    | ~ r2_hidden(sK7,X0)
    | ~ v6_orders_2(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(unflattening,[status(thm)],[c_1201])).

cnf(c_2761,plain,
    ( r1_orders_2(sK5,sK6,sK7) != iProver_top
    | r2_hidden(sK6,X0) != iProver_top
    | r2_hidden(sK7,X0) != iProver_top
    | v6_orders_2(X0,sK5) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1202])).

cnf(c_5443,plain,
    ( r1_orders_2(sK5,sK6,sK7) != iProver_top
    | r2_hidden(sK6,k7_domain_1(u1_struct_0(sK5),X0,X1)) != iProver_top
    | r2_hidden(sK7,k7_domain_1(u1_struct_0(sK5),X0,X1)) != iProver_top
    | v6_orders_2(k7_domain_1(u1_struct_0(sK5),X0,X1),sK5) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2784,c_2761])).

cnf(c_2101,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3578,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_2101])).

cnf(c_3599,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_2101])).

cnf(c_8,plain,
    ( r2_hidden(X0,k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_3676,plain,
    ( r2_hidden(sK7,k2_tarski(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3679,plain,
    ( r2_hidden(sK7,k2_tarski(sK6,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3676])).

cnf(c_3324,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | m1_subset_1(k7_domain_1(u1_struct_0(sK5),X0,sK7),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | v1_xboole_0(u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_3726,plain,
    ( m1_subset_1(k7_domain_1(u1_struct_0(sK5),sK6,sK7),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | v1_xboole_0(u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_3324])).

cnf(c_3727,plain,
    ( m1_subset_1(k7_domain_1(u1_struct_0(sK5),sK6,sK7),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3726])).

cnf(c_28,plain,
    ( ~ r3_orders_2(X0,X1,X2)
    | v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_616,plain,
    ( ~ r3_orders_2(X0,X1,X2)
    | v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_42])).

cnf(c_617,plain,
    ( ~ r3_orders_2(sK5,X0,X1)
    | v6_orders_2(k7_domain_1(u1_struct_0(sK5),X0,X1),sK5)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | v2_struct_0(sK5)
    | ~ l1_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_616])).

cnf(c_621,plain,
    ( v2_struct_0(sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | v6_orders_2(k7_domain_1(u1_struct_0(sK5),X0,X1),sK5)
    | ~ r3_orders_2(sK5,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_617,c_41])).

cnf(c_622,plain,
    ( ~ r3_orders_2(sK5,X0,X1)
    | v6_orders_2(k7_domain_1(u1_struct_0(sK5),X0,X1),sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | v2_struct_0(sK5) ),
    inference(renaming,[status(thm)],[c_621])).

cnf(c_986,plain,
    ( ~ r3_orders_2(sK5,X0,X1)
    | v6_orders_2(k7_domain_1(u1_struct_0(sK5),X0,X1),sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | v1_xboole_0(u1_struct_0(sK5)) ),
    inference(resolution,[status(thm)],[c_622,c_815])).

cnf(c_3209,plain,
    ( ~ r3_orders_2(sK5,X0,sK7)
    | v6_orders_2(k7_domain_1(u1_struct_0(sK5),X0,sK7),sK5)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | v1_xboole_0(u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_986])).

cnf(c_3986,plain,
    ( ~ r3_orders_2(sK5,sK6,sK7)
    | v6_orders_2(k7_domain_1(u1_struct_0(sK5),sK6,sK7),sK5)
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | v1_xboole_0(u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_3209])).

cnf(c_3987,plain,
    ( r3_orders_2(sK5,sK6,sK7) != iProver_top
    | v6_orders_2(k7_domain_1(u1_struct_0(sK5),sK6,sK7),sK5) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3986])).

cnf(c_2780,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_2781,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_17,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_831,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_41])).

cnf(c_832,plain,
    ( ~ r1_orders_2(sK5,X0,X1)
    | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_831])).

cnf(c_2778,plain,
    ( r1_orders_2(sK5,X0,X1) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK5)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_832])).

cnf(c_30,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2782,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3496,plain,
    ( r1_orders_2(sK5,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | v1_xboole_0(u1_orders_2(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2778,c_2782])).

cnf(c_4095,plain,
    ( r1_orders_2(sK5,X0,sK7) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | v1_xboole_0(u1_orders_2(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2781,c_3496])).

cnf(c_4293,plain,
    ( r1_orders_2(sK5,sK6,sK7) != iProver_top
    | v1_xboole_0(u1_orders_2(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2780,c_4095])).

cnf(c_9,plain,
    ( r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_3259,plain,
    ( r2_hidden(sK6,k2_tarski(sK6,X0)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_4374,plain,
    ( r2_hidden(sK6,k2_tarski(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_3259])).

cnf(c_4375,plain,
    ( r2_hidden(sK6,k2_tarski(sK6,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4374])).

cnf(c_824,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_41])).

cnf(c_825,plain,
    ( m1_subset_1(u1_orders_2(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5)))) ),
    inference(unflattening,[status(thm)],[c_824])).

cnf(c_2779,plain,
    ( m1_subset_1(u1_orders_2(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_825])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2796,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4485,plain,
    ( v1_xboole_0(u1_struct_0(sK5)) != iProver_top
    | v1_xboole_0(u1_orders_2(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2779,c_2796])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | v1_xboole_0(X1)
    | k7_domain_1(X1,X2,X0) = k2_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2783,plain,
    ( k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_5246,plain,
    ( k7_domain_1(u1_struct_0(sK5),X0,sK7) = k2_tarski(X0,sK7)
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2781,c_2783])).

cnf(c_5620,plain,
    ( k7_domain_1(u1_struct_0(sK5),sK6,sK7) = k2_tarski(sK6,sK7)
    | v1_xboole_0(u1_struct_0(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2780,c_5246])).

cnf(c_5780,plain,
    ( k7_domain_1(u1_struct_0(sK5),sK6,sK7) = k2_tarski(sK6,sK7)
    | v1_xboole_0(u1_orders_2(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5620,c_4485])).

cnf(c_2111,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3321,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k2_tarski(X2,X3))
    | X0 != X2
    | X1 != k2_tarski(X2,X3) ),
    inference(instantiation,[status(thm)],[c_2111])).

cnf(c_3916,plain,
    ( r2_hidden(X0,k7_domain_1(u1_struct_0(sK5),sK6,sK7))
    | ~ r2_hidden(sK6,k2_tarski(sK6,sK7))
    | X0 != sK6
    | k7_domain_1(u1_struct_0(sK5),sK6,sK7) != k2_tarski(sK6,sK7) ),
    inference(instantiation,[status(thm)],[c_3321])).

cnf(c_5997,plain,
    ( r2_hidden(sK6,k7_domain_1(u1_struct_0(sK5),sK6,sK7))
    | ~ r2_hidden(sK6,k2_tarski(sK6,sK7))
    | k7_domain_1(u1_struct_0(sK5),sK6,sK7) != k2_tarski(sK6,sK7)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_3916])).

cnf(c_5998,plain,
    ( k7_domain_1(u1_struct_0(sK5),sK6,sK7) != k2_tarski(sK6,sK7)
    | sK6 != sK6
    | r2_hidden(sK6,k7_domain_1(u1_struct_0(sK5),sK6,sK7)) = iProver_top
    | r2_hidden(sK6,k2_tarski(sK6,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5997])).

cnf(c_3316,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k2_tarski(X3,X2))
    | X0 != X2
    | X1 != k2_tarski(X3,X2) ),
    inference(instantiation,[status(thm)],[c_2111])).

cnf(c_3911,plain,
    ( r2_hidden(X0,k7_domain_1(u1_struct_0(sK5),sK6,sK7))
    | ~ r2_hidden(sK7,k2_tarski(sK6,sK7))
    | X0 != sK7
    | k7_domain_1(u1_struct_0(sK5),sK6,sK7) != k2_tarski(sK6,sK7) ),
    inference(instantiation,[status(thm)],[c_3316])).

cnf(c_6449,plain,
    ( r2_hidden(sK7,k7_domain_1(u1_struct_0(sK5),sK6,sK7))
    | ~ r2_hidden(sK7,k2_tarski(sK6,sK7))
    | k7_domain_1(u1_struct_0(sK5),sK6,sK7) != k2_tarski(sK6,sK7)
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_3911])).

cnf(c_6450,plain,
    ( k7_domain_1(u1_struct_0(sK5),sK6,sK7) != k2_tarski(sK6,sK7)
    | sK7 != sK7
    | r2_hidden(sK7,k7_domain_1(u1_struct_0(sK5),sK6,sK7)) = iProver_top
    | r2_hidden(sK7,k2_tarski(sK6,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6449])).

cnf(c_23,plain,
    ( r3_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_743,plain,
    ( r3_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_42])).

cnf(c_744,plain,
    ( r3_orders_2(sK5,X0,X1)
    | ~ r1_orders_2(sK5,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | v2_struct_0(sK5)
    | ~ l1_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_743])).

cnf(c_748,plain,
    ( v2_struct_0(sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r1_orders_2(sK5,X0,X1)
    | r3_orders_2(sK5,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_744,c_41])).

cnf(c_749,plain,
    ( r3_orders_2(sK5,X0,X1)
    | ~ r1_orders_2(sK5,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | v2_struct_0(sK5) ),
    inference(renaming,[status(thm)],[c_748])).

cnf(c_920,plain,
    ( r3_orders_2(sK5,X0,X1)
    | ~ r1_orders_2(sK5,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | v1_xboole_0(u1_struct_0(sK5)) ),
    inference(resolution,[status(thm)],[c_749,c_815])).

cnf(c_2774,plain,
    ( r3_orders_2(sK5,X0,X1) = iProver_top
    | r1_orders_2(sK5,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_920])).

cnf(c_921,plain,
    ( r3_orders_2(sK5,X0,X1) = iProver_top
    | r1_orders_2(sK5,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_920])).

cnf(c_6126,plain,
    ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r1_orders_2(sK5,X0,X1) != iProver_top
    | r3_orders_2(sK5,X0,X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2774,c_921,c_3496,c_4485])).

cnf(c_6127,plain,
    ( r3_orders_2(sK5,X0,X1) = iProver_top
    | r1_orders_2(sK5,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6126])).

cnf(c_6136,plain,
    ( r3_orders_2(sK5,X0,sK7) = iProver_top
    | r1_orders_2(sK5,X0,sK7) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2781,c_6127])).

cnf(c_6507,plain,
    ( r3_orders_2(sK5,sK6,sK7) = iProver_top
    | r1_orders_2(sK5,sK6,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2780,c_6136])).

cnf(c_7196,plain,
    ( ~ r1_orders_2(sK5,sK6,sK7)
    | ~ r2_hidden(sK6,k7_domain_1(u1_struct_0(sK5),sK6,sK7))
    | ~ r2_hidden(sK7,k7_domain_1(u1_struct_0(sK5),sK6,sK7))
    | ~ v6_orders_2(k7_domain_1(u1_struct_0(sK5),sK6,sK7),sK5)
    | ~ m1_subset_1(k7_domain_1(u1_struct_0(sK5),sK6,sK7),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_1202])).

cnf(c_7209,plain,
    ( r1_orders_2(sK5,sK6,sK7) != iProver_top
    | r2_hidden(sK6,k7_domain_1(u1_struct_0(sK5),sK6,sK7)) != iProver_top
    | r2_hidden(sK7,k7_domain_1(u1_struct_0(sK5),sK6,sK7)) != iProver_top
    | v6_orders_2(k7_domain_1(u1_struct_0(sK5),sK6,sK7),sK5) != iProver_top
    | m1_subset_1(k7_domain_1(u1_struct_0(sK5),sK6,sK7),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7196])).

cnf(c_7463,plain,
    ( r1_orders_2(sK5,sK6,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5443,c_45,c_46,c_3578,c_3599,c_3679,c_3727,c_3987,c_4293,c_4375,c_4485,c_5780,c_5998,c_6450,c_6507,c_7209])).

cnf(c_35,plain,
    ( ~ sP0(X0,X1,X2)
    | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1097,plain,
    ( r1_orders_2(sK5,sK6,sK7)
    | r1_orders_2(sK5,sK7,sK6)
    | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
    | sK5 != X2
    | sK6 != X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_38])).

cnf(c_1098,plain,
    ( r1_orders_2(sK5,sK6,sK7)
    | r1_orders_2(sK5,sK7,sK6)
    | m1_subset_1(sK4(sK6,sK7,sK5),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(unflattening,[status(thm)],[c_1097])).

cnf(c_2767,plain,
    ( r1_orders_2(sK5,sK6,sK7) = iProver_top
    | r1_orders_2(sK5,sK7,sK6) = iProver_top
    | m1_subset_1(sK4(sK6,sK7,sK5),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1098])).

cnf(c_4,plain,
    ( r7_relat_2(u1_orders_2(X0),X1)
    | ~ v6_orders_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_867,plain,
    ( r7_relat_2(u1_orders_2(X0),X1)
    | ~ v6_orders_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_41])).

cnf(c_868,plain,
    ( r7_relat_2(u1_orders_2(sK5),X0)
    | ~ v6_orders_2(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(unflattening,[status(thm)],[c_867])).

cnf(c_2776,plain,
    ( r7_relat_2(u1_orders_2(sK5),X0) = iProver_top
    | v6_orders_2(X0,sK5) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_868])).

cnf(c_3776,plain,
    ( r1_orders_2(sK5,sK6,sK7) = iProver_top
    | r1_orders_2(sK5,sK7,sK6) = iProver_top
    | r7_relat_2(u1_orders_2(sK5),sK4(sK6,sK7,sK5)) = iProver_top
    | v6_orders_2(sK4(sK6,sK7,sK5),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2767,c_2776])).

cnf(c_36,plain,
    ( ~ sP0(X0,X1,X2)
    | v6_orders_2(sK4(X0,X1,X2),X2) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1063,plain,
    ( r1_orders_2(sK5,sK6,sK7)
    | r1_orders_2(sK5,sK7,sK6)
    | v6_orders_2(sK4(X0,X1,X2),X2)
    | sK5 != X2
    | sK6 != X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_38])).

cnf(c_1064,plain,
    ( r1_orders_2(sK5,sK6,sK7)
    | r1_orders_2(sK5,sK7,sK6)
    | v6_orders_2(sK4(sK6,sK7,sK5),sK5) ),
    inference(unflattening,[status(thm)],[c_1063])).

cnf(c_1065,plain,
    ( r1_orders_2(sK5,sK6,sK7) = iProver_top
    | r1_orders_2(sK5,sK7,sK6) = iProver_top
    | v6_orders_2(sK4(sK6,sK7,sK5),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1064])).

cnf(c_4641,plain,
    ( r7_relat_2(u1_orders_2(sK5),sK4(sK6,sK7,sK5)) = iProver_top
    | r1_orders_2(sK5,sK7,sK6) = iProver_top
    | r1_orders_2(sK5,sK6,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3776,c_1065])).

cnf(c_4642,plain,
    ( r1_orders_2(sK5,sK6,sK7) = iProver_top
    | r1_orders_2(sK5,sK7,sK6) = iProver_top
    | r7_relat_2(u1_orders_2(sK5),sK4(sK6,sK7,sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4641])).

cnf(c_34,plain,
    ( ~ sP0(X0,X1,X2)
    | r2_hidden(X0,sK4(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1131,plain,
    ( r1_orders_2(sK5,sK6,sK7)
    | r1_orders_2(sK5,sK7,sK6)
    | r2_hidden(X0,sK4(X0,X1,X2))
    | sK5 != X2
    | sK6 != X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_38])).

cnf(c_1132,plain,
    ( r1_orders_2(sK5,sK6,sK7)
    | r1_orders_2(sK5,sK7,sK6)
    | r2_hidden(sK6,sK4(sK6,sK7,sK5)) ),
    inference(unflattening,[status(thm)],[c_1131])).

cnf(c_2765,plain,
    ( r1_orders_2(sK5,sK6,sK7) = iProver_top
    | r1_orders_2(sK5,sK7,sK6) = iProver_top
    | r2_hidden(sK6,sK4(sK6,sK7,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1132])).

cnf(c_6252,plain,
    ( r1_orders_2(sK5,sK6,sK7) = iProver_top
    | r1_orders_2(sK5,sK7,sK6) = iProver_top
    | r2_hidden(X0,sK4(sK6,sK7,sK5)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK6),X1) = iProver_top
    | r2_hidden(k4_tarski(sK6,X0),X1) = iProver_top
    | r7_relat_2(X1,sK4(sK6,sK7,sK5)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2765,c_2785])).

cnf(c_10317,plain,
    ( r1_orders_2(sK5,sK7,sK6) = iProver_top
    | r2_hidden(X0,sK4(sK6,sK7,sK5)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK6),X1) = iProver_top
    | r2_hidden(k4_tarski(sK6,X0),X1) = iProver_top
    | r7_relat_2(X1,sK4(sK6,sK7,sK5)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6252,c_45,c_46,c_3578,c_3599,c_3679,c_3727,c_3987,c_4293,c_4375,c_4485,c_5780,c_5998,c_6450,c_6507,c_7209])).

cnf(c_10333,plain,
    ( r1_orders_2(sK5,sK6,sK7) = iProver_top
    | r1_orders_2(sK5,sK7,sK6) = iProver_top
    | r2_hidden(k4_tarski(sK6,sK7),X0) = iProver_top
    | r2_hidden(k4_tarski(sK7,sK6),X0) = iProver_top
    | r7_relat_2(X0,sK4(sK6,sK7,sK5)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2763,c_10317])).

cnf(c_10702,plain,
    ( r1_orders_2(sK5,sK7,sK6) = iProver_top
    | r2_hidden(k4_tarski(sK6,sK7),X0) = iProver_top
    | r2_hidden(k4_tarski(sK7,sK6),X0) = iProver_top
    | r7_relat_2(X0,sK4(sK6,sK7,sK5)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10333,c_45,c_46,c_3578,c_3599,c_3679,c_3727,c_3987,c_4293,c_4375,c_4485,c_5780,c_5998,c_6450,c_6507,c_7209])).

cnf(c_10714,plain,
    ( r1_orders_2(sK5,sK6,sK7) = iProver_top
    | r1_orders_2(sK5,sK7,sK6) = iProver_top
    | r2_hidden(k4_tarski(sK6,sK7),u1_orders_2(sK5)) = iProver_top
    | r2_hidden(k4_tarski(sK7,sK6),u1_orders_2(sK5)) = iProver_top
    | v1_relat_1(u1_orders_2(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4642,c_10702])).

cnf(c_10951,plain,
    ( r1_orders_2(sK5,sK7,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6253,c_44,c_45,c_46,c_93,c_3290,c_3433,c_3520,c_3578,c_3599,c_3679,c_3727,c_3987,c_4293,c_4375,c_4485,c_5780,c_5998,c_6450,c_6507,c_7209,c_10714])).

cnf(c_10953,plain,
    ( r1_orders_2(sK5,sK7,sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_10951])).

cnf(c_31,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r1_orders_2(X2,X1,X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1224,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r2_hidden(sK6,X3)
    | ~ r2_hidden(sK7,X3)
    | ~ v6_orders_2(X3,sK5)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK5)))
    | sK5 != X0
    | sK6 != X2
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_37])).

cnf(c_1225,plain,
    ( ~ r1_orders_2(sK5,sK7,sK6)
    | ~ r2_hidden(sK6,X0)
    | ~ r2_hidden(sK7,X0)
    | ~ v6_orders_2(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(unflattening,[status(thm)],[c_1224])).

cnf(c_7195,plain,
    ( ~ r1_orders_2(sK5,sK7,sK6)
    | ~ r2_hidden(sK6,k7_domain_1(u1_struct_0(sK5),sK6,sK7))
    | ~ r2_hidden(sK7,k7_domain_1(u1_struct_0(sK5),sK6,sK7))
    | ~ v6_orders_2(k7_domain_1(u1_struct_0(sK5),sK6,sK7),sK5)
    | ~ m1_subset_1(k7_domain_1(u1_struct_0(sK5),sK6,sK7),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_1225])).

cnf(c_6137,plain,
    ( r3_orders_2(sK5,X0,sK6) = iProver_top
    | r1_orders_2(sK5,X0,sK6) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2780,c_6127])).

cnf(c_6664,plain,
    ( r3_orders_2(sK5,sK7,sK6) = iProver_top
    | r1_orders_2(sK5,sK7,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2781,c_6137])).

cnf(c_6674,plain,
    ( r3_orders_2(sK5,sK7,sK6)
    | ~ r1_orders_2(sK5,sK7,sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6664])).

cnf(c_4486,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK5))
    | v1_xboole_0(u1_orders_2(sK5)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4485])).

cnf(c_4096,plain,
    ( r1_orders_2(sK5,X0,sK6) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | v1_xboole_0(u1_orders_2(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2780,c_3496])).

cnf(c_4361,plain,
    ( r1_orders_2(sK5,sK7,sK6) != iProver_top
    | v1_xboole_0(u1_orders_2(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2781,c_4096])).

cnf(c_4371,plain,
    ( ~ r1_orders_2(sK5,sK7,sK6)
    | ~ v1_xboole_0(u1_orders_2(sK5)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4361])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11573,c_10953,c_10951,c_7195,c_6674,c_6449,c_5997,c_5780,c_4486,c_4374,c_4371,c_4361,c_3726,c_3676,c_3599,c_3578,c_39,c_40])).


%------------------------------------------------------------------------------
