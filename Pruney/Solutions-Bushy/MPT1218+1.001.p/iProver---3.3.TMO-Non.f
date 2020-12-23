%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1218+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:11 EST 2020

% Result     : Timeout 59.17s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  242 (1228 expanded)
%              Number of clauses        :  146 ( 343 expanded)
%              Number of leaves         :   29 ( 262 expanded)
%              Depth                    :   22
%              Number of atoms          : 1226 (8169 expanded)
%              Number of equality atoms :  153 ( 662 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   16 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v19_lattices(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r2_hidden(X2,X1)
                        & r3_lattices(X0,X2,X3) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v19_lattices(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ r3_lattices(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v19_lattices(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ r3_lattices(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v19_lattices(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r2_hidden(X2,X1)
                      & r3_lattices(X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(X3,X1)
                      | ~ r2_hidden(X2,X1)
                      | ~ r3_lattices(X0,X2,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v19_lattices(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v19_lattices(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r2_hidden(X2,X1)
                      & r3_lattices(X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r2_hidden(X4,X1)
                      | ~ r3_lattices(X0,X4,X5)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v19_lattices(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f58])).

fof(f61,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r2_hidden(X2,X1)
          & r3_lattices(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(X2,X1)
        & r3_lattices(X0,X2,sK3(X0,X1))
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & r2_hidden(X2,X1)
              & r3_lattices(X0,X2,X3)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & r2_hidden(sK2(X0,X1),X1)
            & r3_lattices(X0,sK2(X0,X1),X3)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v19_lattices(X1,X0)
              | ( ~ r2_hidden(sK3(X0,X1),X1)
                & r2_hidden(sK2(X0,X1),X1)
                & r3_lattices(X0,sK2(X0,X1),sK3(X0,X1))
                & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r2_hidden(X4,X1)
                      | ~ r3_lattices(X0,X4,X5)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v19_lattices(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f59,f61,f60])).

fof(f84,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ r3_lattices(X0,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v19_lattices(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v19_lattices(X1,X0)
            & v18_lattices(X1,X0)
            & ~ v1_xboole_0(X1) )
         => k2_struct_0(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v19_lattices(X1,X0)
              & v18_lattices(X1,X0)
              & ~ v1_xboole_0(X1) )
           => k2_struct_0(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_struct_0(X0) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v19_lattices(X1,X0)
          & v18_lattices(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_struct_0(X0) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v19_lattices(X1,X0)
          & v18_lattices(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f71,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k2_struct_0(X0) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v19_lattices(X1,X0)
          & v18_lattices(X1,X0)
          & ~ v1_xboole_0(X1) )
     => ( k2_struct_0(X0) != sK7
        & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0)))
        & v19_lattices(sK7,X0)
        & v18_lattices(sK7,X0)
        & ~ v1_xboole_0(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_struct_0(X0) != X1
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v19_lattices(X1,X0)
            & v18_lattices(X1,X0)
            & ~ v1_xboole_0(X1) )
        & l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k2_struct_0(sK6) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
          & v19_lattices(X1,sK6)
          & v18_lattices(X1,sK6)
          & ~ v1_xboole_0(X1) )
      & l3_lattices(sK6)
      & v10_lattices(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,
    ( k2_struct_0(sK6) != sK7
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    & v19_lattices(sK7,sK6)
    & v18_lattices(sK7,sK6)
    & ~ v1_xboole_0(sK7)
    & l3_lattices(sK6)
    & v10_lattices(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f52,f71,f70])).

fof(f108,plain,(
    v10_lattices(sK6) ),
    inference(cnf_transformation,[],[f72])).

fof(f107,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f72])).

fof(f109,plain,(
    l3_lattices(sK6) ),
    inference(cnf_transformation,[],[f72])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f45])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v18_lattices(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r2_hidden(X3,X1)
                        & r3_lattices(X0,X2,X3) )
                     => r2_hidden(X2,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v18_lattices(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X2,X1)
                    | ~ r2_hidden(X3,X1)
                    | ~ r3_lattices(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v18_lattices(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X2,X1)
                    | ~ r2_hidden(X3,X1)
                    | ~ r3_lattices(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v18_lattices(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X2,X1)
                      & r2_hidden(X3,X1)
                      & r3_lattices(X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(X2,X1)
                      | ~ r2_hidden(X3,X1)
                      | ~ r3_lattices(X0,X2,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v18_lattices(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v18_lattices(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X2,X1)
                      & r2_hidden(X3,X1)
                      & r3_lattices(X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X4,X1)
                      | ~ r2_hidden(X5,X1)
                      | ~ r3_lattices(X0,X4,X5)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v18_lattices(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f53])).

fof(f56,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X3,X1)
          & r3_lattices(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(X2,X1)
        & r2_hidden(sK1(X0,X1),X1)
        & r3_lattices(X0,X2,sK1(X0,X1))
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X2,X1)
              & r2_hidden(X3,X1)
              & r3_lattices(X0,X2,X3)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(sK0(X0,X1),X1)
            & r2_hidden(X3,X1)
            & r3_lattices(X0,sK0(X0,X1),X3)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v18_lattices(X1,X0)
              | ( ~ r2_hidden(sK0(X0,X1),X1)
                & r2_hidden(sK1(X0,X1),X1)
                & r3_lattices(X0,sK0(X0,X1),sK1(X0,X1))
                & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X4,X1)
                      | ~ r2_hidden(X5,X1)
                      | ~ r3_lattices(X0,X4,X5)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v18_lattices(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f54,f56,f55])).

fof(f78,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X5,X1)
      | ~ r3_lattices(X0,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v18_lattices(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f10,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f10,f63])).

fof(f95,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f64])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f43])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f113,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f72])).

fof(f1,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f23,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f22])).

fof(f24,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f23])).

fof(f25,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f26,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f25])).

fof(f74,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l1_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f38,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f94,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f110,plain,(
    ~ v1_xboole_0(sK7) ),
    inference(cnf_transformation,[],[f72])).

fof(f76,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_lattices(X0,X1,X2)
          | ~ r1_lattices(X0,X1,X2) )
        & ( r1_lattices(X0,X1,X2)
          | ~ r3_lattices(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,X2)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f75,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => r1_lattices(X0,k4_lattices(X0,X1,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f112,plain,(
    v19_lattices(sK7,sK6) ),
    inference(cnf_transformation,[],[f72])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f49])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,X1) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,X1) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f66])).

fof(f68,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X2)
            | ~ r2_hidden(X3,X1) )
          & ( r2_hidden(X3,X2)
            | r2_hidden(X3,X1) )
          & m1_subset_1(X3,X0) )
     => ( ( ~ r2_hidden(sK5(X0,X1,X2),X2)
          | ~ r2_hidden(sK5(X0,X1,X2),X1) )
        & ( r2_hidden(sK5(X0,X1,X2),X2)
          | r2_hidden(sK5(X0,X1,X2),X1) )
        & m1_subset_1(sK5(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ( ( ~ r2_hidden(sK5(X0,X1,X2),X2)
              | ~ r2_hidden(sK5(X0,X1,X2),X1) )
            & ( r2_hidden(sK5(X0,X1,X2),X2)
              | r2_hidden(sK5(X0,X1,X2),X1) )
            & m1_subset_1(sK5(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f67,f68])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r2_hidden(sK5(X0,X1,X2),X2)
      | ~ r2_hidden(sK5(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | m1_subset_1(sK5(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f90,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f91,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_lattices(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_lattices(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f93,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f114,plain,(
    k2_struct_0(sK6) != sK7 ),
    inference(cnf_transformation,[],[f72])).

fof(f111,plain,(
    v18_lattices(sK7,sK6) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_16,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | ~ v19_lattices(X3,X0)
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_40,negated_conjecture,
    ( v10_lattices(sK6) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1359,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | ~ v19_lattices(X3,X0)
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_40])).

cnf(c_1360,plain,
    ( ~ r3_lattices(sK6,X0,X1)
    | ~ v19_lattices(X2,sK6)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ l3_lattices(sK6)
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_1359])).

cnf(c_41,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_39,negated_conjecture,
    ( l3_lattices(sK6) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1362,plain,
    ( ~ r3_lattices(sK6,X0,X1)
    | ~ v19_lattices(X2,sK6)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1360,c_41,c_39])).

cnf(c_1363,plain,
    ( ~ r3_lattices(sK6,X0,X1)
    | ~ v19_lattices(X2,sK6)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_1362])).

cnf(c_28,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1380,plain,
    ( ~ r3_lattices(sK6,X0,X1)
    | ~ v19_lattices(X2,sK6)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1363,c_28])).

cnf(c_172708,plain,
    ( ~ r3_lattices(sK6,X0,X1)
    | ~ v19_lattices(sK7,sK6)
    | ~ r2_hidden(X0,sK7)
    | r2_hidden(X1,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_1380])).

cnf(c_210263,plain,
    ( ~ r3_lattices(sK6,k4_lattices(sK6,sK4(u1_struct_0(sK6)),sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6))),X0)
    | ~ v19_lattices(sK7,sK6)
    | r2_hidden(X0,sK7)
    | ~ r2_hidden(k4_lattices(sK6,sK4(u1_struct_0(sK6)),sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6))),sK7)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_172708])).

cnf(c_238186,plain,
    ( ~ r3_lattices(sK6,k4_lattices(sK6,sK4(u1_struct_0(sK6)),sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6))),sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6)))
    | ~ v19_lattices(sK7,sK6)
    | r2_hidden(sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6)),sK7)
    | ~ r2_hidden(k4_lattices(sK6,sK4(u1_struct_0(sK6)),sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6))),sK7)
    | ~ m1_subset_1(sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6)),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_210263])).

cnf(c_10,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(X1,X3)
    | ~ v18_lattices(X3,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1409,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(X1,X3)
    | ~ v18_lattices(X3,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_40])).

cnf(c_1410,plain,
    ( ~ r3_lattices(sK6,X0,X1)
    | ~ r2_hidden(X1,X2)
    | r2_hidden(X0,X2)
    | ~ v18_lattices(X2,sK6)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ l3_lattices(sK6)
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_1409])).

cnf(c_1412,plain,
    ( ~ r3_lattices(sK6,X0,X1)
    | ~ r2_hidden(X1,X2)
    | r2_hidden(X0,X2)
    | ~ v18_lattices(X2,sK6)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1410,c_41,c_39])).

cnf(c_1413,plain,
    ( ~ r3_lattices(sK6,X0,X1)
    | ~ r2_hidden(X1,X2)
    | r2_hidden(X0,X2)
    | ~ v18_lattices(X2,sK6)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_1412])).

cnf(c_1430,plain,
    ( ~ r3_lattices(sK6,X0,X1)
    | ~ r2_hidden(X1,X2)
    | r2_hidden(X0,X2)
    | ~ v18_lattices(X2,sK6)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1413,c_28])).

cnf(c_172711,plain,
    ( ~ r3_lattices(sK6,X0,X1)
    | ~ r2_hidden(X1,sK7)
    | r2_hidden(X0,sK7)
    | ~ v18_lattices(sK7,sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_1430])).

cnf(c_181075,plain,
    ( ~ r3_lattices(sK6,X0,sK4(u1_struct_0(sK6)))
    | r2_hidden(X0,sK7)
    | ~ r2_hidden(sK4(u1_struct_0(sK6)),sK7)
    | ~ v18_lattices(sK7,sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_172711])).

cnf(c_191194,plain,
    ( ~ r3_lattices(sK6,k4_lattices(sK6,sK4(u1_struct_0(sK6)),sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6))),sK4(u1_struct_0(sK6)))
    | r2_hidden(k4_lattices(sK6,sK4(u1_struct_0(sK6)),sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6))),sK7)
    | ~ r2_hidden(sK4(u1_struct_0(sK6)),sK7)
    | ~ v18_lattices(sK7,sK6)
    | ~ m1_subset_1(k4_lattices(sK6,sK4(u1_struct_0(sK6)),sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6))),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_181075])).

cnf(c_22,plain,
    ( m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_3593,plain,
    ( m1_subset_1(sK4(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_27,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_3591,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4143,plain,
    ( r2_hidden(sK4(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3593,c_3591])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_3584,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_3590,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4746,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3584,c_3590])).

cnf(c_2,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_21,plain,
    ( l1_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_593,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X3)
    | v2_struct_0(X1)
    | X1 != X3
    | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
    inference(resolution_lifted,[status(thm)],[c_21,c_4])).

cnf(c_594,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
    inference(unflattening,[status(thm)],[c_593])).

cnf(c_753,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X3)
    | ~ l3_lattices(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ v10_lattices(X3)
    | X1 != X3
    | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
    inference(resolution_lifted,[status(thm)],[c_2,c_594])).

cnf(c_754,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
    inference(unflattening,[status(thm)],[c_753])).

cnf(c_1522,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X2,X0) = k4_lattices(X1,X0,X2)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_754,c_40])).

cnf(c_1523,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ l3_lattices(sK6)
    | v2_struct_0(sK6)
    | k4_lattices(sK6,X0,X1) = k4_lattices(sK6,X1,X0) ),
    inference(unflattening,[status(thm)],[c_1522])).

cnf(c_1527,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | k4_lattices(sK6,X0,X1) = k4_lattices(sK6,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1523,c_41,c_39])).

cnf(c_1528,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | k4_lattices(sK6,X1,X0) = k4_lattices(sK6,X0,X1) ),
    inference(renaming,[status(thm)],[c_1527])).

cnf(c_3572,plain,
    ( k4_lattices(sK6,X0,X1) = k4_lattices(sK6,X1,X0)
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1528])).

cnf(c_4244,plain,
    ( k4_lattices(sK6,sK4(u1_struct_0(sK6)),X0) = k4_lattices(sK6,X0,sK4(u1_struct_0(sK6)))
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3593,c_3572])).

cnf(c_6189,plain,
    ( k4_lattices(sK6,sK4(u1_struct_0(sK6)),X0) = k4_lattices(sK6,X0,sK4(u1_struct_0(sK6)))
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_4746,c_4244])).

cnf(c_6359,plain,
    ( k4_lattices(sK6,sK4(sK7),sK4(u1_struct_0(sK6))) = k4_lattices(sK6,sK4(u1_struct_0(sK6)),sK4(sK7))
    | v1_xboole_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_4143,c_6189])).

cnf(c_38,negated_conjecture,
    ( ~ v1_xboole_0(sK7) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_45,plain,
    ( v1_xboole_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_73686,plain,
    ( k4_lattices(sK6,sK4(sK7),sK4(u1_struct_0(sK6))) = k4_lattices(sK6,sK4(u1_struct_0(sK6)),sK4(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6359,c_45])).

cnf(c_0,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_24,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_669,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(resolution,[status(thm)],[c_0,c_24])).

cnf(c_1,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_673,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_669,c_24,c_2,c_1,c_0])).

cnf(c_26,plain,
    ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_717,plain,
    ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(resolution,[status(thm)],[c_1,c_26])).

cnf(c_721,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_717,c_2])).

cnf(c_722,plain,
    ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(renaming,[status(thm)],[c_721])).

cnf(c_816,plain,
    ( r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X5,u1_struct_0(X4))
    | ~ l3_lattices(X0)
    | ~ l3_lattices(X4)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ v10_lattices(X0)
    | ~ v10_lattices(X4)
    | X5 != X2
    | X4 != X0
    | k4_lattices(X4,X5,X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_673,c_722])).

cnf(c_817,plain,
    ( r3_lattices(X0,k4_lattices(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(unflattening,[status(thm)],[c_816])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k4_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_569,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k4_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X3)
    | v2_struct_0(X1)
    | X1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_19])).

cnf(c_570,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k4_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_569])).

cnf(c_777,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k4_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ l3_lattices(X3)
    | ~ l3_lattices(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ v10_lattices(X3)
    | X1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_570])).

cnf(c_778,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k4_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1) ),
    inference(unflattening,[status(thm)],[c_777])).

cnf(c_835,plain,
    ( r3_lattices(X0,k4_lattices(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_817,c_778])).

cnf(c_1338,plain,
    ( r3_lattices(X0,k4_lattices(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_835,c_40])).

cnf(c_1339,plain,
    ( r3_lattices(sK6,k4_lattices(sK6,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ l3_lattices(sK6)
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_1338])).

cnf(c_1343,plain,
    ( r3_lattices(sK6,k4_lattices(sK6,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1339,c_41,c_39])).

cnf(c_1344,plain,
    ( r3_lattices(sK6,k4_lattices(sK6,X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_1343])).

cnf(c_3580,plain,
    ( r3_lattices(sK6,k4_lattices(sK6,X0,X1),X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1344])).

cnf(c_3579,plain,
    ( r3_lattices(sK6,X0,X1) != iProver_top
    | v19_lattices(X2,sK6) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1380])).

cnf(c_6688,plain,
    ( r3_lattices(sK6,X0,X1) != iProver_top
    | v19_lattices(sK7,sK6) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK7) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3584,c_3579])).

cnf(c_36,negated_conjecture,
    ( v19_lattices(sK7,sK6) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1265,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK7 != X3
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_36])).

cnf(c_1266,plain,
    ( ~ r3_lattices(sK6,X0,X1)
    | ~ r2_hidden(X0,sK7)
    | r2_hidden(X1,sK7)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ l3_lattices(sK6)
    | v2_struct_0(sK6)
    | ~ v10_lattices(sK6) ),
    inference(unflattening,[status(thm)],[c_1265])).

cnf(c_1268,plain,
    ( ~ r3_lattices(sK6,X0,X1)
    | ~ r2_hidden(X0,sK7)
    | r2_hidden(X1,sK7)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1266,c_41,c_40,c_39,c_35])).

cnf(c_1269,plain,
    ( ~ r3_lattices(sK6,X0,X1)
    | ~ r2_hidden(X0,sK7)
    | r2_hidden(X1,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_1268])).

cnf(c_1270,plain,
    ( r3_lattices(sK6,X0,X1) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK7) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1269])).

cnf(c_7236,plain,
    ( r3_lattices(sK6,X0,X1) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK7) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6688,c_1270,c_4746])).

cnf(c_7244,plain,
    ( r2_hidden(X0,sK7) = iProver_top
    | r2_hidden(k4_lattices(sK6,X0,X1),sK7) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3580,c_7236])).

cnf(c_73692,plain,
    ( r2_hidden(k4_lattices(sK6,sK4(sK7),sK4(u1_struct_0(sK6))),sK7) != iProver_top
    | r2_hidden(sK4(u1_struct_0(sK6)),sK7) = iProver_top
    | m1_subset_1(sK4(u1_struct_0(sK6)),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK4(sK7),u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_73686,c_7244])).

cnf(c_73725,plain,
    ( ~ r2_hidden(k4_lattices(sK6,sK4(sK7),sK4(u1_struct_0(sK6))),sK7)
    | r2_hidden(sK4(u1_struct_0(sK6)),sK7)
    | ~ m1_subset_1(sK4(u1_struct_0(sK6)),u1_struct_0(sK6))
    | ~ m1_subset_1(sK4(sK7),u1_struct_0(sK6)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_73692])).

cnf(c_3057,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | r3_lattices(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_5102,plain,
    ( r3_lattices(X0,X1,X2)
    | ~ r3_lattices(sK6,k4_lattices(sK6,sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6)),sK4(u1_struct_0(sK6))),sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6)))
    | X2 != sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6))
    | X1 != k4_lattices(sK6,sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6)),sK4(u1_struct_0(sK6)))
    | X0 != sK6 ),
    inference(instantiation,[status(thm)],[c_3057])).

cnf(c_20113,plain,
    ( r3_lattices(X0,X1,sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6)))
    | ~ r3_lattices(sK6,k4_lattices(sK6,sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6)),sK4(u1_struct_0(sK6))),sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6)))
    | X1 != k4_lattices(sK6,sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6)),sK4(u1_struct_0(sK6)))
    | X0 != sK6
    | sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6)) != sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_5102])).

cnf(c_67883,plain,
    ( r3_lattices(X0,k4_lattices(sK6,sK4(u1_struct_0(sK6)),sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6))),sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6)))
    | ~ r3_lattices(sK6,k4_lattices(sK6,sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6)),sK4(u1_struct_0(sK6))),sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6)))
    | X0 != sK6
    | sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6)) != sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6))
    | k4_lattices(sK6,sK4(u1_struct_0(sK6)),sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6))) != k4_lattices(sK6,sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6)),sK4(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_20113])).

cnf(c_67885,plain,
    ( ~ r3_lattices(sK6,k4_lattices(sK6,sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6)),sK4(u1_struct_0(sK6))),sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6)))
    | r3_lattices(sK6,k4_lattices(sK6,sK4(u1_struct_0(sK6)),sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6))),sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6)))
    | sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6)) != sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6))
    | k4_lattices(sK6,sK4(u1_struct_0(sK6)),sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6))) != k4_lattices(sK6,sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6)),sK4(u1_struct_0(sK6)))
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_67883])).

cnf(c_24009,plain,
    ( ~ m1_subset_1(sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6)),u1_struct_0(sK6))
    | ~ m1_subset_1(sK4(u1_struct_0(sK6)),u1_struct_0(sK6))
    | k4_lattices(sK6,sK4(u1_struct_0(sK6)),sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6))) = k4_lattices(sK6,sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6)),sK4(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_1528])).

cnf(c_11891,plain,
    ( r2_hidden(sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6)),k2_struct_0(sK6))
    | ~ m1_subset_1(sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6)),k2_struct_0(sK6))
    | v1_xboole_0(k2_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_3880,plain,
    ( ~ r3_lattices(sK6,X0,X1)
    | ~ r2_hidden(X1,sK7)
    | r2_hidden(X0,sK7)
    | ~ v18_lattices(sK7,sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_1430])).

cnf(c_5129,plain,
    ( ~ r3_lattices(sK6,X0,sK4(sK7))
    | r2_hidden(X0,sK7)
    | ~ r2_hidden(sK4(sK7),sK7)
    | ~ v18_lattices(sK7,sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_3880])).

cnf(c_10009,plain,
    ( ~ r3_lattices(sK6,k4_lattices(sK6,sK4(sK7),sK4(u1_struct_0(sK6))),sK4(sK7))
    | r2_hidden(k4_lattices(sK6,sK4(sK7),sK4(u1_struct_0(sK6))),sK7)
    | ~ r2_hidden(sK4(sK7),sK7)
    | ~ v18_lattices(sK7,sK6)
    | ~ m1_subset_1(k4_lattices(sK6,sK4(sK7),sK4(u1_struct_0(sK6))),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_5129])).

cnf(c_3047,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_6897,plain,
    ( sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6)) = sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_3047])).

cnf(c_3051,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_4557,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6)),u1_struct_0(sK6))
    | X0 != sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6))
    | X1 != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_3051])).

cnf(c_5363,plain,
    ( m1_subset_1(X0,k2_struct_0(sK6))
    | ~ m1_subset_1(sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6)),u1_struct_0(sK6))
    | X0 != sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6))
    | k2_struct_0(sK6) != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_4557])).

cnf(c_6896,plain,
    ( m1_subset_1(sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6)),k2_struct_0(sK6))
    | ~ m1_subset_1(sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6)),u1_struct_0(sK6))
    | sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6)) != sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6))
    | k2_struct_0(sK6) != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_5363])).

cnf(c_1501,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k4_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_778,c_40])).

cnf(c_1502,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | m1_subset_1(k4_lattices(sK6,X0,X1),u1_struct_0(sK6))
    | ~ l3_lattices(sK6)
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_1501])).

cnf(c_1506,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | m1_subset_1(k4_lattices(sK6,X0,X1),u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1502,c_41,c_39])).

cnf(c_1507,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | m1_subset_1(k4_lattices(sK6,X1,X0),u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_1506])).

cnf(c_4195,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | m1_subset_1(k4_lattices(sK6,X0,sK4(u1_struct_0(sK6))),u1_struct_0(sK6))
    | ~ m1_subset_1(sK4(u1_struct_0(sK6)),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_1507])).

cnf(c_6827,plain,
    ( m1_subset_1(k4_lattices(sK6,sK4(sK7),sK4(u1_struct_0(sK6))),u1_struct_0(sK6))
    | ~ m1_subset_1(sK4(u1_struct_0(sK6)),u1_struct_0(sK6))
    | ~ m1_subset_1(sK4(sK7),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_4195])).

cnf(c_3884,plain,
    ( r3_lattices(sK6,k4_lattices(sK6,X0,sK4(u1_struct_0(sK6))),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(sK4(u1_struct_0(sK6)),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_1344])).

cnf(c_6828,plain,
    ( r3_lattices(sK6,k4_lattices(sK6,sK4(sK7),sK4(u1_struct_0(sK6))),sK4(sK7))
    | ~ m1_subset_1(sK4(u1_struct_0(sK6)),u1_struct_0(sK6))
    | ~ m1_subset_1(sK4(sK7),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_3884])).

cnf(c_5111,plain,
    ( ~ r2_hidden(sK4(sK7),sK7)
    | m1_subset_1(sK4(sK7),X0)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(X0)) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_6630,plain,
    ( ~ r2_hidden(sK4(sK7),sK7)
    | m1_subset_1(sK4(sK7),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_5111])).

cnf(c_29,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_5109,plain,
    ( ~ r2_hidden(sK4(sK7),sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(X0))
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_6619,plain,
    ( ~ r2_hidden(sK4(sK7),sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_struct_0(sK6)))
    | ~ v1_xboole_0(k2_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_5109])).

cnf(c_4565,plain,
    ( r3_lattices(sK6,k4_lattices(sK6,X0,sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6))),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6)),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_1344])).

cnf(c_5314,plain,
    ( r3_lattices(sK6,k4_lattices(sK6,sK4(u1_struct_0(sK6)),sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6))),sK4(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6)),u1_struct_0(sK6))
    | ~ m1_subset_1(sK4(u1_struct_0(sK6)),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_4565])).

cnf(c_4571,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6)),u1_struct_0(sK6))
    | m1_subset_1(k4_lattices(sK6,X0,sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6))),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_1507])).

cnf(c_5273,plain,
    ( ~ m1_subset_1(sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6)),u1_struct_0(sK6))
    | m1_subset_1(k4_lattices(sK6,sK4(u1_struct_0(sK6)),sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6))),u1_struct_0(sK6))
    | ~ m1_subset_1(sK4(u1_struct_0(sK6)),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_4571])).

cnf(c_3971,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | X1 != k1_zfmisc_1(u1_struct_0(sK6))
    | X0 != sK7 ),
    inference(instantiation,[status(thm)],[c_3051])).

cnf(c_4057,plain,
    ( m1_subset_1(sK7,X0)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | X0 != k1_zfmisc_1(u1_struct_0(sK6))
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_3971])).

cnf(c_4362,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | k1_zfmisc_1(X0) != k1_zfmisc_1(u1_struct_0(sK6))
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_4057])).

cnf(c_5268,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_struct_0(sK6)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | k1_zfmisc_1(k2_struct_0(sK6)) != k1_zfmisc_1(u1_struct_0(sK6))
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_4362])).

cnf(c_3055,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_4363,plain,
    ( X0 != u1_struct_0(sK6)
    | k1_zfmisc_1(X0) = k1_zfmisc_1(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_3055])).

cnf(c_4990,plain,
    ( k2_struct_0(sK6) != u1_struct_0(sK6)
    | k1_zfmisc_1(k2_struct_0(sK6)) = k1_zfmisc_1(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_4363])).

cnf(c_4662,plain,
    ( m1_subset_1(sK4(sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_4570,plain,
    ( r3_lattices(sK6,k4_lattices(sK6,sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6)),sK4(u1_struct_0(sK6))),sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6)))
    | ~ m1_subset_1(sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6)),u1_struct_0(sK6))
    | ~ m1_subset_1(sK4(u1_struct_0(sK6)),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_3884])).

cnf(c_3928,plain,
    ( r2_hidden(sK4(X0),X0)
    | ~ m1_subset_1(sK4(X0),X0)
    | v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_4515,plain,
    ( r2_hidden(sK4(sK7),sK7)
    | ~ m1_subset_1(sK4(sK7),sK7)
    | v1_xboole_0(sK7) ),
    inference(instantiation,[status(thm)],[c_3928])).

cnf(c_31,plain,
    ( ~ r2_hidden(sK5(X0,X1,X2),X2)
    | ~ r2_hidden(sK5(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | X2 = X1 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_3996,plain,
    ( ~ r2_hidden(sK5(X0,sK7,k2_struct_0(sK6)),k2_struct_0(sK6))
    | ~ r2_hidden(sK5(X0,sK7,k2_struct_0(sK6)),sK7)
    | ~ m1_subset_1(k2_struct_0(sK6),k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(X0))
    | k2_struct_0(sK6) = sK7 ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_4093,plain,
    ( ~ r2_hidden(sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6)),k2_struct_0(sK6))
    | ~ r2_hidden(sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6)),sK7)
    | ~ m1_subset_1(k2_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | k2_struct_0(sK6) = sK7 ),
    inference(instantiation,[status(thm)],[c_3996])).

cnf(c_33,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(sK5(X1,X2,X0),X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_3991,plain,
    ( m1_subset_1(sK5(X0,sK7,k2_struct_0(sK6)),X0)
    | ~ m1_subset_1(k2_struct_0(sK6),k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(X0))
    | k2_struct_0(sK6) = sK7 ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_4090,plain,
    ( m1_subset_1(sK5(u1_struct_0(sK6),sK7,k2_struct_0(sK6)),u1_struct_0(sK6))
    | ~ m1_subset_1(k2_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | k2_struct_0(sK6) = sK7 ),
    inference(instantiation,[status(thm)],[c_3991])).

cnf(c_4058,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_3047])).

cnf(c_3883,plain,
    ( m1_subset_1(sK4(u1_struct_0(sK6)),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_3078,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_3047])).

cnf(c_17,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_96,plain,
    ( ~ l1_struct_0(sK6)
    | k2_struct_0(sK6) = u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_18,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_93,plain,
    ( m1_subset_1(k2_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ l1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_20,plain,
    ( l1_struct_0(X0)
    | ~ l1_lattices(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_87,plain,
    ( l1_struct_0(sK6)
    | ~ l1_lattices(sK6) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_84,plain,
    ( l1_lattices(sK6)
    | ~ l3_lattices(sK6) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_34,negated_conjecture,
    ( k2_struct_0(sK6) != sK7 ),
    inference(cnf_transformation,[],[f114])).

cnf(c_37,negated_conjecture,
    ( v18_lattices(sK7,sK6) ),
    inference(cnf_transformation,[],[f111])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_238186,c_191194,c_73725,c_67885,c_24009,c_11891,c_10009,c_6897,c_6896,c_6827,c_6828,c_6630,c_6619,c_5314,c_5273,c_5268,c_4990,c_4662,c_4570,c_4515,c_4093,c_4090,c_4058,c_3883,c_3078,c_96,c_93,c_87,c_84,c_34,c_35,c_36,c_37,c_38,c_39])).


%------------------------------------------------------------------------------
