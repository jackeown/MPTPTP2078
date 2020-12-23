%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT2052+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:05 EST 2020

% Result     : Theorem 0.96s
% Output     : CNFRefutation 0.96s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 919 expanded)
%              Number of clauses        :   68 ( 176 expanded)
%              Number of leaves         :   10 ( 263 expanded)
%              Depth                    :   21
%              Number of atoms          :  450 (7561 expanded)
%              Number of equality atoms :   86 ( 232 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(X2,X1)
        & ~ v2_struct_0(X2)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_yellow19(X1,X2))
      <=> ? [X3] :
            ( r1_waybel_0(X1,X2,X3)
            & X0 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_yellow19(X1,X2))
      <=> ? [X3] :
            ( r1_waybel_0(X1,X2,X3)
            & X0 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_yellow19(X1,X2))
      <=> ? [X3] :
            ( r1_waybel_0(X1,X2,X3)
            & X0 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f7])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_yellow19(X1,X2))
          | ! [X3] :
              ( ~ r1_waybel_0(X1,X2,X3)
              | X0 != X3
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
        & ( ? [X3] :
              ( r1_waybel_0(X1,X2,X3)
              & X0 = X3
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(X0,a_2_1_yellow19(X1,X2)) ) )
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_yellow19(X1,X2))
          | ! [X3] :
              ( ~ r1_waybel_0(X1,X2,X3)
              | X0 != X3
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
        & ( ? [X4] :
              ( r1_waybel_0(X1,X2,X4)
              & X0 = X4
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(X0,a_2_1_yellow19(X1,X2)) ) )
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f11])).

fof(f13,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r1_waybel_0(X1,X2,X4)
          & X0 = X4
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( r1_waybel_0(X1,X2,sK0(X0,X1,X2))
        & sK0(X0,X1,X2) = X0
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_yellow19(X1,X2))
          | ! [X3] :
              ( ~ r1_waybel_0(X1,X2,X3)
              | X0 != X3
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
        & ( ( r1_waybel_0(X1,X2,sK0(X0,X1,X2))
            & sK0(X0,X1,X2) = X0
            & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(X0,a_2_1_yellow19(X1,X2)) ) )
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f13])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X0,a_2_1_yellow19(X1,X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_hidden(X2,k2_yellow19(X0,X1))
            <=> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & r1_waybel_0(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( r2_hidden(X2,k2_yellow19(X0,X1))
              <=> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & r1_waybel_0(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r2_hidden(X2,k2_yellow19(X0,X1))
            <~> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & r1_waybel_0(X0,X1,X2) ) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r2_hidden(X2,k2_yellow19(X0,X1))
            <~> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & r1_waybel_0(X0,X1,X2) ) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                | ~ r1_waybel_0(X0,X1,X2)
                | ~ r2_hidden(X2,k2_yellow19(X0,X1)) )
              & ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & r1_waybel_0(X0,X1,X2) )
                | r2_hidden(X2,k2_yellow19(X0,X1)) ) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                | ~ r1_waybel_0(X0,X1,X2)
                | ~ r2_hidden(X2,k2_yellow19(X0,X1)) )
              & ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & r1_waybel_0(X0,X1,X2) )
                | r2_hidden(X2,k2_yellow19(X0,X1)) ) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ r1_waybel_0(X0,X1,X2)
            | ~ r2_hidden(X2,k2_yellow19(X0,X1)) )
          & ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & r1_waybel_0(X0,X1,X2) )
            | r2_hidden(X2,k2_yellow19(X0,X1)) ) )
     => ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ r1_waybel_0(X0,X1,sK3)
          | ~ r2_hidden(sK3,k2_yellow19(X0,X1)) )
        & ( ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
            & r1_waybel_0(X0,X1,sK3) )
          | r2_hidden(sK3,k2_yellow19(X0,X1)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                | ~ r1_waybel_0(X0,X1,X2)
                | ~ r2_hidden(X2,k2_yellow19(X0,X1)) )
              & ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & r1_waybel_0(X0,X1,X2) )
                | r2_hidden(X2,k2_yellow19(X0,X1)) ) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ r1_waybel_0(X0,sK2,X2)
              | ~ r2_hidden(X2,k2_yellow19(X0,sK2)) )
            & ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & r1_waybel_0(X0,sK2,X2) )
              | r2_hidden(X2,k2_yellow19(X0,sK2)) ) )
        & l1_waybel_0(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ r1_waybel_0(X0,X1,X2)
                  | ~ r2_hidden(X2,k2_yellow19(X0,X1)) )
                & ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                    & r1_waybel_0(X0,X1,X2) )
                  | r2_hidden(X2,k2_yellow19(X0,X1)) ) )
            & l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
                | ~ r1_waybel_0(sK1,X1,X2)
                | ~ r2_hidden(X2,k2_yellow19(sK1,X1)) )
              & ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
                  & r1_waybel_0(sK1,X1,X2) )
                | r2_hidden(X2,k2_yellow19(sK1,X1)) ) )
          & l1_waybel_0(X1,sK1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r1_waybel_0(sK1,sK2,sK3)
      | ~ r2_hidden(sK3,k2_yellow19(sK1,sK2)) )
    & ( ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        & r1_waybel_0(sK1,sK2,sK3) )
      | r2_hidden(sK3,k2_yellow19(sK1,sK2)) )
    & l1_waybel_0(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f16,f19,f18,f17])).

fof(f29,plain,(
    l1_waybel_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f26,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f27,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f28,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => k2_yellow19(X0,X1) = a_2_1_yellow19(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,X1) = a_2_1_yellow19(X0,X1)
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,X1) = a_2_1_yellow19(X0,X1)
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f5])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,X1) = a_2_1_yellow19(X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f30,plain,
    ( r1_waybel_0(sK1,sK2,sK3)
    | r2_hidden(sK3,k2_yellow19(sK1,sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_1_yellow19(X1,X2))
      | ~ r1_waybel_0(X1,X2,X3)
      | X0 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_1_yellow19(X1,X2))
      | ~ r1_waybel_0(X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f25])).

fof(f31,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK3,k2_yellow19(sK1,sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f32,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_waybel_0(sK1,sK2,sK3)
    | ~ r2_hidden(sK3,k2_yellow19(sK1,sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_0(X1,X2,sK0(X0,X1,X2))
      | ~ r2_hidden(X0,a_2_1_yellow19(X1,X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( sK0(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_1_yellow19(X1,X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_432,plain,
    ( X0_42 != X1_42
    | X2_42 != X1_42
    | X2_42 = X0_42 ),
    theory(equality)).

cnf(c_685,plain,
    ( X0_42 != X1_42
    | X0_42 = sK0(X2_42,sK1,sK2)
    | sK0(X2_42,sK1,sK2) != X1_42 ),
    inference(instantiation,[status(thm)],[c_432])).

cnf(c_686,plain,
    ( sK0(sK3,sK1,sK2) != sK3
    | sK3 = sK0(sK3,sK1,sK2)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_685])).

cnf(c_435,plain,
    ( ~ m1_subset_1(X0_42,X0_43)
    | m1_subset_1(X1_42,X0_43)
    | X1_42 != X0_42 ),
    theory(equality)).

cnf(c_650,plain,
    ( m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK0(X1_42,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | X0_42 != sK0(X1_42,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_435])).

cnf(c_652,plain,
    ( ~ m1_subset_1(sK0(sK3,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | sK3 != sK0(sK3,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_650])).

cnf(c_4,plain,
    ( m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,a_2_1_yellow19(X1,X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_8,negated_conjecture,
    ( l1_waybel_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_179,plain,
    ( m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,a_2_1_yellow19(X1,X2))
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | sK2 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_8])).

cnf(c_180,plain,
    ( m1_subset_1(sK0(X0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,a_2_1_yellow19(sK1,sK2))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_179])).

cnf(c_11,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_10,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_9,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_184,plain,
    ( ~ r2_hidden(X0,a_2_1_yellow19(sK1,sK2))
    | m1_subset_1(sK0(X0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_180,c_11,c_10,c_9])).

cnf(c_185,plain,
    ( m1_subset_1(sK0(X0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,a_2_1_yellow19(sK1,sK2)) ),
    inference(renaming,[status(thm)],[c_184])).

cnf(c_424,plain,
    ( m1_subset_1(sK0(X0_42,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0_42,a_2_1_yellow19(sK1,sK2)) ),
    inference(subtyping,[status(esa)],[c_185])).

cnf(c_584,plain,
    ( m1_subset_1(sK0(X0_42,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | r2_hidden(X0_42,a_2_1_yellow19(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_424])).

cnf(c_0,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | a_2_1_yellow19(X1,X0) = k2_yellow19(X1,X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_171,plain,
    ( ~ l1_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | a_2_1_yellow19(X0,X1) = k2_yellow19(X0,X1)
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_8])).

cnf(c_172,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | a_2_1_yellow19(sK1,sK2) = k2_yellow19(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_171])).

cnf(c_174,plain,
    ( a_2_1_yellow19(sK1,sK2) = k2_yellow19(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_172,c_11,c_10,c_9])).

cnf(c_425,plain,
    ( a_2_1_yellow19(sK1,sK2) = k2_yellow19(sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_174])).

cnf(c_604,plain,
    ( m1_subset_1(sK0(X0_42,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | r2_hidden(X0_42,k2_yellow19(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_584,c_425])).

cnf(c_638,plain,
    ( m1_subset_1(sK0(X0_42,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0_42,k2_yellow19(sK1,sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_604])).

cnf(c_640,plain,
    ( m1_subset_1(sK0(sK3,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK3,k2_yellow19(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_638])).

cnf(c_7,negated_conjecture,
    ( r1_waybel_0(sK1,sK2,sK3)
    | r2_hidden(sK3,k2_yellow19(sK1,sK2)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_1,plain,
    ( ~ r1_waybel_0(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(X2,a_2_1_yellow19(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_150,plain,
    ( ~ r1_waybel_0(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(X2,a_2_1_yellow19(X0,X1))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_8])).

cnf(c_151,plain,
    ( ~ r1_waybel_0(sK1,sK2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X0,a_2_1_yellow19(sK1,sK2))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_150])).

cnf(c_155,plain,
    ( r2_hidden(X0,a_2_1_yellow19(sK1,sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_waybel_0(sK1,sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_151,c_11,c_10,c_9])).

cnf(c_156,plain,
    ( ~ r1_waybel_0(sK1,sK2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X0,a_2_1_yellow19(sK1,sK2)) ),
    inference(renaming,[status(thm)],[c_155])).

cnf(c_253,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X0,a_2_1_yellow19(sK1,sK2))
    | r2_hidden(sK3,k2_yellow19(sK1,sK2))
    | sK2 != sK2
    | sK1 != sK1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_156])).

cnf(c_254,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK3,a_2_1_yellow19(sK1,sK2))
    | r2_hidden(sK3,k2_yellow19(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_253])).

cnf(c_6,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK3,k2_yellow19(sK1,sK2)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_256,plain,
    ( r2_hidden(sK3,a_2_1_yellow19(sK1,sK2))
    | r2_hidden(sK3,k2_yellow19(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_254,c_6])).

cnf(c_422,plain,
    ( r2_hidden(sK3,a_2_1_yellow19(sK1,sK2))
    | r2_hidden(sK3,k2_yellow19(sK1,sK2)) ),
    inference(subtyping,[status(esa)],[c_256])).

cnf(c_586,plain,
    ( r2_hidden(sK3,a_2_1_yellow19(sK1,sK2)) = iProver_top
    | r2_hidden(sK3,k2_yellow19(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_422])).

cnf(c_601,plain,
    ( r2_hidden(sK3,k2_yellow19(sK1,sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_586,c_425])).

cnf(c_637,plain,
    ( r2_hidden(sK3,k2_yellow19(sK1,sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_601])).

cnf(c_5,negated_conjecture,
    ( ~ r1_waybel_0(sK1,sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK3,k2_yellow19(sK1,sK2)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_2,plain,
    ( r1_waybel_0(X0,X1,sK0(X2,X0,X1))
    | ~ r2_hidden(X2,a_2_1_yellow19(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_132,plain,
    ( r1_waybel_0(X0,X1,sK0(X2,X0,X1))
    | ~ r2_hidden(X2,a_2_1_yellow19(X0,X1))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_8])).

cnf(c_133,plain,
    ( r1_waybel_0(sK1,sK2,sK0(X0,sK1,sK2))
    | ~ r2_hidden(X0,a_2_1_yellow19(sK1,sK2))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_132])).

cnf(c_137,plain,
    ( ~ r2_hidden(X0,a_2_1_yellow19(sK1,sK2))
    | r1_waybel_0(sK1,sK2,sK0(X0,sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_133,c_11,c_10,c_9])).

cnf(c_138,plain,
    ( r1_waybel_0(sK1,sK2,sK0(X0,sK1,sK2))
    | ~ r2_hidden(X0,a_2_1_yellow19(sK1,sK2)) ),
    inference(renaming,[status(thm)],[c_137])).

cnf(c_230,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,a_2_1_yellow19(sK1,sK2))
    | ~ r2_hidden(sK3,k2_yellow19(sK1,sK2))
    | sK0(X0,sK1,sK2) != sK3
    | sK2 != sK2
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_138])).

cnf(c_344,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,a_2_1_yellow19(sK1,sK2))
    | ~ r2_hidden(sK3,k2_yellow19(sK1,sK2))
    | sK0(X0,sK1,sK2) != sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_230])).

cnf(c_420,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0_42,a_2_1_yellow19(sK1,sK2))
    | ~ r2_hidden(sK3,k2_yellow19(sK1,sK2))
    | sK0(X0_42,sK1,sK2) != sK3 ),
    inference(subtyping,[status(esa)],[c_344])).

cnf(c_427,plain,
    ( ~ r2_hidden(X0_42,a_2_1_yellow19(sK1,sK2))
    | sK0(X0_42,sK1,sK2) != sK3
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_420])).

cnf(c_589,plain,
    ( sK0(X0_42,sK1,sK2) != sK3
    | r2_hidden(X0_42,a_2_1_yellow19(sK1,sK2)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_427])).

cnf(c_620,plain,
    ( sK0(X0_42,sK1,sK2) != sK3
    | r2_hidden(X0_42,k2_yellow19(sK1,sK2)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_589,c_425])).

cnf(c_634,plain,
    ( ~ r2_hidden(X0_42,k2_yellow19(sK1,sK2))
    | ~ sP0_iProver_split
    | sK0(X0_42,sK1,sK2) != sK3 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_620])).

cnf(c_636,plain,
    ( ~ r2_hidden(sK3,k2_yellow19(sK1,sK2))
    | ~ sP0_iProver_split
    | sK0(sK3,sK1,sK2) != sK3 ),
    inference(instantiation,[status(thm)],[c_634])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,a_2_1_yellow19(X1,X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | sK0(X0,X1,X2) = X0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_197,plain,
    ( ~ r2_hidden(X0,a_2_1_yellow19(X1,X2))
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | sK0(X0,X1,X2) = X0
    | sK2 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_8])).

cnf(c_198,plain,
    ( ~ r2_hidden(X0,a_2_1_yellow19(sK1,sK2))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | sK0(X0,sK1,sK2) = X0 ),
    inference(unflattening,[status(thm)],[c_197])).

cnf(c_202,plain,
    ( ~ r2_hidden(X0,a_2_1_yellow19(sK1,sK2))
    | sK0(X0,sK1,sK2) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_198,c_11,c_10,c_9])).

cnf(c_423,plain,
    ( ~ r2_hidden(X0_42,a_2_1_yellow19(sK1,sK2))
    | sK0(X0_42,sK1,sK2) = X0_42 ),
    inference(subtyping,[status(esa)],[c_202])).

cnf(c_585,plain,
    ( sK0(X0_42,sK1,sK2) = X0_42
    | r2_hidden(X0_42,a_2_1_yellow19(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_423])).

cnf(c_596,plain,
    ( sK0(X0_42,sK1,sK2) = X0_42
    | r2_hidden(X0_42,k2_yellow19(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_585,c_425])).

cnf(c_629,plain,
    ( sK0(sK3,sK1,sK2) = sK3
    | r2_hidden(sK3,k2_yellow19(sK1,sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_596])).

cnf(c_428,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK3,k2_yellow19(sK1,sK2))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_420])).

cnf(c_588,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK3,k2_yellow19(sK1,sK2)) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_428])).

cnf(c_617,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_588,c_601])).

cnf(c_627,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | sP0_iProver_split ),
    inference(predicate_to_equality_rev,[status(thm)],[c_617])).

cnf(c_430,plain,
    ( X0_42 = X0_42 ),
    theory(equality)).

cnf(c_439,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_430])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_686,c_652,c_640,c_637,c_601,c_636,c_629,c_627,c_439])).


%------------------------------------------------------------------------------
