%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:04 EST 2020

% Result     : Theorem 0.75s
% Output     : CNFRefutation 0.75s
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
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:50:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 0.75/0.95  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.75/0.95  
% 0.75/0.95  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.75/0.95  
% 0.75/0.95  ------  iProver source info
% 0.75/0.95  
% 0.75/0.95  git: date: 2020-06-30 10:37:57 +0100
% 0.75/0.95  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.75/0.95  git: non_committed_changes: false
% 0.75/0.95  git: last_make_outside_of_git: false
% 0.75/0.95  
% 0.75/0.95  ------ 
% 0.75/0.95  
% 0.75/0.95  ------ Input Options
% 0.75/0.95  
% 0.75/0.95  --out_options                           all
% 0.75/0.95  --tptp_safe_out                         true
% 0.75/0.95  --problem_path                          ""
% 0.75/0.95  --include_path                          ""
% 0.75/0.95  --clausifier                            res/vclausify_rel
% 0.75/0.95  --clausifier_options                    --mode clausify
% 0.75/0.95  --stdin                                 false
% 0.75/0.95  --stats_out                             all
% 0.75/0.95  
% 0.75/0.95  ------ General Options
% 0.75/0.95  
% 0.75/0.95  --fof                                   false
% 0.75/0.95  --time_out_real                         305.
% 0.75/0.95  --time_out_virtual                      -1.
% 0.75/0.95  --symbol_type_check                     false
% 0.75/0.95  --clausify_out                          false
% 0.75/0.95  --sig_cnt_out                           false
% 0.75/0.95  --trig_cnt_out                          false
% 0.75/0.95  --trig_cnt_out_tolerance                1.
% 0.75/0.95  --trig_cnt_out_sk_spl                   false
% 0.75/0.95  --abstr_cl_out                          false
% 0.75/0.95  
% 0.75/0.95  ------ Global Options
% 0.75/0.95  
% 0.75/0.95  --schedule                              default
% 0.75/0.95  --add_important_lit                     false
% 0.75/0.95  --prop_solver_per_cl                    1000
% 0.75/0.95  --min_unsat_core                        false
% 0.75/0.95  --soft_assumptions                      false
% 0.75/0.95  --soft_lemma_size                       3
% 0.75/0.95  --prop_impl_unit_size                   0
% 0.75/0.95  --prop_impl_unit                        []
% 0.75/0.95  --share_sel_clauses                     true
% 0.75/0.95  --reset_solvers                         false
% 0.75/0.95  --bc_imp_inh                            [conj_cone]
% 0.75/0.95  --conj_cone_tolerance                   3.
% 0.75/0.95  --extra_neg_conj                        none
% 0.75/0.95  --large_theory_mode                     true
% 0.75/0.95  --prolific_symb_bound                   200
% 0.75/0.95  --lt_threshold                          2000
% 0.75/0.95  --clause_weak_htbl                      true
% 0.75/0.95  --gc_record_bc_elim                     false
% 0.75/0.95  
% 0.75/0.95  ------ Preprocessing Options
% 0.75/0.95  
% 0.75/0.95  --preprocessing_flag                    true
% 0.75/0.95  --time_out_prep_mult                    0.1
% 0.75/0.95  --splitting_mode                        input
% 0.75/0.95  --splitting_grd                         true
% 0.75/0.95  --splitting_cvd                         false
% 0.75/0.95  --splitting_cvd_svl                     false
% 0.75/0.95  --splitting_nvd                         32
% 0.75/0.95  --sub_typing                            true
% 0.75/0.95  --prep_gs_sim                           true
% 0.75/0.95  --prep_unflatten                        true
% 0.75/0.95  --prep_res_sim                          true
% 0.75/0.95  --prep_upred                            true
% 0.75/0.95  --prep_sem_filter                       exhaustive
% 0.75/0.95  --prep_sem_filter_out                   false
% 0.75/0.95  --pred_elim                             true
% 0.75/0.95  --res_sim_input                         true
% 0.75/0.95  --eq_ax_congr_red                       true
% 0.75/0.95  --pure_diseq_elim                       true
% 0.75/0.95  --brand_transform                       false
% 0.75/0.95  --non_eq_to_eq                          false
% 0.75/0.95  --prep_def_merge                        true
% 0.75/0.95  --prep_def_merge_prop_impl              false
% 0.75/0.95  --prep_def_merge_mbd                    true
% 0.75/0.95  --prep_def_merge_tr_red                 false
% 0.75/0.95  --prep_def_merge_tr_cl                  false
% 0.75/0.95  --smt_preprocessing                     true
% 0.75/0.95  --smt_ac_axioms                         fast
% 0.75/0.95  --preprocessed_out                      false
% 0.75/0.95  --preprocessed_stats                    false
% 0.75/0.95  
% 0.75/0.95  ------ Abstraction refinement Options
% 0.75/0.95  
% 0.75/0.95  --abstr_ref                             []
% 0.75/0.95  --abstr_ref_prep                        false
% 0.75/0.95  --abstr_ref_until_sat                   false
% 0.75/0.95  --abstr_ref_sig_restrict                funpre
% 0.75/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 0.75/0.95  --abstr_ref_under                       []
% 0.75/0.95  
% 0.75/0.95  ------ SAT Options
% 0.75/0.95  
% 0.75/0.95  --sat_mode                              false
% 0.75/0.95  --sat_fm_restart_options                ""
% 0.75/0.95  --sat_gr_def                            false
% 0.75/0.95  --sat_epr_types                         true
% 0.75/0.95  --sat_non_cyclic_types                  false
% 0.75/0.95  --sat_finite_models                     false
% 0.75/0.95  --sat_fm_lemmas                         false
% 0.75/0.95  --sat_fm_prep                           false
% 0.75/0.95  --sat_fm_uc_incr                        true
% 0.75/0.95  --sat_out_model                         small
% 0.75/0.95  --sat_out_clauses                       false
% 0.75/0.95  
% 0.75/0.95  ------ QBF Options
% 0.75/0.95  
% 0.75/0.95  --qbf_mode                              false
% 0.75/0.95  --qbf_elim_univ                         false
% 0.75/0.95  --qbf_dom_inst                          none
% 0.75/0.95  --qbf_dom_pre_inst                      false
% 0.75/0.95  --qbf_sk_in                             false
% 0.75/0.95  --qbf_pred_elim                         true
% 0.75/0.95  --qbf_split                             512
% 0.75/0.95  
% 0.75/0.95  ------ BMC1 Options
% 0.75/0.95  
% 0.75/0.95  --bmc1_incremental                      false
% 0.75/0.95  --bmc1_axioms                           reachable_all
% 0.75/0.95  --bmc1_min_bound                        0
% 0.75/0.95  --bmc1_max_bound                        -1
% 0.75/0.95  --bmc1_max_bound_default                -1
% 0.75/0.95  --bmc1_symbol_reachability              true
% 0.75/0.95  --bmc1_property_lemmas                  false
% 0.75/0.95  --bmc1_k_induction                      false
% 0.75/0.95  --bmc1_non_equiv_states                 false
% 0.75/0.95  --bmc1_deadlock                         false
% 0.75/0.95  --bmc1_ucm                              false
% 0.75/0.95  --bmc1_add_unsat_core                   none
% 0.75/0.95  --bmc1_unsat_core_children              false
% 0.75/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 0.75/0.95  --bmc1_out_stat                         full
% 0.75/0.95  --bmc1_ground_init                      false
% 0.75/0.95  --bmc1_pre_inst_next_state              false
% 0.75/0.95  --bmc1_pre_inst_state                   false
% 0.75/0.95  --bmc1_pre_inst_reach_state             false
% 0.75/0.95  --bmc1_out_unsat_core                   false
% 0.75/0.95  --bmc1_aig_witness_out                  false
% 0.75/0.95  --bmc1_verbose                          false
% 0.75/0.95  --bmc1_dump_clauses_tptp                false
% 0.75/0.95  --bmc1_dump_unsat_core_tptp             false
% 0.75/0.95  --bmc1_dump_file                        -
% 0.75/0.95  --bmc1_ucm_expand_uc_limit              128
% 0.75/0.95  --bmc1_ucm_n_expand_iterations          6
% 0.75/0.95  --bmc1_ucm_extend_mode                  1
% 0.75/0.95  --bmc1_ucm_init_mode                    2
% 0.75/0.95  --bmc1_ucm_cone_mode                    none
% 0.75/0.95  --bmc1_ucm_reduced_relation_type        0
% 0.75/0.95  --bmc1_ucm_relax_model                  4
% 0.75/0.95  --bmc1_ucm_full_tr_after_sat            true
% 0.75/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 0.75/0.95  --bmc1_ucm_layered_model                none
% 0.75/0.95  --bmc1_ucm_max_lemma_size               10
% 0.75/0.95  
% 0.75/0.95  ------ AIG Options
% 0.75/0.95  
% 0.75/0.95  --aig_mode                              false
% 0.75/0.95  
% 0.75/0.95  ------ Instantiation Options
% 0.75/0.95  
% 0.75/0.95  --instantiation_flag                    true
% 0.75/0.95  --inst_sos_flag                         false
% 0.75/0.95  --inst_sos_phase                        true
% 0.75/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.75/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.75/0.95  --inst_lit_sel_side                     num_symb
% 0.75/0.95  --inst_solver_per_active                1400
% 0.75/0.95  --inst_solver_calls_frac                1.
% 0.75/0.95  --inst_passive_queue_type               priority_queues
% 0.75/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.75/0.95  --inst_passive_queues_freq              [25;2]
% 0.75/0.95  --inst_dismatching                      true
% 0.75/0.95  --inst_eager_unprocessed_to_passive     true
% 0.75/0.95  --inst_prop_sim_given                   true
% 0.75/0.95  --inst_prop_sim_new                     false
% 0.75/0.95  --inst_subs_new                         false
% 0.75/0.95  --inst_eq_res_simp                      false
% 0.75/0.95  --inst_subs_given                       false
% 0.75/0.95  --inst_orphan_elimination               true
% 0.75/0.95  --inst_learning_loop_flag               true
% 0.75/0.95  --inst_learning_start                   3000
% 0.75/0.95  --inst_learning_factor                  2
% 0.75/0.95  --inst_start_prop_sim_after_learn       3
% 0.75/0.95  --inst_sel_renew                        solver
% 0.75/0.95  --inst_lit_activity_flag                true
% 0.75/0.95  --inst_restr_to_given                   false
% 0.75/0.95  --inst_activity_threshold               500
% 0.75/0.95  --inst_out_proof                        true
% 0.75/0.95  
% 0.75/0.95  ------ Resolution Options
% 0.75/0.95  
% 0.75/0.95  --resolution_flag                       true
% 0.75/0.95  --res_lit_sel                           adaptive
% 0.75/0.95  --res_lit_sel_side                      none
% 0.75/0.95  --res_ordering                          kbo
% 0.75/0.95  --res_to_prop_solver                    active
% 0.75/0.95  --res_prop_simpl_new                    false
% 0.75/0.95  --res_prop_simpl_given                  true
% 0.75/0.95  --res_passive_queue_type                priority_queues
% 0.75/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.75/0.95  --res_passive_queues_freq               [15;5]
% 0.75/0.95  --res_forward_subs                      full
% 0.75/0.95  --res_backward_subs                     full
% 0.75/0.95  --res_forward_subs_resolution           true
% 0.75/0.95  --res_backward_subs_resolution          true
% 0.75/0.95  --res_orphan_elimination                true
% 0.75/0.95  --res_time_limit                        2.
% 0.75/0.95  --res_out_proof                         true
% 0.75/0.95  
% 0.75/0.95  ------ Superposition Options
% 0.75/0.95  
% 0.75/0.95  --superposition_flag                    true
% 0.75/0.95  --sup_passive_queue_type                priority_queues
% 0.75/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.75/0.95  --sup_passive_queues_freq               [8;1;4]
% 0.75/0.95  --demod_completeness_check              fast
% 0.75/0.95  --demod_use_ground                      true
% 0.75/0.95  --sup_to_prop_solver                    passive
% 0.75/0.95  --sup_prop_simpl_new                    true
% 0.75/0.95  --sup_prop_simpl_given                  true
% 0.75/0.95  --sup_fun_splitting                     false
% 0.75/0.95  --sup_smt_interval                      50000
% 0.75/0.95  
% 0.75/0.95  ------ Superposition Simplification Setup
% 0.75/0.95  
% 0.75/0.95  --sup_indices_passive                   []
% 0.75/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.75/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.75/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.75/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 0.75/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.75/0.95  --sup_full_bw                           [BwDemod]
% 0.75/0.95  --sup_immed_triv                        [TrivRules]
% 0.75/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.75/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.75/0.95  --sup_immed_bw_main                     []
% 0.75/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.75/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 0.75/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.75/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.75/0.95  
% 0.75/0.95  ------ Combination Options
% 0.75/0.95  
% 0.75/0.95  --comb_res_mult                         3
% 0.75/0.95  --comb_sup_mult                         2
% 0.75/0.95  --comb_inst_mult                        10
% 0.75/0.95  
% 0.75/0.95  ------ Debug Options
% 0.75/0.95  
% 0.75/0.95  --dbg_backtrace                         false
% 0.75/0.95  --dbg_dump_prop_clauses                 false
% 0.75/0.95  --dbg_dump_prop_clauses_file            -
% 0.75/0.95  --dbg_out_stat                          false
% 0.75/0.95  ------ Parsing...
% 0.75/0.95  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.75/0.95  
% 0.75/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 0.75/0.95  
% 0.75/0.95  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.75/0.95  
% 0.75/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.75/0.95  ------ Proving...
% 0.75/0.95  ------ Problem Properties 
% 0.75/0.95  
% 0.75/0.95  
% 0.75/0.95  clauses                                 8
% 0.75/0.95  conjectures                             1
% 0.75/0.95  EPR                                     0
% 0.75/0.95  Horn                                    6
% 0.75/0.95  unary                                   1
% 0.75/0.95  binary                                  5
% 0.75/0.95  lits                                    17
% 0.75/0.95  lits eq                                 3
% 0.75/0.95  fd_pure                                 0
% 0.75/0.95  fd_pseudo                               0
% 0.75/0.95  fd_cond                                 0
% 0.75/0.95  fd_pseudo_cond                          0
% 0.75/0.95  AC symbols                              0
% 0.75/0.95  
% 0.75/0.95  ------ Schedule dynamic 5 is on 
% 0.75/0.95  
% 0.75/0.95  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.75/0.95  
% 0.75/0.95  
% 0.75/0.95  ------ 
% 0.75/0.95  Current options:
% 0.75/0.95  ------ 
% 0.75/0.95  
% 0.75/0.95  ------ Input Options
% 0.75/0.95  
% 0.75/0.95  --out_options                           all
% 0.75/0.95  --tptp_safe_out                         true
% 0.75/0.95  --problem_path                          ""
% 0.75/0.95  --include_path                          ""
% 0.75/0.95  --clausifier                            res/vclausify_rel
% 0.75/0.95  --clausifier_options                    --mode clausify
% 0.75/0.95  --stdin                                 false
% 0.75/0.95  --stats_out                             all
% 0.75/0.95  
% 0.75/0.95  ------ General Options
% 0.75/0.95  
% 0.75/0.95  --fof                                   false
% 0.75/0.95  --time_out_real                         305.
% 0.75/0.95  --time_out_virtual                      -1.
% 0.75/0.95  --symbol_type_check                     false
% 0.75/0.95  --clausify_out                          false
% 0.75/0.95  --sig_cnt_out                           false
% 0.75/0.95  --trig_cnt_out                          false
% 0.75/0.95  --trig_cnt_out_tolerance                1.
% 0.75/0.95  --trig_cnt_out_sk_spl                   false
% 0.75/0.95  --abstr_cl_out                          false
% 0.75/0.95  
% 0.75/0.95  ------ Global Options
% 0.75/0.95  
% 0.75/0.95  --schedule                              default
% 0.75/0.95  --add_important_lit                     false
% 0.75/0.95  --prop_solver_per_cl                    1000
% 0.75/0.95  --min_unsat_core                        false
% 0.75/0.95  --soft_assumptions                      false
% 0.75/0.95  --soft_lemma_size                       3
% 0.75/0.95  --prop_impl_unit_size                   0
% 0.75/0.95  --prop_impl_unit                        []
% 0.75/0.95  --share_sel_clauses                     true
% 0.75/0.95  --reset_solvers                         false
% 0.75/0.95  --bc_imp_inh                            [conj_cone]
% 0.75/0.95  --conj_cone_tolerance                   3.
% 0.75/0.95  --extra_neg_conj                        none
% 0.75/0.95  --large_theory_mode                     true
% 0.75/0.95  --prolific_symb_bound                   200
% 0.75/0.95  --lt_threshold                          2000
% 0.75/0.95  --clause_weak_htbl                      true
% 0.75/0.95  --gc_record_bc_elim                     false
% 0.75/0.95  
% 0.75/0.95  ------ Preprocessing Options
% 0.75/0.95  
% 0.75/0.95  --preprocessing_flag                    true
% 0.75/0.95  --time_out_prep_mult                    0.1
% 0.75/0.95  --splitting_mode                        input
% 0.75/0.95  --splitting_grd                         true
% 0.75/0.95  --splitting_cvd                         false
% 0.75/0.95  --splitting_cvd_svl                     false
% 0.75/0.95  --splitting_nvd                         32
% 0.75/0.95  --sub_typing                            true
% 0.75/0.95  --prep_gs_sim                           true
% 0.75/0.95  --prep_unflatten                        true
% 0.75/0.95  --prep_res_sim                          true
% 0.75/0.95  --prep_upred                            true
% 0.75/0.95  --prep_sem_filter                       exhaustive
% 0.75/0.95  --prep_sem_filter_out                   false
% 0.75/0.95  --pred_elim                             true
% 0.75/0.95  --res_sim_input                         true
% 0.75/0.95  --eq_ax_congr_red                       true
% 0.75/0.95  --pure_diseq_elim                       true
% 0.75/0.95  --brand_transform                       false
% 0.75/0.95  --non_eq_to_eq                          false
% 0.75/0.95  --prep_def_merge                        true
% 0.75/0.95  --prep_def_merge_prop_impl              false
% 0.75/0.95  --prep_def_merge_mbd                    true
% 0.75/0.95  --prep_def_merge_tr_red                 false
% 0.75/0.95  --prep_def_merge_tr_cl                  false
% 0.75/0.95  --smt_preprocessing                     true
% 0.75/0.95  --smt_ac_axioms                         fast
% 0.75/0.95  --preprocessed_out                      false
% 0.75/0.95  --preprocessed_stats                    false
% 0.75/0.95  
% 0.75/0.95  ------ Abstraction refinement Options
% 0.75/0.95  
% 0.75/0.95  --abstr_ref                             []
% 0.75/0.95  --abstr_ref_prep                        false
% 0.75/0.95  --abstr_ref_until_sat                   false
% 0.75/0.95  --abstr_ref_sig_restrict                funpre
% 0.75/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 0.75/0.95  --abstr_ref_under                       []
% 0.75/0.95  
% 0.75/0.95  ------ SAT Options
% 0.75/0.95  
% 0.75/0.95  --sat_mode                              false
% 0.75/0.95  --sat_fm_restart_options                ""
% 0.75/0.95  --sat_gr_def                            false
% 0.75/0.95  --sat_epr_types                         true
% 0.75/0.95  --sat_non_cyclic_types                  false
% 0.75/0.95  --sat_finite_models                     false
% 0.75/0.95  --sat_fm_lemmas                         false
% 0.75/0.95  --sat_fm_prep                           false
% 0.75/0.95  --sat_fm_uc_incr                        true
% 0.75/0.95  --sat_out_model                         small
% 0.75/0.95  --sat_out_clauses                       false
% 0.75/0.95  
% 0.75/0.95  ------ QBF Options
% 0.75/0.95  
% 0.75/0.95  --qbf_mode                              false
% 0.75/0.95  --qbf_elim_univ                         false
% 0.75/0.95  --qbf_dom_inst                          none
% 0.75/0.95  --qbf_dom_pre_inst                      false
% 0.75/0.95  --qbf_sk_in                             false
% 0.75/0.95  --qbf_pred_elim                         true
% 0.75/0.95  --qbf_split                             512
% 0.75/0.95  
% 0.75/0.95  ------ BMC1 Options
% 0.75/0.95  
% 0.75/0.95  --bmc1_incremental                      false
% 0.75/0.95  --bmc1_axioms                           reachable_all
% 0.75/0.95  --bmc1_min_bound                        0
% 0.75/0.95  --bmc1_max_bound                        -1
% 0.75/0.95  --bmc1_max_bound_default                -1
% 0.75/0.95  --bmc1_symbol_reachability              true
% 0.75/0.95  --bmc1_property_lemmas                  false
% 0.75/0.95  --bmc1_k_induction                      false
% 0.75/0.95  --bmc1_non_equiv_states                 false
% 0.75/0.95  --bmc1_deadlock                         false
% 0.75/0.95  --bmc1_ucm                              false
% 0.75/0.95  --bmc1_add_unsat_core                   none
% 0.75/0.95  --bmc1_unsat_core_children              false
% 0.75/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 0.75/0.95  --bmc1_out_stat                         full
% 0.75/0.95  --bmc1_ground_init                      false
% 0.75/0.95  --bmc1_pre_inst_next_state              false
% 0.75/0.95  --bmc1_pre_inst_state                   false
% 0.75/0.95  --bmc1_pre_inst_reach_state             false
% 0.75/0.95  --bmc1_out_unsat_core                   false
% 0.75/0.95  --bmc1_aig_witness_out                  false
% 0.75/0.95  --bmc1_verbose                          false
% 0.75/0.95  --bmc1_dump_clauses_tptp                false
% 0.75/0.95  --bmc1_dump_unsat_core_tptp             false
% 0.75/0.95  --bmc1_dump_file                        -
% 0.75/0.95  --bmc1_ucm_expand_uc_limit              128
% 0.75/0.95  --bmc1_ucm_n_expand_iterations          6
% 0.75/0.95  --bmc1_ucm_extend_mode                  1
% 0.75/0.95  --bmc1_ucm_init_mode                    2
% 0.75/0.95  --bmc1_ucm_cone_mode                    none
% 0.75/0.95  --bmc1_ucm_reduced_relation_type        0
% 0.75/0.95  --bmc1_ucm_relax_model                  4
% 0.75/0.95  --bmc1_ucm_full_tr_after_sat            true
% 0.75/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 0.75/0.95  --bmc1_ucm_layered_model                none
% 0.75/0.95  --bmc1_ucm_max_lemma_size               10
% 0.75/0.95  
% 0.75/0.95  ------ AIG Options
% 0.75/0.95  
% 0.75/0.95  --aig_mode                              false
% 0.75/0.95  
% 0.75/0.95  ------ Instantiation Options
% 0.75/0.95  
% 0.75/0.95  --instantiation_flag                    true
% 0.75/0.95  --inst_sos_flag                         false
% 0.75/0.95  --inst_sos_phase                        true
% 0.75/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.75/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.75/0.95  --inst_lit_sel_side                     none
% 0.75/0.95  --inst_solver_per_active                1400
% 0.75/0.95  --inst_solver_calls_frac                1.
% 0.75/0.95  --inst_passive_queue_type               priority_queues
% 0.75/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.75/0.96  --inst_passive_queues_freq              [25;2]
% 0.75/0.96  --inst_dismatching                      true
% 0.75/0.96  --inst_eager_unprocessed_to_passive     true
% 0.75/0.96  --inst_prop_sim_given                   true
% 0.75/0.96  --inst_prop_sim_new                     false
% 0.75/0.96  --inst_subs_new                         false
% 0.75/0.96  --inst_eq_res_simp                      false
% 0.75/0.96  --inst_subs_given                       false
% 0.75/0.96  --inst_orphan_elimination               true
% 0.75/0.96  --inst_learning_loop_flag               true
% 0.75/0.96  --inst_learning_start                   3000
% 0.75/0.96  --inst_learning_factor                  2
% 0.75/0.96  --inst_start_prop_sim_after_learn       3
% 0.75/0.96  --inst_sel_renew                        solver
% 0.75/0.96  --inst_lit_activity_flag                true
% 0.75/0.96  --inst_restr_to_given                   false
% 0.75/0.96  --inst_activity_threshold               500
% 0.75/0.96  --inst_out_proof                        true
% 0.75/0.96  
% 0.75/0.96  ------ Resolution Options
% 0.75/0.96  
% 0.75/0.96  --resolution_flag                       false
% 0.75/0.96  --res_lit_sel                           adaptive
% 0.75/0.96  --res_lit_sel_side                      none
% 0.75/0.96  --res_ordering                          kbo
% 0.75/0.96  --res_to_prop_solver                    active
% 0.75/0.96  --res_prop_simpl_new                    false
% 0.75/0.96  --res_prop_simpl_given                  true
% 0.75/0.96  --res_passive_queue_type                priority_queues
% 0.75/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.75/0.96  --res_passive_queues_freq               [15;5]
% 0.75/0.96  --res_forward_subs                      full
% 0.75/0.96  --res_backward_subs                     full
% 0.75/0.96  --res_forward_subs_resolution           true
% 0.75/0.96  --res_backward_subs_resolution          true
% 0.75/0.96  --res_orphan_elimination                true
% 0.75/0.96  --res_time_limit                        2.
% 0.75/0.96  --res_out_proof                         true
% 0.75/0.96  
% 0.75/0.96  ------ Superposition Options
% 0.75/0.96  
% 0.75/0.96  --superposition_flag                    true
% 0.75/0.96  --sup_passive_queue_type                priority_queues
% 0.75/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.75/0.96  --sup_passive_queues_freq               [8;1;4]
% 0.75/0.96  --demod_completeness_check              fast
% 0.75/0.96  --demod_use_ground                      true
% 0.75/0.96  --sup_to_prop_solver                    passive
% 0.75/0.96  --sup_prop_simpl_new                    true
% 0.75/0.96  --sup_prop_simpl_given                  true
% 0.75/0.96  --sup_fun_splitting                     false
% 0.75/0.96  --sup_smt_interval                      50000
% 0.75/0.96  
% 0.75/0.96  ------ Superposition Simplification Setup
% 0.75/0.96  
% 0.75/0.96  --sup_indices_passive                   []
% 0.75/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.75/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.75/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.75/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 0.75/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.75/0.96  --sup_full_bw                           [BwDemod]
% 0.75/0.96  --sup_immed_triv                        [TrivRules]
% 0.75/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.75/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.75/0.96  --sup_immed_bw_main                     []
% 0.75/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.75/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 0.75/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.75/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.75/0.96  
% 0.75/0.96  ------ Combination Options
% 0.75/0.96  
% 0.75/0.96  --comb_res_mult                         3
% 0.75/0.96  --comb_sup_mult                         2
% 0.75/0.96  --comb_inst_mult                        10
% 0.75/0.96  
% 0.75/0.96  ------ Debug Options
% 0.75/0.96  
% 0.75/0.96  --dbg_backtrace                         false
% 0.75/0.96  --dbg_dump_prop_clauses                 false
% 0.75/0.96  --dbg_dump_prop_clauses_file            -
% 0.75/0.96  --dbg_out_stat                          false
% 0.75/0.96  
% 0.75/0.96  
% 0.75/0.96  
% 0.75/0.96  
% 0.75/0.96  ------ Proving...
% 0.75/0.96  
% 0.75/0.96  
% 0.75/0.96  % SZS status Theorem for theBenchmark.p
% 0.75/0.96  
% 0.75/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 0.75/0.96  
% 0.75/0.96  fof(f2,axiom,(
% 0.75/0.96    ! [X0,X1,X2] : ((l1_waybel_0(X2,X1) & ~v2_struct_0(X2) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_yellow19(X1,X2)) <=> ? [X3] : (r1_waybel_0(X1,X2,X3) & X0 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))))),
% 0.75/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.75/0.96  
% 0.75/0.96  fof(f7,plain,(
% 0.75/0.96    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_yellow19(X1,X2)) <=> ? [X3] : (r1_waybel_0(X1,X2,X3) & X0 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1)))),
% 0.75/0.96    inference(ennf_transformation,[],[f2])).
% 0.75/0.96  
% 0.75/0.96  fof(f8,plain,(
% 0.75/0.96    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_yellow19(X1,X2)) <=> ? [X3] : (r1_waybel_0(X1,X2,X3) & X0 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1))),
% 0.75/0.96    inference(flattening,[],[f7])).
% 0.75/0.96  
% 0.75/0.96  fof(f11,plain,(
% 0.75/0.96    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_yellow19(X1,X2)) | ! [X3] : (~r1_waybel_0(X1,X2,X3) | X0 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (? [X3] : (r1_waybel_0(X1,X2,X3) & X0 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X0,a_2_1_yellow19(X1,X2)))) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1))),
% 0.75/0.96    inference(nnf_transformation,[],[f8])).
% 0.75/0.96  
% 0.75/0.96  fof(f12,plain,(
% 0.75/0.96    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_yellow19(X1,X2)) | ! [X3] : (~r1_waybel_0(X1,X2,X3) | X0 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (? [X4] : (r1_waybel_0(X1,X2,X4) & X0 = X4 & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X0,a_2_1_yellow19(X1,X2)))) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1))),
% 0.75/0.96    inference(rectify,[],[f11])).
% 0.75/0.96  
% 0.75/0.96  fof(f13,plain,(
% 0.75/0.96    ! [X2,X1,X0] : (? [X4] : (r1_waybel_0(X1,X2,X4) & X0 = X4 & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (r1_waybel_0(X1,X2,sK0(X0,X1,X2)) & sK0(X0,X1,X2) = X0 & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.75/0.96    introduced(choice_axiom,[])).
% 0.75/0.96  
% 0.75/0.96  fof(f14,plain,(
% 0.75/0.96    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_yellow19(X1,X2)) | ! [X3] : (~r1_waybel_0(X1,X2,X3) | X0 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & ((r1_waybel_0(X1,X2,sK0(X0,X1,X2)) & sK0(X0,X1,X2) = X0 & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X0,a_2_1_yellow19(X1,X2)))) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1))),
% 0.75/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f13])).
% 0.75/0.96  
% 0.75/0.96  fof(f22,plain,(
% 0.75/0.96    ( ! [X2,X0,X1] : (m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_yellow19(X1,X2)) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 0.75/0.96    inference(cnf_transformation,[],[f14])).
% 0.75/0.96  
% 0.75/0.96  fof(f3,conjecture,(
% 0.75/0.96    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_hidden(X2,k2_yellow19(X0,X1)) <=> (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & r1_waybel_0(X0,X1,X2)))))),
% 0.75/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.75/0.96  
% 0.75/0.96  fof(f4,negated_conjecture,(
% 0.75/0.96    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_hidden(X2,k2_yellow19(X0,X1)) <=> (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & r1_waybel_0(X0,X1,X2)))))),
% 0.75/0.96    inference(negated_conjecture,[],[f3])).
% 0.75/0.96  
% 0.75/0.96  fof(f9,plain,(
% 0.75/0.96    ? [X0] : (? [X1] : (? [X2] : (r2_hidden(X2,k2_yellow19(X0,X1)) <~> (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & r1_waybel_0(X0,X1,X2))) & (l1_waybel_0(X1,X0) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.75/0.96    inference(ennf_transformation,[],[f4])).
% 0.75/0.96  
% 0.75/0.96  fof(f10,plain,(
% 0.75/0.96    ? [X0] : (? [X1] : (? [X2] : (r2_hidden(X2,k2_yellow19(X0,X1)) <~> (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & r1_waybel_0(X0,X1,X2))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.75/0.96    inference(flattening,[],[f9])).
% 0.75/0.96  
% 0.75/0.96  fof(f15,plain,(
% 0.75/0.96    ? [X0] : (? [X1] : (? [X2] : (((~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_waybel_0(X0,X1,X2)) | ~r2_hidden(X2,k2_yellow19(X0,X1))) & ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & r1_waybel_0(X0,X1,X2)) | r2_hidden(X2,k2_yellow19(X0,X1)))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.75/0.96    inference(nnf_transformation,[],[f10])).
% 0.75/0.96  
% 0.75/0.96  fof(f16,plain,(
% 0.75/0.96    ? [X0] : (? [X1] : (? [X2] : ((~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_waybel_0(X0,X1,X2) | ~r2_hidden(X2,k2_yellow19(X0,X1))) & ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & r1_waybel_0(X0,X1,X2)) | r2_hidden(X2,k2_yellow19(X0,X1)))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.75/0.96    inference(flattening,[],[f15])).
% 0.75/0.96  
% 0.75/0.96  fof(f19,plain,(
% 0.75/0.96    ( ! [X0,X1] : (? [X2] : ((~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_waybel_0(X0,X1,X2) | ~r2_hidden(X2,k2_yellow19(X0,X1))) & ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & r1_waybel_0(X0,X1,X2)) | r2_hidden(X2,k2_yellow19(X0,X1)))) => ((~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_waybel_0(X0,X1,sK3) | ~r2_hidden(sK3,k2_yellow19(X0,X1))) & ((m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) & r1_waybel_0(X0,X1,sK3)) | r2_hidden(sK3,k2_yellow19(X0,X1))))) )),
% 0.75/0.96    introduced(choice_axiom,[])).
% 0.75/0.96  
% 0.75/0.96  fof(f18,plain,(
% 0.75/0.96    ( ! [X0] : (? [X1] : (? [X2] : ((~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_waybel_0(X0,X1,X2) | ~r2_hidden(X2,k2_yellow19(X0,X1))) & ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & r1_waybel_0(X0,X1,X2)) | r2_hidden(X2,k2_yellow19(X0,X1)))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : ((~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_waybel_0(X0,sK2,X2) | ~r2_hidden(X2,k2_yellow19(X0,sK2))) & ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & r1_waybel_0(X0,sK2,X2)) | r2_hidden(X2,k2_yellow19(X0,sK2)))) & l1_waybel_0(sK2,X0) & ~v2_struct_0(sK2))) )),
% 0.75/0.96    introduced(choice_axiom,[])).
% 0.75/0.96  
% 0.75/0.96  fof(f17,plain,(
% 0.75/0.96    ? [X0] : (? [X1] : (? [X2] : ((~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_waybel_0(X0,X1,X2) | ~r2_hidden(X2,k2_yellow19(X0,X1))) & ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & r1_waybel_0(X0,X1,X2)) | r2_hidden(X2,k2_yellow19(X0,X1)))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) | ~r1_waybel_0(sK1,X1,X2) | ~r2_hidden(X2,k2_yellow19(sK1,X1))) & ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) & r1_waybel_0(sK1,X1,X2)) | r2_hidden(X2,k2_yellow19(sK1,X1)))) & l1_waybel_0(X1,sK1) & ~v2_struct_0(X1)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))),
% 0.75/0.96    introduced(choice_axiom,[])).
% 0.75/0.96  
% 0.75/0.96  fof(f20,plain,(
% 0.75/0.96    (((~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~r1_waybel_0(sK1,sK2,sK3) | ~r2_hidden(sK3,k2_yellow19(sK1,sK2))) & ((m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) & r1_waybel_0(sK1,sK2,sK3)) | r2_hidden(sK3,k2_yellow19(sK1,sK2)))) & l1_waybel_0(sK2,sK1) & ~v2_struct_0(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)),
% 0.75/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f16,f19,f18,f17])).
% 0.75/0.96  
% 0.75/0.96  fof(f29,plain,(
% 0.75/0.96    l1_waybel_0(sK2,sK1)),
% 0.75/0.96    inference(cnf_transformation,[],[f20])).
% 0.75/0.96  
% 0.75/0.96  fof(f26,plain,(
% 0.75/0.96    ~v2_struct_0(sK1)),
% 0.75/0.96    inference(cnf_transformation,[],[f20])).
% 0.75/0.96  
% 0.75/0.96  fof(f27,plain,(
% 0.75/0.96    l1_struct_0(sK1)),
% 0.75/0.96    inference(cnf_transformation,[],[f20])).
% 0.75/0.96  
% 0.75/0.96  fof(f28,plain,(
% 0.75/0.96    ~v2_struct_0(sK2)),
% 0.75/0.96    inference(cnf_transformation,[],[f20])).
% 0.75/0.96  
% 0.75/0.96  fof(f1,axiom,(
% 0.75/0.96    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => k2_yellow19(X0,X1) = a_2_1_yellow19(X0,X1)))),
% 0.75/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.75/0.96  
% 0.75/0.96  fof(f5,plain,(
% 0.75/0.96    ! [X0] : (! [X1] : (k2_yellow19(X0,X1) = a_2_1_yellow19(X0,X1) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.75/0.96    inference(ennf_transformation,[],[f1])).
% 0.75/0.96  
% 0.75/0.96  fof(f6,plain,(
% 0.75/0.96    ! [X0] : (! [X1] : (k2_yellow19(X0,X1) = a_2_1_yellow19(X0,X1) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.75/0.96    inference(flattening,[],[f5])).
% 0.75/0.96  
% 0.75/0.96  fof(f21,plain,(
% 0.75/0.96    ( ! [X0,X1] : (k2_yellow19(X0,X1) = a_2_1_yellow19(X0,X1) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.75/0.96    inference(cnf_transformation,[],[f6])).
% 0.75/0.96  
% 0.75/0.96  fof(f30,plain,(
% 0.75/0.96    r1_waybel_0(sK1,sK2,sK3) | r2_hidden(sK3,k2_yellow19(sK1,sK2))),
% 0.75/0.96    inference(cnf_transformation,[],[f20])).
% 0.75/0.96  
% 0.75/0.96  fof(f25,plain,(
% 0.75/0.96    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_1_yellow19(X1,X2)) | ~r1_waybel_0(X1,X2,X3) | X0 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 0.75/0.96    inference(cnf_transformation,[],[f14])).
% 0.75/0.96  
% 0.75/0.96  fof(f33,plain,(
% 0.75/0.96    ( ! [X2,X3,X1] : (r2_hidden(X3,a_2_1_yellow19(X1,X2)) | ~r1_waybel_0(X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 0.75/0.96    inference(equality_resolution,[],[f25])).
% 0.75/0.96  
% 0.75/0.96  fof(f31,plain,(
% 0.75/0.96    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | r2_hidden(sK3,k2_yellow19(sK1,sK2))),
% 0.75/0.96    inference(cnf_transformation,[],[f20])).
% 0.75/0.96  
% 0.75/0.96  fof(f32,plain,(
% 0.75/0.96    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~r1_waybel_0(sK1,sK2,sK3) | ~r2_hidden(sK3,k2_yellow19(sK1,sK2))),
% 0.75/0.96    inference(cnf_transformation,[],[f20])).
% 0.75/0.96  
% 0.75/0.96  fof(f24,plain,(
% 0.75/0.96    ( ! [X2,X0,X1] : (r1_waybel_0(X1,X2,sK0(X0,X1,X2)) | ~r2_hidden(X0,a_2_1_yellow19(X1,X2)) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 0.75/0.96    inference(cnf_transformation,[],[f14])).
% 0.75/0.96  
% 0.75/0.96  fof(f23,plain,(
% 0.75/0.96    ( ! [X2,X0,X1] : (sK0(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_1_yellow19(X1,X2)) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 0.75/0.96    inference(cnf_transformation,[],[f14])).
% 0.75/0.96  
% 0.75/0.96  cnf(c_432,plain,
% 0.75/0.96      ( X0_42 != X1_42 | X2_42 != X1_42 | X2_42 = X0_42 ),
% 0.75/0.96      theory(equality) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_685,plain,
% 0.75/0.96      ( X0_42 != X1_42
% 0.75/0.96      | X0_42 = sK0(X2_42,sK1,sK2)
% 0.75/0.96      | sK0(X2_42,sK1,sK2) != X1_42 ),
% 0.75/0.96      inference(instantiation,[status(thm)],[c_432]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_686,plain,
% 0.75/0.96      ( sK0(sK3,sK1,sK2) != sK3 | sK3 = sK0(sK3,sK1,sK2) | sK3 != sK3 ),
% 0.75/0.96      inference(instantiation,[status(thm)],[c_685]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_435,plain,
% 0.75/0.96      ( ~ m1_subset_1(X0_42,X0_43)
% 0.75/0.96      | m1_subset_1(X1_42,X0_43)
% 0.75/0.96      | X1_42 != X0_42 ),
% 0.75/0.96      theory(equality) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_650,plain,
% 0.75/0.96      ( m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.75/0.96      | ~ m1_subset_1(sK0(X1_42,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 0.75/0.96      | X0_42 != sK0(X1_42,sK1,sK2) ),
% 0.75/0.96      inference(instantiation,[status(thm)],[c_435]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_652,plain,
% 0.75/0.96      ( ~ m1_subset_1(sK0(sK3,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 0.75/0.96      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.75/0.96      | sK3 != sK0(sK3,sK1,sK2) ),
% 0.75/0.96      inference(instantiation,[status(thm)],[c_650]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_4,plain,
% 0.75/0.96      ( m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 0.75/0.96      | ~ r2_hidden(X0,a_2_1_yellow19(X1,X2))
% 0.75/0.96      | ~ l1_waybel_0(X2,X1)
% 0.75/0.96      | ~ l1_struct_0(X1)
% 0.75/0.96      | v2_struct_0(X1)
% 0.75/0.96      | v2_struct_0(X2) ),
% 0.75/0.96      inference(cnf_transformation,[],[f22]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_8,negated_conjecture,
% 0.75/0.96      ( l1_waybel_0(sK2,sK1) ),
% 0.75/0.96      inference(cnf_transformation,[],[f29]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_179,plain,
% 0.75/0.96      ( m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 0.75/0.96      | ~ r2_hidden(X0,a_2_1_yellow19(X1,X2))
% 0.75/0.96      | ~ l1_struct_0(X1)
% 0.75/0.96      | v2_struct_0(X1)
% 0.75/0.96      | v2_struct_0(X2)
% 0.75/0.96      | sK2 != X2
% 0.75/0.96      | sK1 != X1 ),
% 0.75/0.96      inference(resolution_lifted,[status(thm)],[c_4,c_8]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_180,plain,
% 0.75/0.96      ( m1_subset_1(sK0(X0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 0.75/0.96      | ~ r2_hidden(X0,a_2_1_yellow19(sK1,sK2))
% 0.75/0.96      | ~ l1_struct_0(sK1)
% 0.75/0.96      | v2_struct_0(sK2)
% 0.75/0.96      | v2_struct_0(sK1) ),
% 0.75/0.96      inference(unflattening,[status(thm)],[c_179]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_11,negated_conjecture,
% 0.75/0.96      ( ~ v2_struct_0(sK1) ),
% 0.75/0.96      inference(cnf_transformation,[],[f26]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_10,negated_conjecture,
% 0.75/0.96      ( l1_struct_0(sK1) ),
% 0.75/0.96      inference(cnf_transformation,[],[f27]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_9,negated_conjecture,
% 0.75/0.96      ( ~ v2_struct_0(sK2) ),
% 0.75/0.96      inference(cnf_transformation,[],[f28]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_184,plain,
% 0.75/0.96      ( ~ r2_hidden(X0,a_2_1_yellow19(sK1,sK2))
% 0.75/0.96      | m1_subset_1(sK0(X0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 0.75/0.96      inference(global_propositional_subsumption,
% 0.75/0.96                [status(thm)],
% 0.75/0.96                [c_180,c_11,c_10,c_9]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_185,plain,
% 0.75/0.96      ( m1_subset_1(sK0(X0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 0.75/0.96      | ~ r2_hidden(X0,a_2_1_yellow19(sK1,sK2)) ),
% 0.75/0.96      inference(renaming,[status(thm)],[c_184]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_424,plain,
% 0.75/0.96      ( m1_subset_1(sK0(X0_42,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 0.75/0.96      | ~ r2_hidden(X0_42,a_2_1_yellow19(sK1,sK2)) ),
% 0.75/0.96      inference(subtyping,[status(esa)],[c_185]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_584,plain,
% 0.75/0.96      ( m1_subset_1(sK0(X0_42,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 0.75/0.96      | r2_hidden(X0_42,a_2_1_yellow19(sK1,sK2)) != iProver_top ),
% 0.75/0.96      inference(predicate_to_equality,[status(thm)],[c_424]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_0,plain,
% 0.75/0.96      ( ~ l1_waybel_0(X0,X1)
% 0.75/0.96      | ~ l1_struct_0(X1)
% 0.75/0.96      | v2_struct_0(X1)
% 0.75/0.96      | v2_struct_0(X0)
% 0.75/0.96      | a_2_1_yellow19(X1,X0) = k2_yellow19(X1,X0) ),
% 0.75/0.96      inference(cnf_transformation,[],[f21]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_171,plain,
% 0.75/0.96      ( ~ l1_struct_0(X0)
% 0.75/0.96      | v2_struct_0(X1)
% 0.75/0.96      | v2_struct_0(X0)
% 0.75/0.96      | a_2_1_yellow19(X0,X1) = k2_yellow19(X0,X1)
% 0.75/0.96      | sK2 != X1
% 0.75/0.96      | sK1 != X0 ),
% 0.75/0.96      inference(resolution_lifted,[status(thm)],[c_0,c_8]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_172,plain,
% 0.75/0.96      ( ~ l1_struct_0(sK1)
% 0.75/0.96      | v2_struct_0(sK2)
% 0.75/0.96      | v2_struct_0(sK1)
% 0.75/0.96      | a_2_1_yellow19(sK1,sK2) = k2_yellow19(sK1,sK2) ),
% 0.75/0.96      inference(unflattening,[status(thm)],[c_171]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_174,plain,
% 0.75/0.96      ( a_2_1_yellow19(sK1,sK2) = k2_yellow19(sK1,sK2) ),
% 0.75/0.96      inference(global_propositional_subsumption,
% 0.75/0.96                [status(thm)],
% 0.75/0.96                [c_172,c_11,c_10,c_9]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_425,plain,
% 0.75/0.96      ( a_2_1_yellow19(sK1,sK2) = k2_yellow19(sK1,sK2) ),
% 0.75/0.96      inference(subtyping,[status(esa)],[c_174]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_604,plain,
% 0.75/0.96      ( m1_subset_1(sK0(X0_42,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 0.75/0.96      | r2_hidden(X0_42,k2_yellow19(sK1,sK2)) != iProver_top ),
% 0.75/0.96      inference(light_normalisation,[status(thm)],[c_584,c_425]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_638,plain,
% 0.75/0.96      ( m1_subset_1(sK0(X0_42,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 0.75/0.96      | ~ r2_hidden(X0_42,k2_yellow19(sK1,sK2)) ),
% 0.75/0.96      inference(predicate_to_equality_rev,[status(thm)],[c_604]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_640,plain,
% 0.75/0.96      ( m1_subset_1(sK0(sK3,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 0.75/0.96      | ~ r2_hidden(sK3,k2_yellow19(sK1,sK2)) ),
% 0.75/0.96      inference(instantiation,[status(thm)],[c_638]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_7,negated_conjecture,
% 0.75/0.96      ( r1_waybel_0(sK1,sK2,sK3) | r2_hidden(sK3,k2_yellow19(sK1,sK2)) ),
% 0.75/0.96      inference(cnf_transformation,[],[f30]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_1,plain,
% 0.75/0.96      ( ~ r1_waybel_0(X0,X1,X2)
% 0.75/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 0.75/0.96      | r2_hidden(X2,a_2_1_yellow19(X0,X1))
% 0.75/0.96      | ~ l1_waybel_0(X1,X0)
% 0.75/0.96      | ~ l1_struct_0(X0)
% 0.75/0.96      | v2_struct_0(X0)
% 0.75/0.96      | v2_struct_0(X1) ),
% 0.75/0.96      inference(cnf_transformation,[],[f33]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_150,plain,
% 0.75/0.96      ( ~ r1_waybel_0(X0,X1,X2)
% 0.75/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 0.75/0.96      | r2_hidden(X2,a_2_1_yellow19(X0,X1))
% 0.75/0.96      | ~ l1_struct_0(X0)
% 0.75/0.96      | v2_struct_0(X0)
% 0.75/0.96      | v2_struct_0(X1)
% 0.75/0.96      | sK2 != X1
% 0.75/0.96      | sK1 != X0 ),
% 0.75/0.96      inference(resolution_lifted,[status(thm)],[c_1,c_8]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_151,plain,
% 0.75/0.96      ( ~ r1_waybel_0(sK1,sK2,X0)
% 0.75/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.75/0.96      | r2_hidden(X0,a_2_1_yellow19(sK1,sK2))
% 0.75/0.96      | ~ l1_struct_0(sK1)
% 0.75/0.96      | v2_struct_0(sK2)
% 0.75/0.96      | v2_struct_0(sK1) ),
% 0.75/0.96      inference(unflattening,[status(thm)],[c_150]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_155,plain,
% 0.75/0.96      ( r2_hidden(X0,a_2_1_yellow19(sK1,sK2))
% 0.75/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.75/0.96      | ~ r1_waybel_0(sK1,sK2,X0) ),
% 0.75/0.96      inference(global_propositional_subsumption,
% 0.75/0.96                [status(thm)],
% 0.75/0.96                [c_151,c_11,c_10,c_9]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_156,plain,
% 0.75/0.96      ( ~ r1_waybel_0(sK1,sK2,X0)
% 0.75/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.75/0.96      | r2_hidden(X0,a_2_1_yellow19(sK1,sK2)) ),
% 0.75/0.96      inference(renaming,[status(thm)],[c_155]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_253,plain,
% 0.75/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.75/0.96      | r2_hidden(X0,a_2_1_yellow19(sK1,sK2))
% 0.75/0.96      | r2_hidden(sK3,k2_yellow19(sK1,sK2))
% 0.75/0.96      | sK2 != sK2
% 0.75/0.96      | sK1 != sK1
% 0.75/0.96      | sK3 != X0 ),
% 0.75/0.96      inference(resolution_lifted,[status(thm)],[c_7,c_156]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_254,plain,
% 0.75/0.96      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.75/0.96      | r2_hidden(sK3,a_2_1_yellow19(sK1,sK2))
% 0.75/0.96      | r2_hidden(sK3,k2_yellow19(sK1,sK2)) ),
% 0.75/0.96      inference(unflattening,[status(thm)],[c_253]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_6,negated_conjecture,
% 0.75/0.96      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.75/0.96      | r2_hidden(sK3,k2_yellow19(sK1,sK2)) ),
% 0.75/0.96      inference(cnf_transformation,[],[f31]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_256,plain,
% 0.75/0.96      ( r2_hidden(sK3,a_2_1_yellow19(sK1,sK2))
% 0.75/0.96      | r2_hidden(sK3,k2_yellow19(sK1,sK2)) ),
% 0.75/0.96      inference(global_propositional_subsumption,
% 0.75/0.96                [status(thm)],
% 0.75/0.96                [c_254,c_6]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_422,plain,
% 0.75/0.96      ( r2_hidden(sK3,a_2_1_yellow19(sK1,sK2))
% 0.75/0.96      | r2_hidden(sK3,k2_yellow19(sK1,sK2)) ),
% 0.75/0.96      inference(subtyping,[status(esa)],[c_256]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_586,plain,
% 0.75/0.96      ( r2_hidden(sK3,a_2_1_yellow19(sK1,sK2)) = iProver_top
% 0.75/0.96      | r2_hidden(sK3,k2_yellow19(sK1,sK2)) = iProver_top ),
% 0.75/0.96      inference(predicate_to_equality,[status(thm)],[c_422]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_601,plain,
% 0.75/0.96      ( r2_hidden(sK3,k2_yellow19(sK1,sK2)) = iProver_top ),
% 0.75/0.96      inference(light_normalisation,[status(thm)],[c_586,c_425]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_637,plain,
% 0.75/0.96      ( r2_hidden(sK3,k2_yellow19(sK1,sK2)) ),
% 0.75/0.96      inference(predicate_to_equality_rev,[status(thm)],[c_601]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_5,negated_conjecture,
% 0.75/0.96      ( ~ r1_waybel_0(sK1,sK2,sK3)
% 0.75/0.96      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.75/0.96      | ~ r2_hidden(sK3,k2_yellow19(sK1,sK2)) ),
% 0.75/0.96      inference(cnf_transformation,[],[f32]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_2,plain,
% 0.75/0.96      ( r1_waybel_0(X0,X1,sK0(X2,X0,X1))
% 0.75/0.96      | ~ r2_hidden(X2,a_2_1_yellow19(X0,X1))
% 0.75/0.96      | ~ l1_waybel_0(X1,X0)
% 0.75/0.96      | ~ l1_struct_0(X0)
% 0.75/0.96      | v2_struct_0(X0)
% 0.75/0.96      | v2_struct_0(X1) ),
% 0.75/0.96      inference(cnf_transformation,[],[f24]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_132,plain,
% 0.75/0.96      ( r1_waybel_0(X0,X1,sK0(X2,X0,X1))
% 0.75/0.96      | ~ r2_hidden(X2,a_2_1_yellow19(X0,X1))
% 0.75/0.96      | ~ l1_struct_0(X0)
% 0.75/0.96      | v2_struct_0(X0)
% 0.75/0.96      | v2_struct_0(X1)
% 0.75/0.96      | sK2 != X1
% 0.75/0.96      | sK1 != X0 ),
% 0.75/0.96      inference(resolution_lifted,[status(thm)],[c_2,c_8]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_133,plain,
% 0.75/0.96      ( r1_waybel_0(sK1,sK2,sK0(X0,sK1,sK2))
% 0.75/0.96      | ~ r2_hidden(X0,a_2_1_yellow19(sK1,sK2))
% 0.75/0.96      | ~ l1_struct_0(sK1)
% 0.75/0.96      | v2_struct_0(sK2)
% 0.75/0.96      | v2_struct_0(sK1) ),
% 0.75/0.96      inference(unflattening,[status(thm)],[c_132]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_137,plain,
% 0.75/0.96      ( ~ r2_hidden(X0,a_2_1_yellow19(sK1,sK2))
% 0.75/0.96      | r1_waybel_0(sK1,sK2,sK0(X0,sK1,sK2)) ),
% 0.75/0.96      inference(global_propositional_subsumption,
% 0.75/0.96                [status(thm)],
% 0.75/0.96                [c_133,c_11,c_10,c_9]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_138,plain,
% 0.75/0.96      ( r1_waybel_0(sK1,sK2,sK0(X0,sK1,sK2))
% 0.75/0.96      | ~ r2_hidden(X0,a_2_1_yellow19(sK1,sK2)) ),
% 0.75/0.96      inference(renaming,[status(thm)],[c_137]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_230,plain,
% 0.75/0.96      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.75/0.96      | ~ r2_hidden(X0,a_2_1_yellow19(sK1,sK2))
% 0.75/0.96      | ~ r2_hidden(sK3,k2_yellow19(sK1,sK2))
% 0.75/0.96      | sK0(X0,sK1,sK2) != sK3
% 0.75/0.96      | sK2 != sK2
% 0.75/0.96      | sK1 != sK1 ),
% 0.75/0.96      inference(resolution_lifted,[status(thm)],[c_5,c_138]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_344,plain,
% 0.75/0.96      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.75/0.96      | ~ r2_hidden(X0,a_2_1_yellow19(sK1,sK2))
% 0.75/0.96      | ~ r2_hidden(sK3,k2_yellow19(sK1,sK2))
% 0.75/0.96      | sK0(X0,sK1,sK2) != sK3 ),
% 0.75/0.96      inference(equality_resolution_simp,[status(thm)],[c_230]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_420,plain,
% 0.75/0.96      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.75/0.96      | ~ r2_hidden(X0_42,a_2_1_yellow19(sK1,sK2))
% 0.75/0.96      | ~ r2_hidden(sK3,k2_yellow19(sK1,sK2))
% 0.75/0.96      | sK0(X0_42,sK1,sK2) != sK3 ),
% 0.75/0.96      inference(subtyping,[status(esa)],[c_344]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_427,plain,
% 0.75/0.96      ( ~ r2_hidden(X0_42,a_2_1_yellow19(sK1,sK2))
% 0.75/0.96      | sK0(X0_42,sK1,sK2) != sK3
% 0.75/0.96      | ~ sP0_iProver_split ),
% 0.75/0.96      inference(splitting,
% 0.75/0.96                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 0.75/0.96                [c_420]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_589,plain,
% 0.75/0.96      ( sK0(X0_42,sK1,sK2) != sK3
% 0.75/0.96      | r2_hidden(X0_42,a_2_1_yellow19(sK1,sK2)) != iProver_top
% 0.75/0.96      | sP0_iProver_split != iProver_top ),
% 0.75/0.96      inference(predicate_to_equality,[status(thm)],[c_427]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_620,plain,
% 0.75/0.96      ( sK0(X0_42,sK1,sK2) != sK3
% 0.75/0.96      | r2_hidden(X0_42,k2_yellow19(sK1,sK2)) != iProver_top
% 0.75/0.96      | sP0_iProver_split != iProver_top ),
% 0.75/0.96      inference(light_normalisation,[status(thm)],[c_589,c_425]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_634,plain,
% 0.75/0.96      ( ~ r2_hidden(X0_42,k2_yellow19(sK1,sK2))
% 0.75/0.96      | ~ sP0_iProver_split
% 0.75/0.96      | sK0(X0_42,sK1,sK2) != sK3 ),
% 0.75/0.96      inference(predicate_to_equality_rev,[status(thm)],[c_620]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_636,plain,
% 0.75/0.96      ( ~ r2_hidden(sK3,k2_yellow19(sK1,sK2))
% 0.75/0.96      | ~ sP0_iProver_split
% 0.75/0.96      | sK0(sK3,sK1,sK2) != sK3 ),
% 0.75/0.96      inference(instantiation,[status(thm)],[c_634]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_3,plain,
% 0.75/0.96      ( ~ r2_hidden(X0,a_2_1_yellow19(X1,X2))
% 0.75/0.96      | ~ l1_waybel_0(X2,X1)
% 0.75/0.96      | ~ l1_struct_0(X1)
% 0.75/0.96      | v2_struct_0(X1)
% 0.75/0.96      | v2_struct_0(X2)
% 0.75/0.96      | sK0(X0,X1,X2) = X0 ),
% 0.75/0.96      inference(cnf_transformation,[],[f23]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_197,plain,
% 0.75/0.96      ( ~ r2_hidden(X0,a_2_1_yellow19(X1,X2))
% 0.75/0.96      | ~ l1_struct_0(X1)
% 0.75/0.96      | v2_struct_0(X1)
% 0.75/0.96      | v2_struct_0(X2)
% 0.75/0.96      | sK0(X0,X1,X2) = X0
% 0.75/0.96      | sK2 != X2
% 0.75/0.96      | sK1 != X1 ),
% 0.75/0.96      inference(resolution_lifted,[status(thm)],[c_3,c_8]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_198,plain,
% 0.75/0.96      ( ~ r2_hidden(X0,a_2_1_yellow19(sK1,sK2))
% 0.75/0.96      | ~ l1_struct_0(sK1)
% 0.75/0.96      | v2_struct_0(sK2)
% 0.75/0.96      | v2_struct_0(sK1)
% 0.75/0.96      | sK0(X0,sK1,sK2) = X0 ),
% 0.75/0.96      inference(unflattening,[status(thm)],[c_197]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_202,plain,
% 0.75/0.96      ( ~ r2_hidden(X0,a_2_1_yellow19(sK1,sK2)) | sK0(X0,sK1,sK2) = X0 ),
% 0.75/0.96      inference(global_propositional_subsumption,
% 0.75/0.96                [status(thm)],
% 0.75/0.96                [c_198,c_11,c_10,c_9]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_423,plain,
% 0.75/0.96      ( ~ r2_hidden(X0_42,a_2_1_yellow19(sK1,sK2))
% 0.75/0.96      | sK0(X0_42,sK1,sK2) = X0_42 ),
% 0.75/0.96      inference(subtyping,[status(esa)],[c_202]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_585,plain,
% 0.75/0.96      ( sK0(X0_42,sK1,sK2) = X0_42
% 0.75/0.96      | r2_hidden(X0_42,a_2_1_yellow19(sK1,sK2)) != iProver_top ),
% 0.75/0.96      inference(predicate_to_equality,[status(thm)],[c_423]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_596,plain,
% 0.75/0.96      ( sK0(X0_42,sK1,sK2) = X0_42
% 0.75/0.96      | r2_hidden(X0_42,k2_yellow19(sK1,sK2)) != iProver_top ),
% 0.75/0.96      inference(light_normalisation,[status(thm)],[c_585,c_425]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_629,plain,
% 0.75/0.96      ( sK0(sK3,sK1,sK2) = sK3
% 0.75/0.96      | r2_hidden(sK3,k2_yellow19(sK1,sK2)) != iProver_top ),
% 0.75/0.96      inference(instantiation,[status(thm)],[c_596]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_428,plain,
% 0.75/0.96      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.75/0.96      | ~ r2_hidden(sK3,k2_yellow19(sK1,sK2))
% 0.75/0.96      | sP0_iProver_split ),
% 0.75/0.96      inference(splitting,
% 0.75/0.96                [splitting(split),new_symbols(definition,[])],
% 0.75/0.96                [c_420]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_588,plain,
% 0.75/0.96      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 0.75/0.96      | r2_hidden(sK3,k2_yellow19(sK1,sK2)) != iProver_top
% 0.75/0.96      | sP0_iProver_split = iProver_top ),
% 0.75/0.96      inference(predicate_to_equality,[status(thm)],[c_428]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_617,plain,
% 0.75/0.96      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 0.75/0.96      | sP0_iProver_split = iProver_top ),
% 0.75/0.96      inference(forward_subsumption_resolution,
% 0.75/0.96                [status(thm)],
% 0.75/0.96                [c_588,c_601]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_627,plain,
% 0.75/0.96      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.75/0.96      | sP0_iProver_split ),
% 0.75/0.96      inference(predicate_to_equality_rev,[status(thm)],[c_617]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_430,plain,( X0_42 = X0_42 ),theory(equality) ).
% 0.75/0.96  
% 0.75/0.96  cnf(c_439,plain,
% 0.75/0.96      ( sK3 = sK3 ),
% 0.75/0.96      inference(instantiation,[status(thm)],[c_430]) ).
% 0.75/0.96  
% 0.75/0.96  cnf(contradiction,plain,
% 0.75/0.96      ( $false ),
% 0.75/0.96      inference(minisat,
% 0.75/0.96                [status(thm)],
% 0.75/0.96                [c_686,c_652,c_640,c_637,c_601,c_636,c_629,c_627,c_439]) ).
% 0.75/0.96  
% 0.75/0.96  
% 0.75/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 0.75/0.96  
% 0.75/0.96  ------                               Statistics
% 0.75/0.96  
% 0.75/0.96  ------ General
% 0.75/0.96  
% 0.75/0.96  abstr_ref_over_cycles:                  0
% 0.75/0.96  abstr_ref_under_cycles:                 0
% 0.75/0.96  gc_basic_clause_elim:                   0
% 0.75/0.96  forced_gc_time:                         0
% 0.75/0.96  parsing_time:                           0.007
% 0.75/0.96  unif_index_cands_time:                  0.
% 0.75/0.96  unif_index_add_time:                    0.
% 0.75/0.96  orderings_time:                         0.
% 0.75/0.96  out_proof_time:                         0.01
% 0.75/0.96  total_time:                             0.053
% 0.75/0.96  num_of_symbols:                         49
% 0.75/0.96  num_of_terms:                           600
% 0.75/0.96  
% 0.75/0.96  ------ Preprocessing
% 0.75/0.96  
% 0.75/0.96  num_of_splits:                          1
% 0.75/0.96  num_of_split_atoms:                     1
% 0.75/0.96  num_of_reused_defs:                     0
% 0.75/0.96  num_eq_ax_congr_red:                    16
% 0.75/0.96  num_of_sem_filtered_clauses:            1
% 0.75/0.96  num_of_subtypes:                        6
% 0.75/0.96  monotx_restored_types:                  0
% 0.75/0.96  sat_num_of_epr_types:                   0
% 0.75/0.96  sat_num_of_non_cyclic_types:            0
% 0.75/0.96  sat_guarded_non_collapsed_types:        1
% 0.75/0.96  num_pure_diseq_elim:                    0
% 0.75/0.96  simp_replaced_by:                       0
% 0.75/0.96  res_preprocessed:                       48
% 0.75/0.96  prep_upred:                             0
% 0.75/0.96  prep_unflattend:                        12
% 0.75/0.96  smt_new_axioms:                         0
% 0.75/0.96  pred_elim_cands:                        2
% 0.75/0.96  pred_elim:                              4
% 0.75/0.96  pred_elim_cl:                           5
% 0.75/0.96  pred_elim_cycles:                       6
% 0.75/0.96  merged_defs:                            0
% 0.75/0.96  merged_defs_ncl:                        0
% 0.75/0.96  bin_hyper_res:                          0
% 0.75/0.96  prep_cycles:                            4
% 0.75/0.96  pred_elim_time:                         0.005
% 0.75/0.96  splitting_time:                         0.
% 0.75/0.96  sem_filter_time:                        0.
% 0.75/0.96  monotx_time:                            0.
% 0.75/0.96  subtype_inf_time:                       0.
% 0.75/0.96  
% 0.75/0.96  ------ Problem properties
% 0.75/0.96  
% 0.75/0.96  clauses:                                8
% 0.75/0.96  conjectures:                            1
% 0.75/0.96  epr:                                    0
% 0.75/0.96  horn:                                   6
% 0.75/0.96  ground:                                 4
% 0.75/0.96  unary:                                  1
% 0.75/0.96  binary:                                 5
% 0.75/0.96  lits:                                   17
% 0.75/0.96  lits_eq:                                3
% 0.75/0.96  fd_pure:                                0
% 0.75/0.96  fd_pseudo:                              0
% 0.75/0.96  fd_cond:                                0
% 0.75/0.96  fd_pseudo_cond:                         0
% 0.75/0.96  ac_symbols:                             0
% 0.75/0.96  
% 0.75/0.96  ------ Propositional Solver
% 0.75/0.96  
% 0.75/0.96  prop_solver_calls:                      23
% 0.75/0.96  prop_fast_solver_calls:                 309
% 0.75/0.96  smt_solver_calls:                       0
% 0.75/0.96  smt_fast_solver_calls:                  0
% 0.75/0.96  prop_num_of_clauses:                    174
% 0.75/0.96  prop_preprocess_simplified:             1096
% 0.75/0.96  prop_fo_subsumed:                       17
% 0.75/0.96  prop_solver_time:                       0.
% 0.75/0.96  smt_solver_time:                        0.
% 0.75/0.96  smt_fast_solver_time:                   0.
% 0.75/0.96  prop_fast_solver_time:                  0.
% 0.75/0.96  prop_unsat_core_time:                   0.
% 0.75/0.96  
% 0.75/0.96  ------ QBF
% 0.75/0.96  
% 0.75/0.96  qbf_q_res:                              0
% 0.75/0.96  qbf_num_tautologies:                    0
% 0.75/0.96  qbf_prep_cycles:                        0
% 0.75/0.96  
% 0.75/0.96  ------ BMC1
% 0.75/0.96  
% 0.75/0.96  bmc1_current_bound:                     -1
% 0.75/0.96  bmc1_last_solved_bound:                 -1
% 0.75/0.96  bmc1_unsat_core_size:                   -1
% 0.75/0.96  bmc1_unsat_core_parents_size:           -1
% 0.75/0.96  bmc1_merge_next_fun:                    0
% 0.75/0.96  bmc1_unsat_core_clauses_time:           0.
% 0.75/0.96  
% 0.75/0.96  ------ Instantiation
% 0.75/0.96  
% 0.75/0.96  inst_num_of_clauses:                    22
% 0.75/0.96  inst_num_in_passive:                    0
% 0.75/0.96  inst_num_in_active:                     15
% 0.75/0.96  inst_num_in_unprocessed:                6
% 0.75/0.96  inst_num_of_loops:                      17
% 0.75/0.96  inst_num_of_learning_restarts:          0
% 0.75/0.96  inst_num_moves_active_passive:          0
% 0.75/0.96  inst_lit_activity:                      0
% 0.75/0.96  inst_lit_activity_moves:                0
% 0.75/0.96  inst_num_tautologies:                   0
% 0.75/0.96  inst_num_prop_implied:                  0
% 0.75/0.96  inst_num_existing_simplified:           0
% 0.75/0.96  inst_num_eq_res_simplified:             0
% 0.75/0.96  inst_num_child_elim:                    0
% 0.75/0.96  inst_num_of_dismatching_blockings:      0
% 0.75/0.96  inst_num_of_non_proper_insts:           5
% 0.75/0.96  inst_num_of_duplicates:                 0
% 0.75/0.96  inst_inst_num_from_inst_to_res:         0
% 0.75/0.96  inst_dismatching_checking_time:         0.
% 0.75/0.96  
% 0.75/0.96  ------ Resolution
% 0.75/0.96  
% 0.75/0.96  res_num_of_clauses:                     0
% 0.75/0.96  res_num_in_passive:                     0
% 0.75/0.96  res_num_in_active:                      0
% 0.75/0.96  res_num_of_loops:                       52
% 0.75/0.96  res_forward_subset_subsumed:            0
% 0.75/0.96  res_backward_subset_subsumed:           0
% 0.75/0.96  res_forward_subsumed:                   0
% 0.75/0.96  res_backward_subsumed:                  0
% 0.75/0.96  res_forward_subsumption_resolution:     0
% 0.75/0.96  res_backward_subsumption_resolution:    0
% 0.75/0.96  res_clause_to_clause_subsumption:       16
% 0.75/0.96  res_orphan_elimination:                 0
% 0.75/0.96  res_tautology_del:                      4
% 0.75/0.96  res_num_eq_res_simplified:              1
% 0.75/0.96  res_num_sel_changes:                    0
% 0.75/0.96  res_moves_from_active_to_pass:          0
% 0.75/0.96  
% 0.75/0.96  ------ Superposition
% 0.75/0.96  
% 0.75/0.96  sup_time_total:                         0.
% 0.75/0.96  sup_time_generating:                    0.
% 0.75/0.96  sup_time_sim_full:                      0.
% 0.75/0.96  sup_time_sim_immed:                     0.
% 0.75/0.96  
% 0.75/0.96  sup_num_of_clauses:                     7
% 0.75/0.96  sup_num_in_active:                      2
% 0.75/0.96  sup_num_in_passive:                     5
% 0.75/0.96  sup_num_of_loops:                       2
% 0.75/0.96  sup_fw_superposition:                   0
% 0.75/0.96  sup_bw_superposition:                   0
% 0.75/0.96  sup_immediate_simplified:               0
% 0.75/0.96  sup_given_eliminated:                   0
% 0.75/0.96  comparisons_done:                       0
% 0.75/0.96  comparisons_avoided:                    0
% 0.75/0.96  
% 0.75/0.96  ------ Simplifications
% 0.75/0.96  
% 0.75/0.96  
% 0.75/0.96  sim_fw_subset_subsumed:                 0
% 0.75/0.96  sim_bw_subset_subsumed:                 0
% 0.75/0.96  sim_fw_subsumed:                        0
% 0.75/0.96  sim_bw_subsumed:                        1
% 0.75/0.96  sim_fw_subsumption_res:                 1
% 0.75/0.96  sim_bw_subsumption_res:                 0
% 0.75/0.96  sim_tautology_del:                      0
% 0.75/0.96  sim_eq_tautology_del:                   0
% 0.75/0.96  sim_eq_res_simp:                        0
% 0.75/0.96  sim_fw_demodulated:                     0
% 0.75/0.96  sim_bw_demodulated:                     0
% 0.75/0.96  sim_light_normalised:                   5
% 0.75/0.96  sim_joinable_taut:                      0
% 0.75/0.96  sim_joinable_simp:                      0
% 0.75/0.96  sim_ac_normalised:                      0
% 0.75/0.96  sim_smt_subsumption:                    0
% 0.75/0.96  
%------------------------------------------------------------------------------
