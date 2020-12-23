%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1145+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:00 EST 2020

% Result     : Theorem 0.64s
% Output     : CNFRefutation 0.64s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 123 expanded)
%              Number of clauses        :   21 (  24 expanded)
%              Number of leaves         :    8 (  41 expanded)
%              Depth                    :   10
%              Number of atoms          :  170 ( 742 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(X1,X0)
          & r7_relat_2(X2,X0) )
       => r7_relat_2(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r7_relat_2(X2,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r7_relat_2(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r7_relat_2(X2,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r7_relat_2(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r7_relat_2(X2,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r7_relat_2(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f5,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X1,X0) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X2,X1)
               => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & v6_orders_2(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v6_orders_2(X1,X0) )
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r1_tarski(X2,X1)
                 => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                    & v6_orders_2(X2,X0) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                | ~ v6_orders_2(X2,X0) )
              & r1_tarski(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v6_orders_2(X1,X0) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                | ~ v6_orders_2(X2,X0) )
              & r1_tarski(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v6_orders_2(X1,X0) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v6_orders_2(X2,X0) )
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v6_orders_2(sK2,X0) )
        & r1_tarski(sK2,X1)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                | ~ v6_orders_2(X2,X0) )
              & r1_tarski(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v6_orders_2(X1,X0) )
     => ( ? [X2] :
            ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
            & r1_tarski(X2,sK1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        & v6_orders_2(sK1,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v6_orders_2(X2,X0) )
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X1,X0) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
                | ~ v6_orders_2(X2,sK0) )
              & r1_tarski(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & v6_orders_2(X1,sK0) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v6_orders_2(sK2,sK0) )
    & r1_tarski(sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & v6_orders_2(sK1,sK0)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f17,f16,f15])).

fof(f28,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f24,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f25,plain,(
    v6_orders_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_orders_2(X1,X0)
              | ~ r7_relat_2(u1_orders_2(X0),X1) )
            & ( r7_relat_2(u1_orders_2(X0),X1)
              | ~ v6_orders_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r7_relat_2(u1_orders_2(X0),X1)
      | ~ v6_orders_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f29,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v6_orders_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f27,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v6_orders_2(X1,X0)
      | ~ r7_relat_2(u1_orders_2(X0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f26,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r7_relat_2(X2,X1)
    | r7_relat_2(X2,X0)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_6,negated_conjecture,
    ( r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_113,plain,
    ( ~ r7_relat_2(X0,sK1)
    | r7_relat_2(X0,sK2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_4,c_6])).

cnf(c_131,plain,
    ( ~ r7_relat_2(X0,sK1)
    | r7_relat_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(resolution,[status(thm)],[c_0,c_113])).

cnf(c_3,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_10,negated_conjecture,
    ( l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_149,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(resolution,[status(thm)],[c_3,c_10])).

cnf(c_218,plain,
    ( ~ r7_relat_2(u1_orders_2(sK0),sK1)
    | r7_relat_2(u1_orders_2(sK0),sK2) ),
    inference(resolution,[status(thm)],[c_131,c_149])).

cnf(c_9,negated_conjecture,
    ( v6_orders_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_2,plain,
    ( r7_relat_2(u1_orders_2(X0),X1)
    | ~ v6_orders_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_155,plain,
    ( r7_relat_2(u1_orders_2(sK0),X0)
    | ~ v6_orders_2(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[status(thm)],[c_2,c_10])).

cnf(c_204,plain,
    ( r7_relat_2(u1_orders_2(sK0),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[status(thm)],[c_9,c_155])).

cnf(c_5,negated_conjecture,
    ( ~ v6_orders_2(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_7,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_58,negated_conjecture,
    ( ~ v6_orders_2(sK2,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5,c_7])).

cnf(c_1,plain,
    ( ~ r7_relat_2(u1_orders_2(X0),X1)
    | v6_orders_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_169,plain,
    ( ~ r7_relat_2(u1_orders_2(sK0),X0)
    | v6_orders_2(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[status(thm)],[c_1,c_10])).

cnf(c_194,plain,
    ( ~ r7_relat_2(u1_orders_2(sK0),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[status(thm)],[c_58,c_169])).

cnf(c_8,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_218,c_204,c_194,c_7,c_8])).


%------------------------------------------------------------------------------
