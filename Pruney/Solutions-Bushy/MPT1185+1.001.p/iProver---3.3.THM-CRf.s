%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1185+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:06 EST 2020

% Result     : Theorem 0.38s
% Output     : CNFRefutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 295 expanded)
%              Number of clauses        :   36 (  64 expanded)
%              Number of leaves         :   13 (  67 expanded)
%              Depth                    :   17
%              Number of atoms          :  319 (1429 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(X1,X0)
          & r8_relat_2(X2,X0) )
       => r8_relat_2(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r8_relat_2(X2,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r8_relat_2(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r8_relat_2(X2,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r8_relat_2(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r8_relat_2(X2,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r8_relat_2(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X1,X0) )
         => r3_orders_1(u1_orders_2(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v6_orders_2(X1,X0) )
           => r3_orders_1(u1_orders_2(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f14,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v6_orders_2(X1,X0) )
           => r3_orders_1(u1_orders_2(X0),X1) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f15,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v6_orders_2(X1,X0) )
           => r3_orders_1(u1_orders_2(X0),X1) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r3_orders_1(u1_orders_2(X0),X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v6_orders_2(X1,X0) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r3_orders_1(u1_orders_2(X0),X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v6_orders_2(X1,X0) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(flattening,[],[f28])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r3_orders_1(u1_orders_2(X0),X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v6_orders_2(X1,X0) )
     => ( ~ r3_orders_1(u1_orders_2(X0),sK1)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        & v6_orders_2(sK1,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r3_orders_1(u1_orders_2(X0),X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X1,X0) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0) )
   => ( ? [X1] :
          ( ~ r3_orders_1(u1_orders_2(sK0),X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & v6_orders_2(X1,sK0) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ~ r3_orders_1(u1_orders_2(sK0),sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & v6_orders_2(sK1,sK0)
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f38,f37])).

fof(f63,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f61,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(X1,X0)
          & r4_relat_2(X2,X0) )
       => r4_relat_2(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r4_relat_2(X2,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r4_relat_2(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r4_relat_2(X2,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r4_relat_2(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r4_relat_2(X2,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r4_relat_2(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r3_orders_1(X0,X1)
        <=> ( r6_relat_2(X0,X1)
            & r4_relat_2(X0,X1)
            & r8_relat_2(X0,X1)
            & r1_relat_2(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r3_orders_1(X0,X1)
        <=> ( r6_relat_2(X0,X1)
            & r4_relat_2(X0,X1)
            & r8_relat_2(X0,X1)
            & r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r3_orders_1(X0,X1)
            | ~ r6_relat_2(X0,X1)
            | ~ r4_relat_2(X0,X1)
            | ~ r8_relat_2(X0,X1)
            | ~ r1_relat_2(X0,X1) )
          & ( ( r6_relat_2(X0,X1)
              & r4_relat_2(X0,X1)
              & r8_relat_2(X0,X1)
              & r1_relat_2(X0,X1) )
            | ~ r3_orders_1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r3_orders_1(X0,X1)
            | ~ r6_relat_2(X0,X1)
            | ~ r4_relat_2(X0,X1)
            | ~ r8_relat_2(X0,X1)
            | ~ r1_relat_2(X0,X1) )
          & ( ( r6_relat_2(X0,X1)
              & r4_relat_2(X0,X1)
              & r8_relat_2(X0,X1)
              & r1_relat_2(X0,X1) )
            | ~ r3_orders_1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r3_orders_1(X0,X1)
      | ~ r6_relat_2(X0,X1)
      | ~ r4_relat_2(X0,X1)
      | ~ r8_relat_2(X0,X1)
      | ~ r1_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r7_relat_2(X1,X0)
      <=> ( r6_relat_2(X1,X0)
          & r1_relat_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r7_relat_2(X1,X0)
      <=> ( r6_relat_2(X1,X0)
          & r1_relat_2(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( r7_relat_2(X1,X0)
          | ~ r6_relat_2(X1,X0)
          | ~ r1_relat_2(X1,X0) )
        & ( ( r6_relat_2(X1,X0)
            & r1_relat_2(X1,X0) )
          | ~ r7_relat_2(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( r7_relat_2(X1,X0)
          | ~ r6_relat_2(X1,X0)
          | ~ r1_relat_2(X1,X0) )
        & ( ( r6_relat_2(X1,X0)
            & r1_relat_2(X1,X0) )
          | ~ r7_relat_2(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r6_relat_2(X1,X0)
      | ~ r7_relat_2(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f62,plain,(
    v6_orders_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_orders_2(X1,X0)
              | ~ r7_relat_2(u1_orders_2(X0),X1) )
            & ( r7_relat_2(u1_orders_2(X0),X1)
              | ~ v6_orders_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r7_relat_2(u1_orders_2(X0),X1)
      | ~ v6_orders_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f64,plain,(
    ~ r3_orders_1(u1_orders_2(sK0),sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_relat_2(X1,X0)
      | ~ r7_relat_2(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v4_orders_2(X0)
      <=> r8_relat_2(u1_orders_2(X0),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( v4_orders_2(X0)
      <=> r8_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X0] :
      ( ( ( v4_orders_2(X0)
          | ~ r8_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
        & ( r8_relat_2(u1_orders_2(X0),u1_struct_0(X0))
          | ~ v4_orders_2(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f43,plain,(
    ! [X0] :
      ( r8_relat_2(u1_orders_2(X0),u1_struct_0(X0))
      | ~ v4_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v5_orders_2(X0)
      <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( v5_orders_2(X0)
      <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f32,plain,(
    ! [X0] :
      ( ( ( v5_orders_2(X0)
          | ~ r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
        & ( r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))
          | ~ v5_orders_2(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f45,plain,(
    ! [X0] :
      ( r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f60,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f59,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_18,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r8_relat_2(X2,X1)
    | r8_relat_2(X2,X0)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_13,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_347,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[status(thm)],[c_13,c_20])).

cnf(c_365,plain,
    ( ~ r8_relat_2(X0,u1_struct_0(sK0))
    | r8_relat_2(X0,sK1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_18,c_347])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_12,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_22,negated_conjecture,
    ( l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_284,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(resolution,[status(thm)],[c_12,c_22])).

cnf(c_341,plain,
    ( v1_relat_1(u1_orders_2(sK0)) ),
    inference(resolution,[status(thm)],[c_0,c_284])).

cnf(c_508,plain,
    ( ~ r8_relat_2(u1_orders_2(sK0),u1_struct_0(sK0))
    | r8_relat_2(u1_orders_2(sK0),sK1) ),
    inference(resolution,[status(thm)],[c_365,c_341])).

cnf(c_17,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r4_relat_2(X2,X1)
    | r4_relat_2(X2,X0)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_379,plain,
    ( ~ r4_relat_2(X0,u1_struct_0(sK0))
    | r4_relat_2(X0,sK1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_17,c_347])).

cnf(c_498,plain,
    ( ~ r4_relat_2(u1_orders_2(sK0),u1_struct_0(sK0))
    | r4_relat_2(u1_orders_2(sK0),sK1) ),
    inference(resolution,[status(thm)],[c_379,c_341])).

cnf(c_7,plain,
    ( ~ r1_relat_2(X0,X1)
    | ~ r6_relat_2(X0,X1)
    | r3_orders_1(X0,X1)
    | ~ r4_relat_2(X0,X1)
    | ~ r8_relat_2(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_15,plain,
    ( r6_relat_2(X0,X1)
    | ~ r7_relat_2(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_21,negated_conjecture,
    ( v6_orders_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2,plain,
    ( r7_relat_2(u1_orders_2(X0),X1)
    | ~ v6_orders_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_290,plain,
    ( r7_relat_2(u1_orders_2(sK0),X0)
    | ~ v6_orders_2(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[status(thm)],[c_2,c_22])).

cnf(c_329,plain,
    ( r7_relat_2(u1_orders_2(sK0),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[status(thm)],[c_21,c_290])).

cnf(c_331,plain,
    ( r7_relat_2(u1_orders_2(sK0),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_329,c_20])).

cnf(c_449,plain,
    ( r6_relat_2(u1_orders_2(sK0),sK1)
    | ~ v1_relat_1(u1_orders_2(sK0)) ),
    inference(resolution,[status(thm)],[c_15,c_331])).

cnf(c_451,plain,
    ( r6_relat_2(u1_orders_2(sK0),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_449,c_341])).

cnf(c_464,plain,
    ( ~ r1_relat_2(u1_orders_2(sK0),sK1)
    | r3_orders_1(u1_orders_2(sK0),sK1)
    | ~ r4_relat_2(u1_orders_2(sK0),sK1)
    | ~ r8_relat_2(u1_orders_2(sK0),sK1)
    | ~ v1_relat_1(u1_orders_2(sK0)) ),
    inference(resolution,[status(thm)],[c_7,c_451])).

cnf(c_19,negated_conjecture,
    ( ~ r3_orders_1(u1_orders_2(sK0),sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_16,plain,
    ( r1_relat_2(X0,X1)
    | ~ r7_relat_2(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_439,plain,
    ( r1_relat_2(u1_orders_2(sK0),sK1)
    | ~ v1_relat_1(u1_orders_2(sK0)) ),
    inference(resolution,[status(thm)],[c_16,c_331])).

cnf(c_466,plain,
    ( ~ r8_relat_2(u1_orders_2(sK0),sK1)
    | ~ r4_relat_2(u1_orders_2(sK0),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_464,c_19,c_341,c_439])).

cnf(c_467,plain,
    ( ~ r4_relat_2(u1_orders_2(sK0),sK1)
    | ~ r8_relat_2(u1_orders_2(sK0),sK1) ),
    inference(renaming,[status(thm)],[c_466])).

cnf(c_4,plain,
    ( r8_relat_2(u1_orders_2(X0),u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_68,plain,
    ( r8_relat_2(u1_orders_2(sK0),u1_struct_0(sK0))
    | ~ v4_orders_2(sK0)
    | ~ l1_orders_2(sK0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_6,plain,
    ( r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_64,plain,
    ( r4_relat_2(u1_orders_2(sK0),u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_23,negated_conjecture,
    ( v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_24,negated_conjecture,
    ( v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_508,c_498,c_467,c_68,c_64,c_22,c_23,c_24])).


%------------------------------------------------------------------------------
