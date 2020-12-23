%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1156+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:02 EST 2020

% Result     : Theorem 19.75s
% Output     : CNFRefutation 19.75s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 298 expanded)
%              Number of clauses        :   35 ( 108 expanded)
%              Number of leaves         :   16 (  78 expanded)
%              Depth                    :   11
%              Number of atoms          :  244 (1159 expanded)
%              Number of equality atoms :   91 ( 147 expanded)
%              Maximal formula depth    :   47 (   5 average)
%              Maximal clause size      :   68 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t50_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ~ r2_hidden(X2,k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_orders_2)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT016+2.ax',fc2_struct_0)).

fof(dt_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(t49_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ~ ( r2_hidden(X2,X3)
                  & r2_hidden(X2,k2_orders_2(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_orders_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT006+2.ax',t4_subset)).

fof(d13_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_orders_2(X1,X2) = a_2_1_orders_2(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_orders_2)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t75_enumset1)).

fof(d6_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( X9 = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)
    <=> ! [X10] :
          ( r2_hidden(X10,X9)
        <=> ~ ( X10 != X1
              & X10 != X2
              & X10 != X3
              & X10 != X4
              & X10 != X5
              & X10 != X6
              & X10 != X7
              & X10 != X8 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT005+2.ax',d6_enumset1)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ~ r2_hidden(X2,k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t50_orders_2])).

fof(c_0_17,plain,(
    ! [X765] :
      ( ~ l1_orders_2(X765)
      | l1_struct_0(X765) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

fof(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v3_orders_2(esk1_0)
    & v4_orders_2(esk1_0)
    & v5_orders_2(esk1_0)
    & l1_orders_2(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & r2_hidden(esk2_0,k2_orders_2(esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).

fof(c_0_19,plain,(
    ! [X684] :
      ( v2_struct_0(X684)
      | ~ l1_struct_0(X684)
      | ~ v1_xboole_0(u1_struct_0(X684)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_20,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,plain,(
    ! [X672,X673] :
      ( v1_xboole_0(X672)
      | ~ m1_subset_1(X673,X672)
      | m1_subset_1(k6_domain_1(X672,X673),k1_zfmisc_1(X672)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

cnf(c_0_23,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_26,plain,(
    ! [X669,X670,X671] :
      ( v2_struct_0(X669)
      | ~ v3_orders_2(X669)
      | ~ v4_orders_2(X669)
      | ~ v5_orders_2(X669)
      | ~ l1_orders_2(X669)
      | ~ m1_subset_1(X670,u1_struct_0(X669))
      | ~ m1_subset_1(X671,k1_zfmisc_1(u1_struct_0(X669)))
      | ~ r2_hidden(X670,X671)
      | ~ r2_hidden(X670,k2_orders_2(X669,X671)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_orders_2])])])])).

fof(c_0_27,plain,(
    ! [X357,X358,X359] :
      ( ~ r2_hidden(X357,X358)
      | ~ m1_subset_1(X358,k1_zfmisc_1(X359))
      | m1_subset_1(X357,X359) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_28,plain,(
    ! [X663,X664] :
      ( v2_struct_0(X663)
      | ~ v3_orders_2(X663)
      | ~ v4_orders_2(X663)
      | ~ v5_orders_2(X663)
      | ~ l1_orders_2(X663)
      | ~ m1_subset_1(X664,k1_zfmisc_1(u1_struct_0(X663)))
      | k2_orders_2(X663,X664) = a_2_1_orders_2(X663,X664) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_orders_2])])])])).

cnf(c_0_29,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_31,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

fof(c_0_32,plain,(
    ! [X674,X675] :
      ( v1_xboole_0(X674)
      | ~ m1_subset_1(X675,X674)
      | k6_domain_1(X674,X675) = k1_tarski(X675) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_33,plain,(
    ! [X1941] : k2_tarski(X1941,X1941) = k1_tarski(X1941) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_34,plain,(
    ! [X2067,X2068] : k1_enumset1(X2067,X2067,X2068) = k2_tarski(X2067,X2068) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_35,plain,(
    ! [X3209,X3210,X3211] : k2_enumset1(X3209,X3209,X3210,X3211) = k1_enumset1(X3209,X3210,X3211) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_36,plain,(
    ! [X3359,X3360,X3361,X3362] : k3_enumset1(X3359,X3359,X3360,X3361,X3362) = k2_enumset1(X3359,X3360,X3361,X3362) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_37,plain,(
    ! [X4580,X4581,X4582,X4583,X4584] : k4_enumset1(X4580,X4580,X4581,X4582,X4583,X4584) = k3_enumset1(X4580,X4581,X4582,X4583,X4584) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_38,plain,(
    ! [X4636,X4637,X4638,X4639,X4640,X4641] : k5_enumset1(X4636,X4636,X4637,X4638,X4639,X4640,X4641) = k4_enumset1(X4636,X4637,X4638,X4639,X4640,X4641) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_39,plain,(
    ! [X4713,X4714,X4715,X4716,X4717,X4718,X4719] : k6_enumset1(X4713,X4713,X4714,X4715,X4716,X4717,X4718,X4719) = k5_enumset1(X4713,X4714,X4715,X4716,X4717,X4718,X4719) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

cnf(c_0_40,plain,
    ( v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X2,k2_orders_2(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_41,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_42,plain,
    ( v2_struct_0(X1)
    | k2_orders_2(X1,X2) = a_2_1_orders_2(X1,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(k6_domain_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

cnf(c_0_44,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_45,negated_conjecture,
    ( v4_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_46,negated_conjecture,
    ( v3_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_47,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_48,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_49,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_50,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_51,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_52,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_53,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_54,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_55,plain,
    ( v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,k2_orders_2(X1,X2))
    | ~ r2_hidden(X3,X2) ),
    inference(csr,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_56,negated_conjecture,
    ( k2_orders_2(esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0)) = a_2_1_orders_2(esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_21])]),c_0_25])).

cnf(c_0_57,plain,
    ( k6_domain_1(X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_50]),c_0_51]),c_0_52]),c_0_53]),c_0_54])).

fof(c_0_58,plain,(
    ! [X4774,X4775,X4776,X4777,X4778,X4779,X4780,X4781,X4782,X4783,X4784,X4785,X4786,X4787,X4788,X4789,X4790,X4791,X4792,X4793] :
      ( ( ~ r2_hidden(X4783,X4782)
        | X4783 = X4774
        | X4783 = X4775
        | X4783 = X4776
        | X4783 = X4777
        | X4783 = X4778
        | X4783 = X4779
        | X4783 = X4780
        | X4783 = X4781
        | X4782 != k6_enumset1(X4774,X4775,X4776,X4777,X4778,X4779,X4780,X4781) )
      & ( X4784 != X4774
        | r2_hidden(X4784,X4782)
        | X4782 != k6_enumset1(X4774,X4775,X4776,X4777,X4778,X4779,X4780,X4781) )
      & ( X4784 != X4775
        | r2_hidden(X4784,X4782)
        | X4782 != k6_enumset1(X4774,X4775,X4776,X4777,X4778,X4779,X4780,X4781) )
      & ( X4784 != X4776
        | r2_hidden(X4784,X4782)
        | X4782 != k6_enumset1(X4774,X4775,X4776,X4777,X4778,X4779,X4780,X4781) )
      & ( X4784 != X4777
        | r2_hidden(X4784,X4782)
        | X4782 != k6_enumset1(X4774,X4775,X4776,X4777,X4778,X4779,X4780,X4781) )
      & ( X4784 != X4778
        | r2_hidden(X4784,X4782)
        | X4782 != k6_enumset1(X4774,X4775,X4776,X4777,X4778,X4779,X4780,X4781) )
      & ( X4784 != X4779
        | r2_hidden(X4784,X4782)
        | X4782 != k6_enumset1(X4774,X4775,X4776,X4777,X4778,X4779,X4780,X4781) )
      & ( X4784 != X4780
        | r2_hidden(X4784,X4782)
        | X4782 != k6_enumset1(X4774,X4775,X4776,X4777,X4778,X4779,X4780,X4781) )
      & ( X4784 != X4781
        | r2_hidden(X4784,X4782)
        | X4782 != k6_enumset1(X4774,X4775,X4776,X4777,X4778,X4779,X4780,X4781) )
      & ( esk496_9(X4785,X4786,X4787,X4788,X4789,X4790,X4791,X4792,X4793) != X4785
        | ~ r2_hidden(esk496_9(X4785,X4786,X4787,X4788,X4789,X4790,X4791,X4792,X4793),X4793)
        | X4793 = k6_enumset1(X4785,X4786,X4787,X4788,X4789,X4790,X4791,X4792) )
      & ( esk496_9(X4785,X4786,X4787,X4788,X4789,X4790,X4791,X4792,X4793) != X4786
        | ~ r2_hidden(esk496_9(X4785,X4786,X4787,X4788,X4789,X4790,X4791,X4792,X4793),X4793)
        | X4793 = k6_enumset1(X4785,X4786,X4787,X4788,X4789,X4790,X4791,X4792) )
      & ( esk496_9(X4785,X4786,X4787,X4788,X4789,X4790,X4791,X4792,X4793) != X4787
        | ~ r2_hidden(esk496_9(X4785,X4786,X4787,X4788,X4789,X4790,X4791,X4792,X4793),X4793)
        | X4793 = k6_enumset1(X4785,X4786,X4787,X4788,X4789,X4790,X4791,X4792) )
      & ( esk496_9(X4785,X4786,X4787,X4788,X4789,X4790,X4791,X4792,X4793) != X4788
        | ~ r2_hidden(esk496_9(X4785,X4786,X4787,X4788,X4789,X4790,X4791,X4792,X4793),X4793)
        | X4793 = k6_enumset1(X4785,X4786,X4787,X4788,X4789,X4790,X4791,X4792) )
      & ( esk496_9(X4785,X4786,X4787,X4788,X4789,X4790,X4791,X4792,X4793) != X4789
        | ~ r2_hidden(esk496_9(X4785,X4786,X4787,X4788,X4789,X4790,X4791,X4792,X4793),X4793)
        | X4793 = k6_enumset1(X4785,X4786,X4787,X4788,X4789,X4790,X4791,X4792) )
      & ( esk496_9(X4785,X4786,X4787,X4788,X4789,X4790,X4791,X4792,X4793) != X4790
        | ~ r2_hidden(esk496_9(X4785,X4786,X4787,X4788,X4789,X4790,X4791,X4792,X4793),X4793)
        | X4793 = k6_enumset1(X4785,X4786,X4787,X4788,X4789,X4790,X4791,X4792) )
      & ( esk496_9(X4785,X4786,X4787,X4788,X4789,X4790,X4791,X4792,X4793) != X4791
        | ~ r2_hidden(esk496_9(X4785,X4786,X4787,X4788,X4789,X4790,X4791,X4792,X4793),X4793)
        | X4793 = k6_enumset1(X4785,X4786,X4787,X4788,X4789,X4790,X4791,X4792) )
      & ( esk496_9(X4785,X4786,X4787,X4788,X4789,X4790,X4791,X4792,X4793) != X4792
        | ~ r2_hidden(esk496_9(X4785,X4786,X4787,X4788,X4789,X4790,X4791,X4792,X4793),X4793)
        | X4793 = k6_enumset1(X4785,X4786,X4787,X4788,X4789,X4790,X4791,X4792) )
      & ( r2_hidden(esk496_9(X4785,X4786,X4787,X4788,X4789,X4790,X4791,X4792,X4793),X4793)
        | esk496_9(X4785,X4786,X4787,X4788,X4789,X4790,X4791,X4792,X4793) = X4785
        | esk496_9(X4785,X4786,X4787,X4788,X4789,X4790,X4791,X4792,X4793) = X4786
        | esk496_9(X4785,X4786,X4787,X4788,X4789,X4790,X4791,X4792,X4793) = X4787
        | esk496_9(X4785,X4786,X4787,X4788,X4789,X4790,X4791,X4792,X4793) = X4788
        | esk496_9(X4785,X4786,X4787,X4788,X4789,X4790,X4791,X4792,X4793) = X4789
        | esk496_9(X4785,X4786,X4787,X4788,X4789,X4790,X4791,X4792,X4793) = X4790
        | esk496_9(X4785,X4786,X4787,X4788,X4789,X4790,X4791,X4792,X4793) = X4791
        | esk496_9(X4785,X4786,X4787,X4788,X4789,X4790,X4791,X4792,X4793) = X4792
        | X4793 = k6_enumset1(X4785,X4786,X4787,X4788,X4789,X4790,X4791,X4792) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).

cnf(c_0_59,negated_conjecture,
    ( ~ r2_hidden(X1,a_2_1_orders_2(esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0)))
    | ~ r2_hidden(X1,k6_domain_1(u1_struct_0(esk1_0),esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_21]),c_0_56])]),c_0_25])).

cnf(c_0_60,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk1_0),esk2_0) = k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_30]),c_0_31])).

cnf(c_0_61,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X4,X5,X2,X6,X7,X8,X9,X10) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk2_0,k2_orders_2(esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_63,negated_conjecture,
    ( ~ r2_hidden(X1,a_2_1_orders_2(esk1_0,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)))
    | ~ r2_hidden(X1,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_60]),c_0_60])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,k6_enumset1(X2,X3,X1,X4,X5,X6,X7,X8)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_61])])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk2_0,a_2_1_orders_2(esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0))) ),
    inference(rw,[status(thm)],[c_0_62,c_0_56])).

cnf(c_0_66,negated_conjecture,
    ( ~ r2_hidden(esk2_0,a_2_1_orders_2(esk1_0,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_60]),c_0_66]),
    [proof]).
%------------------------------------------------------------------------------
