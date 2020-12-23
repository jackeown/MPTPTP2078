%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT2044+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:09 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   26 ( 233 expanded)
%              Number of clauses        :   19 (  78 expanded)
%              Number of leaves         :    3 (  55 expanded)
%              Depth                    :    9
%              Number of atoms          :  105 (1234 expanded)
%              Number of equality atoms :   10 (  40 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   19 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_yellow19,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( r2_hidden(X3,k1_yellow19(X1,X2))
            <=> m1_connsp_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow19)).

fof(d1_yellow19,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k1_yellow19(X1,X2) = a_2_0_yellow19(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_yellow19)).

fof(fraenkel_a_2_0_yellow19,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & v2_pre_topc(X2)
        & l1_pre_topc(X2)
        & m1_subset_1(X3,u1_struct_0(X2)) )
     => ( r2_hidden(X1,a_2_0_yellow19(X2,X3))
      <=> ? [X4] :
            ( m1_connsp_2(X4,X2,X3)
            & X1 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_yellow19)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( r2_hidden(X3,k1_yellow19(X1,X2))
              <=> m1_connsp_2(X3,X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t3_yellow19])).

fof(c_0_4,plain,(
    ! [X5,X6] :
      ( v2_struct_0(X5)
      | ~ v2_pre_topc(X5)
      | ~ l1_pre_topc(X5)
      | ~ m1_subset_1(X6,u1_struct_0(X5))
      | k1_yellow19(X5,X6) = a_2_0_yellow19(X5,X6) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_yellow19])])])])).

fof(c_0_5,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & ( ~ r2_hidden(esk4_0,k1_yellow19(esk2_0,esk3_0))
      | ~ m1_connsp_2(esk4_0,esk2_0,esk3_0) )
    & ( r2_hidden(esk4_0,k1_yellow19(esk2_0,esk3_0))
      | m1_connsp_2(esk4_0,esk2_0,esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_3])])])])).

fof(c_0_6,plain,(
    ! [X7,X8,X9,X11] :
      ( ( m1_connsp_2(esk1_3(X7,X8,X9),X8,X9)
        | ~ r2_hidden(X7,a_2_0_yellow19(X8,X9))
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | ~ m1_subset_1(X9,u1_struct_0(X8)) )
      & ( X7 = esk1_3(X7,X8,X9)
        | ~ r2_hidden(X7,a_2_0_yellow19(X8,X9))
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | ~ m1_subset_1(X9,u1_struct_0(X8)) )
      & ( ~ m1_connsp_2(X11,X8,X9)
        | X7 != X11
        | r2_hidden(X7,a_2_0_yellow19(X8,X9))
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | ~ m1_subset_1(X9,u1_struct_0(X8)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_0_yellow19])])])])])])).

cnf(c_0_7,plain,
    ( v2_struct_0(X1)
    | k1_yellow19(X1,X2) = a_2_0_yellow19(X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,plain,
    ( r2_hidden(X4,a_2_0_yellow19(X2,X3))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X1,X2,X3)
    | X4 != X1
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( ~ r2_hidden(esk4_0,k1_yellow19(esk2_0,esk3_0))
    | ~ m1_connsp_2(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,negated_conjecture,
    ( k1_yellow19(esk2_0,esk3_0) = a_2_0_yellow19(esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9]),c_0_10])]),c_0_11])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,a_2_0_yellow19(X2,X3))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk4_0,k1_yellow19(esk2_0,esk3_0))
    | m1_connsp_2(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,negated_conjecture,
    ( ~ m1_connsp_2(esk4_0,esk2_0,esk3_0)
    | ~ r2_hidden(esk4_0,a_2_0_yellow19(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(X1,a_2_0_yellow19(esk2_0,esk3_0))
    | ~ m1_connsp_2(X1,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_8]),c_0_9]),c_0_10])]),c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( m1_connsp_2(esk4_0,esk2_0,esk3_0)
    | r2_hidden(esk4_0,a_2_0_yellow19(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_16,c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( ~ m1_connsp_2(esk4_0,esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_21,plain,
    ( X1 = esk1_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_0_yellow19(X2,X3))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk4_0,a_2_0_yellow19(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_23,plain,
    ( m1_connsp_2(esk1_3(X1,X2,X3),X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_0_yellow19(X2,X3))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_24,negated_conjecture,
    ( esk1_3(esk4_0,esk2_0,esk3_0) = esk4_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_8]),c_0_9]),c_0_10])]),c_0_11])).

cnf(c_0_25,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_22]),c_0_24]),c_0_8]),c_0_9]),c_0_10])]),c_0_20]),c_0_11]),
    [proof]).

%------------------------------------------------------------------------------
