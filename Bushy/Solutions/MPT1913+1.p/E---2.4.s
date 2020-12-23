%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow_6__t9_yellow_6.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:56 EDT 2019

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   37 ( 138 expanded)
%              Number of clauses        :   26 (  46 expanded)
%              Number of leaves         :    5 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :  257 (1114 expanded)
%              Number of equality atoms :   31 ( 106 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal clause size      :   60 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t9_yellow_6,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v4_relat_1(X2,X1)
            & v1_funct_1(X2)
            & v1_partfun1(X2,X1)
            & v2_pralg_1(X2) )
         => ! [X3] :
              ( m1_subset_1(X3,X1)
             => k1_funct_1(k12_pralg_1(X1,X2),X3) = u1_struct_0(k10_pralg_1(X1,X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t9_yellow_6.p',t9_yellow_6)).

fof(d13_pralg_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1)
        & v1_funct_1(X2)
        & v1_partfun1(X2,X1)
        & v2_pralg_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v4_relat_1(X3,X1)
            & v1_funct_1(X3)
            & v1_partfun1(X3,X1) )
         => ( X3 = k12_pralg_1(X1,X2)
          <=> ! [X4] :
                ~ ( r2_hidden(X4,X1)
                  & ! [X5] :
                      ( l1_struct_0(X5)
                     => ~ ( X5 = k1_funct_1(X2,X4)
                          & k1_funct_1(X3,X4) = u1_struct_0(X5) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t9_yellow_6.p',d13_pralg_1)).

fof(dt_k12_pralg_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1)
        & v1_funct_1(X2)
        & v1_partfun1(X2,X1)
        & v2_pralg_1(X2) )
     => ( v1_relat_1(k12_pralg_1(X1,X2))
        & v4_relat_1(k12_pralg_1(X1,X2),X1)
        & v1_funct_1(k12_pralg_1(X1,X2))
        & v1_partfun1(k12_pralg_1(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t9_yellow_6.p',dt_k12_pralg_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t9_yellow_6.p',t2_subset)).

fof(redefinition_k10_pralg_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v1_xboole_0(X1)
        & v1_relat_1(X2)
        & v4_relat_1(X2,X1)
        & v1_funct_1(X2)
        & v1_partfun1(X2,X1)
        & v2_pralg_1(X2)
        & m1_subset_1(X3,X1) )
     => k10_pralg_1(X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t9_yellow_6.p',redefinition_k10_pralg_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ( v1_relat_1(X2)
              & v4_relat_1(X2,X1)
              & v1_funct_1(X2)
              & v1_partfun1(X2,X1)
              & v2_pralg_1(X2) )
           => ! [X3] :
                ( m1_subset_1(X3,X1)
               => k1_funct_1(k12_pralg_1(X1,X2),X3) = u1_struct_0(k10_pralg_1(X1,X2,X3)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t9_yellow_6])).

fof(c_0_6,plain,(
    ! [X11,X12,X13,X14,X17] :
      ( ( l1_struct_0(esk4_4(X11,X12,X13,X14))
        | ~ r2_hidden(X14,X11)
        | X13 != k12_pralg_1(X11,X12)
        | ~ v1_relat_1(X13)
        | ~ v4_relat_1(X13,X11)
        | ~ v1_funct_1(X13)
        | ~ v1_partfun1(X13,X11)
        | ~ v1_relat_1(X12)
        | ~ v4_relat_1(X12,X11)
        | ~ v1_funct_1(X12)
        | ~ v1_partfun1(X12,X11)
        | ~ v2_pralg_1(X12) )
      & ( esk4_4(X11,X12,X13,X14) = k1_funct_1(X12,X14)
        | ~ r2_hidden(X14,X11)
        | X13 != k12_pralg_1(X11,X12)
        | ~ v1_relat_1(X13)
        | ~ v4_relat_1(X13,X11)
        | ~ v1_funct_1(X13)
        | ~ v1_partfun1(X13,X11)
        | ~ v1_relat_1(X12)
        | ~ v4_relat_1(X12,X11)
        | ~ v1_funct_1(X12)
        | ~ v1_partfun1(X12,X11)
        | ~ v2_pralg_1(X12) )
      & ( k1_funct_1(X13,X14) = u1_struct_0(esk4_4(X11,X12,X13,X14))
        | ~ r2_hidden(X14,X11)
        | X13 != k12_pralg_1(X11,X12)
        | ~ v1_relat_1(X13)
        | ~ v4_relat_1(X13,X11)
        | ~ v1_funct_1(X13)
        | ~ v1_partfun1(X13,X11)
        | ~ v1_relat_1(X12)
        | ~ v4_relat_1(X12,X11)
        | ~ v1_funct_1(X12)
        | ~ v1_partfun1(X12,X11)
        | ~ v2_pralg_1(X12) )
      & ( r2_hidden(esk5_3(X11,X12,X13),X11)
        | X13 = k12_pralg_1(X11,X12)
        | ~ v1_relat_1(X13)
        | ~ v4_relat_1(X13,X11)
        | ~ v1_funct_1(X13)
        | ~ v1_partfun1(X13,X11)
        | ~ v1_relat_1(X12)
        | ~ v4_relat_1(X12,X11)
        | ~ v1_funct_1(X12)
        | ~ v1_partfun1(X12,X11)
        | ~ v2_pralg_1(X12) )
      & ( ~ l1_struct_0(X17)
        | X17 != k1_funct_1(X12,esk5_3(X11,X12,X13))
        | k1_funct_1(X13,esk5_3(X11,X12,X13)) != u1_struct_0(X17)
        | X13 = k12_pralg_1(X11,X12)
        | ~ v1_relat_1(X13)
        | ~ v4_relat_1(X13,X11)
        | ~ v1_funct_1(X13)
        | ~ v1_partfun1(X13,X11)
        | ~ v1_relat_1(X12)
        | ~ v4_relat_1(X12,X11)
        | ~ v1_funct_1(X12)
        | ~ v1_partfun1(X12,X11)
        | ~ v2_pralg_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_pralg_1])])])])])).

fof(c_0_7,plain,(
    ! [X21,X22] :
      ( ( v1_relat_1(k12_pralg_1(X21,X22))
        | ~ v1_relat_1(X22)
        | ~ v4_relat_1(X22,X21)
        | ~ v1_funct_1(X22)
        | ~ v1_partfun1(X22,X21)
        | ~ v2_pralg_1(X22) )
      & ( v4_relat_1(k12_pralg_1(X21,X22),X21)
        | ~ v1_relat_1(X22)
        | ~ v4_relat_1(X22,X21)
        | ~ v1_funct_1(X22)
        | ~ v1_partfun1(X22,X21)
        | ~ v2_pralg_1(X22) )
      & ( v1_funct_1(k12_pralg_1(X21,X22))
        | ~ v1_relat_1(X22)
        | ~ v4_relat_1(X22,X21)
        | ~ v1_funct_1(X22)
        | ~ v1_partfun1(X22,X21)
        | ~ v2_pralg_1(X22) )
      & ( v1_partfun1(k12_pralg_1(X21,X22),X21)
        | ~ v1_relat_1(X22)
        | ~ v4_relat_1(X22,X21)
        | ~ v1_funct_1(X22)
        | ~ v1_partfun1(X22,X21)
        | ~ v2_pralg_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k12_pralg_1])])])).

fof(c_0_8,plain,(
    ! [X31,X32] :
      ( ~ m1_subset_1(X31,X32)
      | v1_xboole_0(X32)
      | r2_hidden(X31,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_9,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    & v1_relat_1(esk2_0)
    & v4_relat_1(esk2_0,esk1_0)
    & v1_funct_1(esk2_0)
    & v1_partfun1(esk2_0,esk1_0)
    & v2_pralg_1(esk2_0)
    & m1_subset_1(esk3_0,esk1_0)
    & k1_funct_1(k12_pralg_1(esk1_0,esk2_0),esk3_0) != u1_struct_0(k10_pralg_1(esk1_0,esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).

fof(c_0_10,plain,(
    ! [X26,X27,X28] :
      ( v1_xboole_0(X26)
      | ~ v1_relat_1(X27)
      | ~ v4_relat_1(X27,X26)
      | ~ v1_funct_1(X27)
      | ~ v1_partfun1(X27,X26)
      | ~ v2_pralg_1(X27)
      | ~ m1_subset_1(X28,X26)
      | k10_pralg_1(X26,X27,X28) = k1_funct_1(X27,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k10_pralg_1])])])).

cnf(c_0_11,plain,
    ( esk4_4(X1,X2,X3,X4) = k1_funct_1(X2,X4)
    | ~ r2_hidden(X4,X1)
    | X3 != k12_pralg_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v4_relat_1(X3,X1)
    | ~ v1_funct_1(X3)
    | ~ v1_partfun1(X3,X1)
    | ~ v1_relat_1(X2)
    | ~ v4_relat_1(X2,X1)
    | ~ v1_funct_1(X2)
    | ~ v1_partfun1(X2,X1)
    | ~ v2_pralg_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( v1_relat_1(k12_pralg_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v4_relat_1(X2,X1)
    | ~ v1_funct_1(X2)
    | ~ v1_partfun1(X2,X1)
    | ~ v2_pralg_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( v4_relat_1(k12_pralg_1(X1,X2),X1)
    | ~ v1_relat_1(X2)
    | ~ v4_relat_1(X2,X1)
    | ~ v1_funct_1(X2)
    | ~ v1_partfun1(X2,X1)
    | ~ v2_pralg_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( v1_funct_1(k12_pralg_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v4_relat_1(X2,X1)
    | ~ v1_funct_1(X2)
    | ~ v1_partfun1(X2,X1)
    | ~ v2_pralg_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,plain,
    ( v1_partfun1(k12_pralg_1(X1,X2),X1)
    | ~ v1_relat_1(X2)
    | ~ v4_relat_1(X2,X1)
    | ~ v1_funct_1(X2)
    | ~ v1_partfun1(X2,X1)
    | ~ v2_pralg_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,plain,
    ( v1_xboole_0(X1)
    | k10_pralg_1(X1,X2,X3) = k1_funct_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v4_relat_1(X2,X1)
    | ~ v1_funct_1(X2)
    | ~ v1_partfun1(X2,X1)
    | ~ v2_pralg_1(X2)
    | ~ m1_subset_1(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,plain,
    ( k1_funct_1(X1,X2) = u1_struct_0(esk4_4(X3,X4,X1,X2))
    | ~ r2_hidden(X2,X3)
    | X1 != k12_pralg_1(X3,X4)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X3)
    | ~ v1_relat_1(X4)
    | ~ v4_relat_1(X4,X3)
    | ~ v1_funct_1(X4)
    | ~ v1_partfun1(X4,X3)
    | ~ v2_pralg_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_21,plain,
    ( esk4_4(X1,X2,k12_pralg_1(X1,X2),X3) = k1_funct_1(X2,X3)
    | ~ r2_hidden(X3,X1)
    | ~ v2_pralg_1(X2)
    | ~ v1_partfun1(X2,X1)
    | ~ v1_funct_1(X2)
    | ~ v4_relat_1(X2,X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk3_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( k10_pralg_1(esk1_0,X1,esk3_0) = k1_funct_1(X1,esk3_0)
    | ~ v2_pralg_1(X1)
    | ~ v1_partfun1(X1,esk1_0)
    | ~ v1_funct_1(X1)
    | ~ v4_relat_1(X1,esk1_0)
    | ~ v1_relat_1(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_17]),c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( v1_partfun1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_25,negated_conjecture,
    ( v2_pralg_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_27,negated_conjecture,
    ( v4_relat_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_29,plain,
    ( u1_struct_0(esk4_4(X1,X2,k12_pralg_1(X1,X2),X3)) = k1_funct_1(k12_pralg_1(X1,X2),X3)
    | ~ r2_hidden(X3,X1)
    | ~ v2_pralg_1(X2)
    | ~ v1_partfun1(X2,X1)
    | ~ v1_funct_1(X2)
    | ~ v4_relat_1(X2,X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_20]),c_0_12]),c_0_13]),c_0_14]),c_0_15])).

cnf(c_0_30,negated_conjecture,
    ( esk4_4(esk1_0,X1,k12_pralg_1(esk1_0,X1),esk3_0) = k1_funct_1(X1,esk3_0)
    | ~ v2_pralg_1(X1)
    | ~ v1_partfun1(X1,esk1_0)
    | ~ v1_funct_1(X1)
    | ~ v4_relat_1(X1,esk1_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( k1_funct_1(k12_pralg_1(esk1_0,esk2_0),esk3_0) != u1_struct_0(k10_pralg_1(esk1_0,esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_32,negated_conjecture,
    ( k10_pralg_1(esk1_0,esk2_0,esk3_0) = k1_funct_1(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28])])).

cnf(c_0_33,negated_conjecture,
    ( u1_struct_0(esk4_4(esk1_0,X1,k12_pralg_1(esk1_0,X1),esk3_0)) = k1_funct_1(k12_pralg_1(esk1_0,X1),esk3_0)
    | ~ v2_pralg_1(X1)
    | ~ v1_partfun1(X1,esk1_0)
    | ~ v1_funct_1(X1)
    | ~ v4_relat_1(X1,esk1_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_22])).

cnf(c_0_34,negated_conjecture,
    ( esk4_4(esk1_0,esk2_0,k12_pralg_1(esk1_0,esk2_0),esk3_0) = k1_funct_1(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28])])).

cnf(c_0_35,negated_conjecture,
    ( u1_struct_0(k1_funct_1(esk2_0,esk3_0)) != k1_funct_1(k12_pralg_1(esk1_0,esk2_0),esk3_0) ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_24]),c_0_34]),c_0_25]),c_0_26]),c_0_27]),c_0_28])]),c_0_35]),
    [proof]).
%------------------------------------------------------------------------------
