%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:01:08 EST 2020

% Result     : Theorem 0.92s
% Output     : CNFRefutation 0.92s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 522 expanded)
%              Number of clauses        :   38 ( 183 expanded)
%              Number of leaves         :    5 ( 124 expanded)
%              Depth                    :   13
%              Number of atoms          :  201 (3337 expanded)
%              Number of equality atoms :   20 ( 440 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t5_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( k1_relat_1(X3) = X1
          & ! [X4] :
              ( r2_hidden(X4,X1)
             => r2_hidden(k1_funct_1(X3,X4),X2) ) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).

fof(d13_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( X3 = k10_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ( r2_hidden(X4,k1_relat_1(X1))
                & r2_hidden(k1_funct_1(X1,X4),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).

fof(t4_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(k2_relat_1(X2),X1)
       => ( v1_funct_1(X2)
          & v1_funct_2(X2,k1_relat_1(X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(t145_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( ( k1_relat_1(X3) = X1
            & ! [X4] :
                ( r2_hidden(X4,X1)
               => r2_hidden(k1_funct_1(X3,X4),X2) ) )
         => ( v1_funct_1(X3)
            & v1_funct_2(X3,X1,X2)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t5_funct_2])).

fof(c_0_6,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X9,k1_relat_1(X6))
        | ~ r2_hidden(X9,X8)
        | X8 != k10_relat_1(X6,X7)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( r2_hidden(k1_funct_1(X6,X9),X7)
        | ~ r2_hidden(X9,X8)
        | X8 != k10_relat_1(X6,X7)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( ~ r2_hidden(X10,k1_relat_1(X6))
        | ~ r2_hidden(k1_funct_1(X6,X10),X7)
        | r2_hidden(X10,X8)
        | X8 != k10_relat_1(X6,X7)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( ~ r2_hidden(esk1_3(X6,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X6,X11,X12),k1_relat_1(X6))
        | ~ r2_hidden(k1_funct_1(X6,esk1_3(X6,X11,X12)),X11)
        | X12 = k10_relat_1(X6,X11)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( r2_hidden(esk1_3(X6,X11,X12),k1_relat_1(X6))
        | r2_hidden(esk1_3(X6,X11,X12),X12)
        | X12 = k10_relat_1(X6,X11)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( r2_hidden(k1_funct_1(X6,esk1_3(X6,X11,X12)),X11)
        | r2_hidden(esk1_3(X6,X11,X12),X12)
        | X12 = k10_relat_1(X6,X11)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_funct_1])])])])])])).

fof(c_0_7,negated_conjecture,(
    ! [X21] :
      ( v1_relat_1(esk4_0)
      & v1_funct_1(esk4_0)
      & k1_relat_1(esk4_0) = esk2_0
      & ( ~ r2_hidden(X21,esk2_0)
        | r2_hidden(k1_funct_1(esk4_0,X21),esk3_0) )
      & ( ~ v1_funct_1(esk4_0)
        | ~ v1_funct_2(esk4_0,esk2_0,esk3_0)
        | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).

fof(c_0_8,plain,(
    ! [X16,X17] :
      ( ( v1_funct_1(X17)
        | ~ r1_tarski(k2_relat_1(X17),X16)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( v1_funct_2(X17,k1_relat_1(X17),X16)
        | ~ r1_tarski(k2_relat_1(X17),X16)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X17),X16)))
        | ~ r1_tarski(k2_relat_1(X17),X16)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).

fof(c_0_9,plain,(
    ! [X14,X15] :
      ( ~ v1_relat_1(X15)
      | ~ v1_funct_1(X15)
      | r1_tarski(k9_relat_1(X15,k10_relat_1(X15,X14)),X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).

fof(c_0_10,plain,(
    ! [X5] :
      ( ~ v1_relat_1(X5)
      | k9_relat_1(X5,k1_relat_1(X5)) = k2_relat_1(X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k1_funct_1(X2,X1),X3)
    | X4 != k10_relat_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( ~ v1_funct_1(esk4_0)
    | ~ v1_funct_2(esk4_0,esk2_0,esk3_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),k1_relat_1(X1))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_20,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ r2_hidden(k1_funct_1(X2,X1),X3)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk4_0,X1),esk3_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_23,negated_conjecture,
    ( ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    | ~ v1_funct_2(esk4_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_12,c_0_13])])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,X1)))
    | ~ r1_tarski(k2_relat_1(esk4_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_13]),c_0_16])])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_2(esk4_0,esk2_0,X1)
    | ~ r1_tarski(k2_relat_1(esk4_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_15]),c_0_13]),c_0_16])])).

cnf(c_0_26,plain,
    ( r1_tarski(k9_relat_1(X1,X2),X3)
    | r2_hidden(esk1_3(X1,X3,X2),k1_relat_1(X1))
    | r2_hidden(esk1_3(X1,X3,X2),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( k9_relat_1(esk4_0,esk2_0) = k2_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_15]),c_0_16])])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,X3)
    | X3 != k10_relat_1(X2,X4)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(X1,k10_relat_1(esk4_0,esk3_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_15]),c_0_13]),c_0_16])])).

cnf(c_0_30,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(esk4_0),esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk4_0),X1)
    | r2_hidden(esk1_3(esk4_0,X1,esk2_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_15]),c_0_13]),c_0_16])])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk1_3(esk4_0,esk3_0,X1),esk2_0)
    | r2_hidden(esk1_3(esk4_0,esk3_0,X1),X1)
    | r2_hidden(X2,X1)
    | ~ r2_hidden(X2,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_19]),c_0_15]),c_0_13]),c_0_16])])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk1_3(esk4_0,esk3_0,esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,plain,
    ( X3 = k10_relat_1(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(k1_funct_1(X1,esk1_3(X1,X2,X3)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X1,k10_relat_1(esk4_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_15]),c_0_13]),c_0_16])])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk1_3(esk4_0,esk3_0,esk2_0),X1)
    | r2_hidden(esk1_3(esk4_0,esk3_0,X1),esk2_0)
    | r2_hidden(esk1_3(esk4_0,esk3_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(esk1_3(esk4_0,esk3_0,X2),esk2_0)
    | ~ r2_hidden(esk1_3(esk4_0,esk3_0,X2),X2)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_35]),c_0_15]),c_0_13]),c_0_16])]),c_0_22])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk1_3(esk4_0,esk3_0,esk2_0),k10_relat_1(esk4_0,X1))
    | r2_hidden(esk1_3(esk4_0,esk3_0,k10_relat_1(esk4_0,X1)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk1_3(esk4_0,esk3_0,esk2_0),k10_relat_1(esk4_0,X1))
    | r2_hidden(X2,k10_relat_1(esk4_0,X1))
    | ~ r2_hidden(esk1_3(esk4_0,esk3_0,k10_relat_1(esk4_0,X1)),k10_relat_1(esk4_0,X1))
    | ~ r2_hidden(X2,esk2_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_41,plain,
    ( r2_hidden(k1_funct_1(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | X4 != k10_relat_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk1_3(esk4_0,esk3_0,esk2_0),k10_relat_1(esk4_0,X1))
    | ~ r2_hidden(esk1_3(esk4_0,esk3_0,k10_relat_1(esk4_0,X1)),k10_relat_1(esk4_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(ef,[status(thm)],[c_0_40]),c_0_34])])).

cnf(c_0_43,plain,
    ( r1_tarski(k9_relat_1(X1,X2),X3)
    | ~ r2_hidden(k1_funct_1(X1,esk1_3(X1,X3,X2)),X3)
    | ~ r2_hidden(esk1_3(X1,X3,X2),k1_relat_1(X1))
    | ~ r2_hidden(esk1_3(X1,X3,X2),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_35])).

cnf(c_0_44,plain,
    ( r2_hidden(k1_funct_1(X1,X2),X3)
    | ~ r2_hidden(X2,k10_relat_1(X1,X3))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk1_3(esk4_0,esk3_0,esk2_0),k10_relat_1(esk4_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_29]),c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk4_0),X1)
    | ~ r2_hidden(k1_funct_1(esk4_0,esk1_3(esk4_0,X1,esk2_0)),X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_27]),c_0_15]),c_0_13]),c_0_16])]),c_0_31])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk4_0,esk1_3(esk4_0,esk3_0,esk2_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_13]),c_0_16])])).

cnf(c_0_48,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_46]),c_0_47])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:02:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.35  # No SInE strategy applied
% 0.12/0.35  # Trying AutoSched0 for 299 seconds
% 0.92/1.12  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S039A
% 0.92/1.12  # and selection function PSelectUnlessUniqMaxPos.
% 0.92/1.12  #
% 0.92/1.12  # Preprocessing time       : 0.027 s
% 0.92/1.12  # Presaturation interreduction done
% 0.92/1.12  
% 0.92/1.12  # Proof found!
% 0.92/1.12  # SZS status Theorem
% 0.92/1.12  # SZS output start CNFRefutation
% 0.92/1.12  fof(t5_funct_2, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X3)=X1&![X4]:(r2_hidden(X4,X1)=>r2_hidden(k1_funct_1(X3,X4),X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_funct_2)).
% 0.92/1.12  fof(d13_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(X3=k10_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,k1_relat_1(X1))&r2_hidden(k1_funct_1(X1,X4),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_funct_1)).
% 0.92/1.12  fof(t4_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(k2_relat_1(X2),X1)=>((v1_funct_1(X2)&v1_funct_2(X2,k1_relat_1(X2),X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 0.92/1.12  fof(t145_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 0.92/1.12  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 0.92/1.12  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X3)=X1&![X4]:(r2_hidden(X4,X1)=>r2_hidden(k1_funct_1(X3,X4),X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))))), inference(assume_negation,[status(cth)],[t5_funct_2])).
% 0.92/1.12  fof(c_0_6, plain, ![X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X9,k1_relat_1(X6))|~r2_hidden(X9,X8)|X8!=k10_relat_1(X6,X7)|(~v1_relat_1(X6)|~v1_funct_1(X6)))&(r2_hidden(k1_funct_1(X6,X9),X7)|~r2_hidden(X9,X8)|X8!=k10_relat_1(X6,X7)|(~v1_relat_1(X6)|~v1_funct_1(X6))))&(~r2_hidden(X10,k1_relat_1(X6))|~r2_hidden(k1_funct_1(X6,X10),X7)|r2_hidden(X10,X8)|X8!=k10_relat_1(X6,X7)|(~v1_relat_1(X6)|~v1_funct_1(X6))))&((~r2_hidden(esk1_3(X6,X11,X12),X12)|(~r2_hidden(esk1_3(X6,X11,X12),k1_relat_1(X6))|~r2_hidden(k1_funct_1(X6,esk1_3(X6,X11,X12)),X11))|X12=k10_relat_1(X6,X11)|(~v1_relat_1(X6)|~v1_funct_1(X6)))&((r2_hidden(esk1_3(X6,X11,X12),k1_relat_1(X6))|r2_hidden(esk1_3(X6,X11,X12),X12)|X12=k10_relat_1(X6,X11)|(~v1_relat_1(X6)|~v1_funct_1(X6)))&(r2_hidden(k1_funct_1(X6,esk1_3(X6,X11,X12)),X11)|r2_hidden(esk1_3(X6,X11,X12),X12)|X12=k10_relat_1(X6,X11)|(~v1_relat_1(X6)|~v1_funct_1(X6)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_funct_1])])])])])])).
% 0.92/1.12  fof(c_0_7, negated_conjecture, ![X21]:((v1_relat_1(esk4_0)&v1_funct_1(esk4_0))&((k1_relat_1(esk4_0)=esk2_0&(~r2_hidden(X21,esk2_0)|r2_hidden(k1_funct_1(esk4_0,X21),esk3_0)))&(~v1_funct_1(esk4_0)|~v1_funct_2(esk4_0,esk2_0,esk3_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).
% 0.92/1.12  fof(c_0_8, plain, ![X16, X17]:(((v1_funct_1(X17)|~r1_tarski(k2_relat_1(X17),X16)|(~v1_relat_1(X17)|~v1_funct_1(X17)))&(v1_funct_2(X17,k1_relat_1(X17),X16)|~r1_tarski(k2_relat_1(X17),X16)|(~v1_relat_1(X17)|~v1_funct_1(X17))))&(m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X17),X16)))|~r1_tarski(k2_relat_1(X17),X16)|(~v1_relat_1(X17)|~v1_funct_1(X17)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).
% 0.92/1.12  fof(c_0_9, plain, ![X14, X15]:(~v1_relat_1(X15)|~v1_funct_1(X15)|r1_tarski(k9_relat_1(X15,k10_relat_1(X15,X14)),X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).
% 0.92/1.12  fof(c_0_10, plain, ![X5]:(~v1_relat_1(X5)|k9_relat_1(X5,k1_relat_1(X5))=k2_relat_1(X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.92/1.12  cnf(c_0_11, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k1_funct_1(X2,X1),X3)|X4!=k10_relat_1(X2,X3)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.92/1.12  cnf(c_0_12, negated_conjecture, (~v1_funct_1(esk4_0)|~v1_funct_2(esk4_0,esk2_0,esk3_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.92/1.12  cnf(c_0_13, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.92/1.12  cnf(c_0_14, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.92/1.12  cnf(c_0_15, negated_conjecture, (k1_relat_1(esk4_0)=esk2_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.92/1.12  cnf(c_0_16, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.92/1.12  cnf(c_0_17, plain, (v1_funct_2(X1,k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.92/1.12  cnf(c_0_18, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.92/1.12  cnf(c_0_19, plain, (r2_hidden(esk1_3(X1,X2,X3),k1_relat_1(X1))|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k10_relat_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.92/1.12  cnf(c_0_20, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.92/1.12  cnf(c_0_21, plain, (r2_hidden(X1,k10_relat_1(X2,X3))|~r2_hidden(k1_funct_1(X2,X1),X3)|~r2_hidden(X1,k1_relat_1(X2))|~v1_funct_1(X2)|~v1_relat_1(X2)), inference(er,[status(thm)],[c_0_11])).
% 0.92/1.12  cnf(c_0_22, negated_conjecture, (r2_hidden(k1_funct_1(esk4_0,X1),esk3_0)|~r2_hidden(X1,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.92/1.12  cnf(c_0_23, negated_conjecture, (~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))|~v1_funct_2(esk4_0,esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_12, c_0_13])])).
% 0.92/1.12  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,X1)))|~r1_tarski(k2_relat_1(esk4_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_13]), c_0_16])])).
% 0.92/1.12  cnf(c_0_25, negated_conjecture, (v1_funct_2(esk4_0,esk2_0,X1)|~r1_tarski(k2_relat_1(esk4_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_15]), c_0_13]), c_0_16])])).
% 0.92/1.12  cnf(c_0_26, plain, (r1_tarski(k9_relat_1(X1,X2),X3)|r2_hidden(esk1_3(X1,X3,X2),k1_relat_1(X1))|r2_hidden(esk1_3(X1,X3,X2),X2)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.92/1.12  cnf(c_0_27, negated_conjecture, (k9_relat_1(esk4_0,esk2_0)=k2_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_15]), c_0_16])])).
% 0.92/1.12  cnf(c_0_28, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(X1,X3)|X3!=k10_relat_1(X2,X4)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.92/1.12  cnf(c_0_29, negated_conjecture, (r2_hidden(X1,k10_relat_1(esk4_0,esk3_0))|~r2_hidden(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_15]), c_0_13]), c_0_16])])).
% 0.92/1.12  cnf(c_0_30, negated_conjecture, (~r1_tarski(k2_relat_1(esk4_0),esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])).
% 0.92/1.12  cnf(c_0_31, negated_conjecture, (r1_tarski(k2_relat_1(esk4_0),X1)|r2_hidden(esk1_3(esk4_0,X1,esk2_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_15]), c_0_13]), c_0_16])])).
% 0.92/1.12  cnf(c_0_32, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(X1,k10_relat_1(X2,X3))|~v1_funct_1(X2)|~v1_relat_1(X2)), inference(er,[status(thm)],[c_0_28])).
% 0.92/1.12  cnf(c_0_33, negated_conjecture, (r2_hidden(esk1_3(esk4_0,esk3_0,X1),esk2_0)|r2_hidden(esk1_3(esk4_0,esk3_0,X1),X1)|r2_hidden(X2,X1)|~r2_hidden(X2,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_19]), c_0_15]), c_0_13]), c_0_16])])).
% 0.92/1.12  cnf(c_0_34, negated_conjecture, (r2_hidden(esk1_3(esk4_0,esk3_0,esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.92/1.12  cnf(c_0_35, plain, (X3=k10_relat_1(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),k1_relat_1(X1))|~r2_hidden(k1_funct_1(X1,esk1_3(X1,X2,X3)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.92/1.12  cnf(c_0_36, negated_conjecture, (r2_hidden(X1,esk2_0)|~r2_hidden(X1,k10_relat_1(esk4_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_15]), c_0_13]), c_0_16])])).
% 0.92/1.12  cnf(c_0_37, negated_conjecture, (r2_hidden(esk1_3(esk4_0,esk3_0,esk2_0),X1)|r2_hidden(esk1_3(esk4_0,esk3_0,X1),esk2_0)|r2_hidden(esk1_3(esk4_0,esk3_0,X1),X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.92/1.12  cnf(c_0_38, negated_conjecture, (r2_hidden(X1,X2)|~r2_hidden(esk1_3(esk4_0,esk3_0,X2),esk2_0)|~r2_hidden(esk1_3(esk4_0,esk3_0,X2),X2)|~r2_hidden(X1,esk2_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_35]), c_0_15]), c_0_13]), c_0_16])]), c_0_22])).
% 0.92/1.12  cnf(c_0_39, negated_conjecture, (r2_hidden(esk1_3(esk4_0,esk3_0,esk2_0),k10_relat_1(esk4_0,X1))|r2_hidden(esk1_3(esk4_0,esk3_0,k10_relat_1(esk4_0,X1)),esk2_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.92/1.12  cnf(c_0_40, negated_conjecture, (r2_hidden(esk1_3(esk4_0,esk3_0,esk2_0),k10_relat_1(esk4_0,X1))|r2_hidden(X2,k10_relat_1(esk4_0,X1))|~r2_hidden(esk1_3(esk4_0,esk3_0,k10_relat_1(esk4_0,X1)),k10_relat_1(esk4_0,X1))|~r2_hidden(X2,esk2_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.92/1.12  cnf(c_0_41, plain, (r2_hidden(k1_funct_1(X1,X2),X3)|~r2_hidden(X2,X4)|X4!=k10_relat_1(X1,X3)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.92/1.12  cnf(c_0_42, negated_conjecture, (r2_hidden(esk1_3(esk4_0,esk3_0,esk2_0),k10_relat_1(esk4_0,X1))|~r2_hidden(esk1_3(esk4_0,esk3_0,k10_relat_1(esk4_0,X1)),k10_relat_1(esk4_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(ef,[status(thm)],[c_0_40]), c_0_34])])).
% 0.92/1.12  cnf(c_0_43, plain, (r1_tarski(k9_relat_1(X1,X2),X3)|~r2_hidden(k1_funct_1(X1,esk1_3(X1,X3,X2)),X3)|~r2_hidden(esk1_3(X1,X3,X2),k1_relat_1(X1))|~r2_hidden(esk1_3(X1,X3,X2),X2)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_18, c_0_35])).
% 0.92/1.12  cnf(c_0_44, plain, (r2_hidden(k1_funct_1(X1,X2),X3)|~r2_hidden(X2,k10_relat_1(X1,X3))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_41])).
% 0.92/1.12  cnf(c_0_45, negated_conjecture, (r2_hidden(esk1_3(esk4_0,esk3_0,esk2_0),k10_relat_1(esk4_0,esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_29]), c_0_39])).
% 0.92/1.12  cnf(c_0_46, negated_conjecture, (r1_tarski(k2_relat_1(esk4_0),X1)|~r2_hidden(k1_funct_1(esk4_0,esk1_3(esk4_0,X1,esk2_0)),X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_27]), c_0_15]), c_0_13]), c_0_16])]), c_0_31])).
% 0.92/1.12  cnf(c_0_47, negated_conjecture, (r2_hidden(k1_funct_1(esk4_0,esk1_3(esk4_0,esk3_0,esk2_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_13]), c_0_16])])).
% 0.92/1.12  cnf(c_0_48, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_46]), c_0_47])]), ['proof']).
% 0.92/1.12  # SZS output end CNFRefutation
% 0.92/1.12  # Proof object total steps             : 49
% 0.92/1.12  # Proof object clause steps            : 38
% 0.92/1.12  # Proof object formula steps           : 11
% 0.92/1.12  # Proof object conjectures             : 27
% 0.92/1.12  # Proof object clause conjectures      : 24
% 0.92/1.12  # Proof object formula conjectures     : 3
% 0.92/1.12  # Proof object initial clauses used    : 14
% 0.92/1.12  # Proof object initial formulas used   : 5
% 0.92/1.12  # Proof object generating inferences   : 20
% 0.92/1.12  # Proof object simplifying inferences  : 47
% 0.92/1.12  # Training examples: 0 positive, 0 negative
% 0.92/1.12  # Parsed axioms                        : 5
% 0.92/1.12  # Removed by relevancy pruning/SinE    : 0
% 0.92/1.12  # Initial clauses                      : 16
% 0.92/1.12  # Removed in clause preprocessing      : 1
% 0.92/1.12  # Initial clauses in saturation        : 15
% 0.92/1.12  # Processed clauses                    : 799
% 0.92/1.12  # ...of these trivial                  : 0
% 0.92/1.12  # ...subsumed                          : 399
% 0.92/1.12  # ...remaining for further processing  : 400
% 0.92/1.12  # Other redundant clauses eliminated   : 3
% 0.92/1.12  # Clauses deleted for lack of memory   : 0
% 0.92/1.12  # Backward-subsumed                    : 7
% 0.92/1.12  # Backward-rewritten                   : 0
% 0.92/1.12  # Generated clauses                    : 35752
% 0.92/1.12  # ...of the previous two non-trivial   : 34718
% 0.92/1.12  # Contextual simplify-reflections      : 56
% 0.92/1.12  # Paramodulations                      : 35629
% 0.92/1.12  # Factorizations                       : 120
% 0.92/1.12  # Equation resolutions                 : 3
% 0.92/1.12  # Propositional unsat checks           : 0
% 0.92/1.12  #    Propositional check models        : 0
% 0.92/1.12  #    Propositional check unsatisfiable : 0
% 0.92/1.12  #    Propositional clauses             : 0
% 0.92/1.12  #    Propositional clauses after purity: 0
% 0.92/1.12  #    Propositional unsat core size     : 0
% 0.92/1.12  #    Propositional preprocessing time  : 0.000
% 0.92/1.12  #    Propositional encoding time       : 0.000
% 0.92/1.12  #    Propositional solver time         : 0.000
% 0.92/1.12  #    Success case prop preproc time    : 0.000
% 0.92/1.12  #    Success case prop encoding time   : 0.000
% 0.92/1.12  #    Success case prop solver time     : 0.000
% 0.92/1.12  # Current number of processed clauses  : 375
% 0.92/1.12  #    Positive orientable unit clauses  : 7
% 0.92/1.12  #    Positive unorientable unit clauses: 0
% 0.92/1.12  #    Negative unit clauses             : 1
% 0.92/1.12  #    Non-unit-clauses                  : 367
% 0.92/1.12  # Current number of unprocessed clauses: 33937
% 0.92/1.12  # ...number of literals in the above   : 323318
% 0.92/1.12  # Current number of archived formulas  : 0
% 0.92/1.12  # Current number of archived clauses   : 22
% 0.92/1.12  # Clause-clause subsumption calls (NU) : 29723
% 0.92/1.12  # Rec. Clause-clause subsumption calls : 7483
% 0.92/1.12  # Non-unit clause-clause subsumptions  : 456
% 0.92/1.12  # Unit Clause-clause subsumption calls : 19
% 0.92/1.12  # Rewrite failures with RHS unbound    : 0
% 0.92/1.12  # BW rewrite match attempts            : 5
% 0.92/1.12  # BW rewrite match successes           : 0
% 0.92/1.12  # Condensation attempts                : 0
% 0.92/1.12  # Condensation successes               : 0
% 0.92/1.12  # Termbank termtop insertions          : 1289106
% 0.92/1.12  
% 0.92/1.12  # -------------------------------------------------
% 0.92/1.12  # User time                : 0.754 s
% 0.92/1.12  # System time              : 0.023 s
% 0.92/1.12  # Total time               : 0.778 s
% 0.92/1.12  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
