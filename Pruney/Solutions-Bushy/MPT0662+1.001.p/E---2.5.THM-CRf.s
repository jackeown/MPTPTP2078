%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0662+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:59 EST 2020

% Result     : Theorem 0.92s
% Output     : CNFRefutation 0.92s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 161 expanded)
%              Number of clauses        :   42 (  69 expanded)
%              Number of leaves         :   12 (  39 expanded)
%              Depth                    :   14
%              Number of atoms          :  214 ( 701 expanded)
%              Number of equality atoms :   41 ( 180 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t88_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k7_relat_1(X2,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(t70_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
       => k1_funct_1(k7_relat_1(X3,X2),X1) = k1_funct_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_funct_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(d4_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( ( r2_hidden(X2,k1_relat_1(X1))
           => ( X3 = k1_funct_1(X1,X2)
            <=> r2_hidden(k4_tarski(X2,X3),X1) ) )
          & ( ~ r2_hidden(X2,k1_relat_1(X1))
           => ( X3 = k1_funct_1(X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(fc8_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k7_relat_1(X1,X2))
        & v1_funct_1(k7_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(c_0_12,plain,(
    ! [X27,X28,X29] :
      ( ~ r2_hidden(X27,X28)
      | ~ m1_subset_1(X28,k1_zfmisc_1(X29))
      | m1_subset_1(X27,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_13,plain,(
    ! [X25,X26] :
      ( ( ~ m1_subset_1(X25,k1_zfmisc_1(X26))
        | r1_tarski(X25,X26) )
      & ( ~ r1_tarski(X25,X26)
        | m1_subset_1(X25,k1_zfmisc_1(X26)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_14,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_16,plain,(
    ! [X32,X33] :
      ( ~ v1_relat_1(X33)
      | r1_tarski(k7_relat_1(X33,X32),X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
         => k1_funct_1(k7_relat_1(X3,X2),X1) = k1_funct_1(X3,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t70_funct_1])).

fof(c_0_18,plain,(
    ! [X10,X11,X12,X13,X14,X15,X16,X17] :
      ( ( r2_hidden(X13,X10)
        | ~ r2_hidden(X13,X12)
        | X12 != k3_xboole_0(X10,X11) )
      & ( r2_hidden(X13,X11)
        | ~ r2_hidden(X13,X12)
        | X12 != k3_xboole_0(X10,X11) )
      & ( ~ r2_hidden(X14,X10)
        | ~ r2_hidden(X14,X11)
        | r2_hidden(X14,X12)
        | X12 != k3_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X15,X16,X17),X17)
        | ~ r2_hidden(esk1_3(X15,X16,X17),X15)
        | ~ r2_hidden(esk1_3(X15,X16,X17),X16)
        | X17 = k3_xboole_0(X15,X16) )
      & ( r2_hidden(esk1_3(X15,X16,X17),X15)
        | r2_hidden(esk1_3(X15,X16,X17),X17)
        | X17 = k3_xboole_0(X15,X16) )
      & ( r2_hidden(esk1_3(X15,X16,X17),X16)
        | r2_hidden(esk1_3(X15,X16,X17),X17)
        | X17 = k3_xboole_0(X15,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_19,plain,
    ( m1_subset_1(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,plain,
    ( r1_tarski(k7_relat_1(X1,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X7,X8,X9] :
      ( ( X9 != k1_funct_1(X7,X8)
        | r2_hidden(k4_tarski(X8,X9),X7)
        | ~ r2_hidden(X8,k1_relat_1(X7))
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) )
      & ( ~ r2_hidden(k4_tarski(X8,X9),X7)
        | X9 = k1_funct_1(X7,X8)
        | ~ r2_hidden(X8,k1_relat_1(X7))
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) )
      & ( X9 != k1_funct_1(X7,X8)
        | X9 = k1_xboole_0
        | r2_hidden(X8,k1_relat_1(X7))
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) )
      & ( X9 != k1_xboole_0
        | X9 = k1_funct_1(X7,X8)
        | r2_hidden(X8,k1_relat_1(X7))
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).

fof(c_0_22,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & v1_funct_1(esk4_0)
    & r2_hidden(esk2_0,k1_relat_1(k7_relat_1(esk4_0,esk3_0)))
    & k1_funct_1(k7_relat_1(esk4_0,esk3_0),esk2_0) != k1_funct_1(esk4_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

fof(c_0_23,plain,(
    ! [X34,X35] :
      ( ~ v1_relat_1(X35)
      | k1_relat_1(k7_relat_1(X35,X34)) = k3_xboole_0(k1_relat_1(X35),X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

fof(c_0_24,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_25,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,k7_relat_1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_27,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_28,plain,(
    ! [X30,X31] :
      ( ~ r2_hidden(X30,X31)
      | ~ v1_xboole_0(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_29,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | X1 != k1_funct_1(X2,X3)
    | ~ r2_hidden(X3,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk2_0,k1_relat_1(k7_relat_1(esk4_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_36,plain,
    ( k3_xboole_0(X1,X2) = X1
    | r2_hidden(esk1_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( k7_relat_1(X1,X2) = k3_xboole_0(X3,X4)
    | m1_subset_1(esk1_3(X3,X4,k7_relat_1(X1,X2)),X1)
    | r2_hidden(esk1_3(X3,X4,k7_relat_1(X1,X2)),X4)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_38,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk2_0,k3_xboole_0(esk3_0,k1_relat_1(esk4_0))) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])]),c_0_34])).

fof(c_0_42,plain,(
    ! [X23,X24] :
      ( ~ m1_subset_1(X23,X24)
      | v1_xboole_0(X24)
      | r2_hidden(X23,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r2_hidden(esk1_3(X1,X2,X1),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( k7_relat_1(esk4_0,X1) = k3_xboole_0(X2,X3)
    | m1_subset_1(esk1_3(X2,X3,k7_relat_1(esk4_0,X1)),esk4_0)
    | r2_hidden(esk1_3(X2,X3,k7_relat_1(esk4_0,X1)),X3) ),
    inference(spm,[status(thm)],[c_0_37,c_0_33])).

cnf(c_0_45,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk2_0,k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_49,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( k3_xboole_0(k7_relat_1(esk4_0,X1),X2) = k7_relat_1(esk4_0,X1)
    | m1_subset_1(esk1_3(k7_relat_1(esk4_0,X1),X2,k7_relat_1(esk4_0,X1)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47]),c_0_33])])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( k3_xboole_0(k7_relat_1(esk4_0,X1),X2) = k7_relat_1(esk4_0,X1)
    | r2_hidden(esk1_3(k7_relat_1(esk4_0,X1),X2,k7_relat_1(esk4_0,X1)),esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

cnf(c_0_54,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(k3_xboole_0(X2,X3),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(k3_xboole_0(X2,X3)))
    | ~ v1_funct_1(k3_xboole_0(X2,X3))
    | ~ v1_relat_1(k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_39])).

cnf(c_0_55,negated_conjecture,
    ( k3_xboole_0(esk4_0,k7_relat_1(esk4_0,X1)) = k7_relat_1(esk4_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_53]),c_0_34])).

cnf(c_0_56,plain,
    ( X2 = k1_funct_1(X3,X1)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,k1_relat_1(X3))
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(k7_relat_1(esk4_0,X2),X1)),esk4_0)
    | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(esk4_0,X2)))
    | ~ v1_funct_1(k7_relat_1(esk4_0,X2))
    | ~ v1_relat_1(k7_relat_1(esk4_0,X2)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk4_0,X1),X2) = k1_funct_1(esk4_0,X2)
    | ~ r2_hidden(X2,k1_relat_1(k7_relat_1(esk4_0,X1)))
    | ~ r2_hidden(X2,k1_relat_1(esk4_0))
    | ~ v1_funct_1(k7_relat_1(esk4_0,X1))
    | ~ v1_relat_1(k7_relat_1(esk4_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_47]),c_0_33])])).

cnf(c_0_59,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk4_0,esk3_0),esk2_0) != k1_funct_1(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_60,plain,(
    ! [X21,X22] :
      ( ( v1_relat_1(k7_relat_1(X21,X22))
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( v1_funct_1(k7_relat_1(X21,X22))
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).

cnf(c_0_61,negated_conjecture,
    ( ~ v1_funct_1(k7_relat_1(esk4_0,esk3_0))
    | ~ v1_relat_1(k7_relat_1(esk4_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_31]),c_0_46])]),c_0_59])).

cnf(c_0_62,plain,
    ( v1_funct_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

fof(c_0_63,plain,(
    ! [X19,X20] :
      ( ~ v1_relat_1(X19)
      | v1_relat_1(k7_relat_1(X19,X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_64,negated_conjecture,
    ( ~ v1_relat_1(k7_relat_1(esk4_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_47]),c_0_33])])).

cnf(c_0_65,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_33])]),
    [proof]).

%------------------------------------------------------------------------------
