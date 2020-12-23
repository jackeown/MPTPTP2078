%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:01:08 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   67 (1310 expanded)
%              Number of clauses        :   54 ( 494 expanded)
%              Number of leaves         :    6 ( 306 expanded)
%              Depth                    :   17
%              Number of atoms          :  343 (10431 expanded)
%              Number of equality atoms :   70 (2102 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   44 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d12_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( X3 = k9_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(X5,k1_relat_1(X1))
                  & r2_hidden(X5,X2)
                  & X4 = k1_funct_1(X1,X5) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

fof(d5_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( X2 = k2_relat_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                  & X3 = k1_funct_1(X1,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_1)).

fof(t4_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(k2_relat_1(X2),X1)
       => ( v1_funct_1(X2)
          & v1_funct_2(X2,k1_relat_1(X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(t145_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(c_0_6,plain,(
    ! [X6,X7,X8,X9,X11,X12,X13,X14,X16] :
      ( ( r2_hidden(esk1_4(X6,X7,X8,X9),k1_relat_1(X6))
        | ~ r2_hidden(X9,X8)
        | X8 != k9_relat_1(X6,X7)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( r2_hidden(esk1_4(X6,X7,X8,X9),X7)
        | ~ r2_hidden(X9,X8)
        | X8 != k9_relat_1(X6,X7)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( X9 = k1_funct_1(X6,esk1_4(X6,X7,X8,X9))
        | ~ r2_hidden(X9,X8)
        | X8 != k9_relat_1(X6,X7)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( ~ r2_hidden(X12,k1_relat_1(X6))
        | ~ r2_hidden(X12,X7)
        | X11 != k1_funct_1(X6,X12)
        | r2_hidden(X11,X8)
        | X8 != k9_relat_1(X6,X7)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( ~ r2_hidden(esk2_3(X6,X13,X14),X14)
        | ~ r2_hidden(X16,k1_relat_1(X6))
        | ~ r2_hidden(X16,X13)
        | esk2_3(X6,X13,X14) != k1_funct_1(X6,X16)
        | X14 = k9_relat_1(X6,X13)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( r2_hidden(esk3_3(X6,X13,X14),k1_relat_1(X6))
        | r2_hidden(esk2_3(X6,X13,X14),X14)
        | X14 = k9_relat_1(X6,X13)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( r2_hidden(esk3_3(X6,X13,X14),X13)
        | r2_hidden(esk2_3(X6,X13,X14),X14)
        | X14 = k9_relat_1(X6,X13)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( esk2_3(X6,X13,X14) = k1_funct_1(X6,esk3_3(X6,X13,X14))
        | r2_hidden(esk2_3(X6,X13,X14),X14)
        | X14 = k9_relat_1(X6,X13)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).

fof(c_0_7,plain,(
    ! [X26,X27,X28,X30,X31,X32,X34] :
      ( ( r2_hidden(esk5_3(X26,X27,X28),k1_relat_1(X26))
        | ~ r2_hidden(X28,X27)
        | X27 != k2_relat_1(X26)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( X28 = k1_funct_1(X26,esk5_3(X26,X27,X28))
        | ~ r2_hidden(X28,X27)
        | X27 != k2_relat_1(X26)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( ~ r2_hidden(X31,k1_relat_1(X26))
        | X30 != k1_funct_1(X26,X31)
        | r2_hidden(X30,X27)
        | X27 != k2_relat_1(X26)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( ~ r2_hidden(esk6_2(X26,X32),X32)
        | ~ r2_hidden(X34,k1_relat_1(X26))
        | esk6_2(X26,X32) != k1_funct_1(X26,X34)
        | X32 = k2_relat_1(X26)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( r2_hidden(esk7_2(X26,X32),k1_relat_1(X26))
        | r2_hidden(esk6_2(X26,X32),X32)
        | X32 = k2_relat_1(X26)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( esk6_2(X26,X32) = k1_funct_1(X26,esk7_2(X26,X32))
        | r2_hidden(esk6_2(X26,X32),X32)
        | X32 = k2_relat_1(X26)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_8,negated_conjecture,(
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

cnf(c_0_9,plain,
    ( r2_hidden(X4,X5)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,X3)
    | X4 != k1_funct_1(X2,X1)
    | X5 != k9_relat_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( X1 = k1_funct_1(X2,esk5_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_12,negated_conjecture,(
    ! [X43] :
      ( v1_relat_1(esk10_0)
      & v1_funct_1(esk10_0)
      & k1_relat_1(esk10_0) = esk8_0
      & ( ~ r2_hidden(X43,esk8_0)
        | r2_hidden(k1_funct_1(esk10_0,X43),esk9_0) )
      & ( ~ v1_funct_1(esk10_0)
        | ~ v1_funct_2(esk10_0,esk8_0,esk9_0)
        | ~ m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0))) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).

cnf(c_0_13,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k9_relat_1(X1,X3))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r2_hidden(X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_9])])).

cnf(c_0_14,plain,
    ( k1_funct_1(X1,esk5_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( r2_hidden(esk5_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( k1_relat_1(esk10_0) = esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( v1_funct_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( v1_relat_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_20,plain,
    ( X1 = k1_funct_1(X2,esk1_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k9_relat_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_21,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),k1_relat_1(X1))
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,k9_relat_1(X2,X3))
    | ~ r2_hidden(esk5_3(X2,k2_relat_1(X2),X1),X3)
    | ~ r2_hidden(X1,k2_relat_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk5_3(esk10_0,k2_relat_1(esk10_0),X1),esk8_0)
    | ~ r2_hidden(X1,k2_relat_1(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_24,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_19])])).

cnf(c_0_25,plain,
    ( k1_funct_1(X1,esk1_4(X1,X2,k9_relat_1(X1,X2),X3)) = X3
    | ~ r2_hidden(X3,k9_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( r2_hidden(esk1_4(X1,X2,k9_relat_1(X1,X2),X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,k9_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(X1,k9_relat_1(esk10_0,esk8_0))
    | ~ r2_hidden(X1,k2_relat_1(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_17]),c_0_18])])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(X1,k9_relat_1(X2,X3))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk10_0,X1),k9_relat_1(esk10_0,esk8_0))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_24]),c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_30,plain,
    ( esk6_2(X1,X2) = k1_funct_1(X1,esk7_2(X1,X2))
    | r2_hidden(esk6_2(X1,X2),X2)
    | X2 = k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_31,plain,
    ( r2_hidden(esk7_2(X1,X2),k1_relat_1(X1))
    | r2_hidden(esk6_2(X1,X2),X2)
    | X2 = k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk10_0,X1),k2_relat_1(esk10_0))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_17]),c_0_18])])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk1_4(esk10_0,X1,k9_relat_1(esk10_0,X1),X2),esk8_0)
    | ~ r2_hidden(X2,k9_relat_1(esk10_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_34,negated_conjecture,
    ( k1_funct_1(esk10_0,esk7_2(esk10_0,X1)) = esk6_2(esk10_0,X1)
    | X1 = k2_relat_1(esk10_0)
    | r2_hidden(esk6_2(esk10_0,X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_17]),c_0_18])])).

cnf(c_0_35,negated_conjecture,
    ( X1 = k2_relat_1(esk10_0)
    | r2_hidden(esk7_2(esk10_0,X1),esk8_0)
    | r2_hidden(esk6_2(esk10_0,X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_17]),c_0_16]),c_0_18])])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(X1,k2_relat_1(esk10_0))
    | ~ r2_hidden(X1,k9_relat_1(esk10_0,X2)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_25]),c_0_17]),c_0_18])]),c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( X1 = k2_relat_1(esk10_0)
    | r2_hidden(esk6_2(esk10_0,X1),k2_relat_1(esk10_0))
    | r2_hidden(esk6_2(esk10_0,X1),X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_34]),c_0_16]),c_0_17]),c_0_18])]),c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( k9_relat_1(esk10_0,X1) = k2_relat_1(esk10_0)
    | r2_hidden(esk6_2(esk10_0,k9_relat_1(esk10_0,X1)),k2_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

fof(c_0_39,plain,(
    ! [X18,X19,X20,X21,X22,X23,X24] :
      ( ( r2_hidden(X21,k1_relat_1(X18))
        | ~ r2_hidden(X21,X20)
        | X20 != k10_relat_1(X18,X19)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( r2_hidden(k1_funct_1(X18,X21),X19)
        | ~ r2_hidden(X21,X20)
        | X20 != k10_relat_1(X18,X19)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( ~ r2_hidden(X22,k1_relat_1(X18))
        | ~ r2_hidden(k1_funct_1(X18,X22),X19)
        | r2_hidden(X22,X20)
        | X20 != k10_relat_1(X18,X19)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( ~ r2_hidden(esk4_3(X18,X23,X24),X24)
        | ~ r2_hidden(esk4_3(X18,X23,X24),k1_relat_1(X18))
        | ~ r2_hidden(k1_funct_1(X18,esk4_3(X18,X23,X24)),X23)
        | X24 = k10_relat_1(X18,X23)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( r2_hidden(esk4_3(X18,X23,X24),k1_relat_1(X18))
        | r2_hidden(esk4_3(X18,X23,X24),X24)
        | X24 = k10_relat_1(X18,X23)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( r2_hidden(k1_funct_1(X18,esk4_3(X18,X23,X24)),X23)
        | r2_hidden(esk4_3(X18,X23,X24),X24)
        | X24 = k10_relat_1(X18,X23)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_funct_1])])])])])])).

cnf(c_0_40,plain,
    ( X2 = k2_relat_1(X1)
    | ~ r2_hidden(esk6_2(X1,X2),X2)
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | esk6_2(X1,X2) != k1_funct_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_41,negated_conjecture,
    ( k9_relat_1(esk10_0,X1) = k2_relat_1(esk10_0)
    | r2_hidden(esk6_2(esk10_0,k9_relat_1(esk10_0,X1)),k9_relat_1(esk10_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_38])).

cnf(c_0_42,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),k1_relat_1(X1))
    | r2_hidden(esk4_3(X1,X2,X3),X3)
    | X3 = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_43,plain,(
    ! [X38,X39] :
      ( ( v1_funct_1(X39)
        | ~ r1_tarski(k2_relat_1(X39),X38)
        | ~ v1_relat_1(X39)
        | ~ v1_funct_1(X39) )
      & ( v1_funct_2(X39,k1_relat_1(X39),X38)
        | ~ r1_tarski(k2_relat_1(X39),X38)
        | ~ v1_relat_1(X39)
        | ~ v1_funct_1(X39) )
      & ( m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X39),X38)))
        | ~ r1_tarski(k2_relat_1(X39),X38)
        | ~ v1_relat_1(X39)
        | ~ v1_funct_1(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).

cnf(c_0_44,negated_conjecture,
    ( k2_relat_1(esk10_0) = k9_relat_1(esk10_0,esk8_0)
    | esk6_2(esk10_0,k9_relat_1(esk10_0,esk8_0)) != k1_funct_1(esk10_0,X1)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_45,plain,
    ( X3 = k10_relat_1(X1,X2)
    | ~ r2_hidden(esk4_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk4_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(k1_funct_1(X1,esk4_3(X1,X2,X3)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk10_0,X1),esk9_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_47,plain,
    ( k10_relat_1(X1,X2) = k1_relat_1(X1)
    | r2_hidden(esk4_3(X1,X2,k1_relat_1(X1)),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(ef,[status(thm)],[c_0_42])).

cnf(c_0_48,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( k2_relat_1(esk10_0) = k9_relat_1(esk10_0,esk8_0)
    | ~ r2_hidden(esk5_3(esk10_0,k2_relat_1(esk10_0),esk6_2(esk10_0,k9_relat_1(esk10_0,esk8_0))),esk8_0) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_14]),c_0_17]),c_0_18])])]),c_0_38])).

fof(c_0_50,plain,(
    ! [X36,X37] :
      ( ~ v1_relat_1(X37)
      | ~ v1_funct_1(X37)
      | r1_tarski(k9_relat_1(X37,k10_relat_1(X37,X36)),X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).

cnf(c_0_51,negated_conjecture,
    ( X1 = k10_relat_1(esk10_0,esk9_0)
    | ~ r2_hidden(esk4_3(esk10_0,esk9_0,X1),esk8_0)
    | ~ r2_hidden(esk4_3(esk10_0,esk9_0,X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_52,negated_conjecture,
    ( k10_relat_1(esk10_0,X1) = esk8_0
    | r2_hidden(esk4_3(esk10_0,X1,esk8_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_17]),c_0_16]),c_0_16]),c_0_16]),c_0_18])])).

cnf(c_0_53,negated_conjecture,
    ( v1_funct_2(esk10_0,esk8_0,X1)
    | ~ r1_tarski(k2_relat_1(esk10_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_54,negated_conjecture,
    ( k2_relat_1(esk10_0) = k9_relat_1(esk10_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_23]),c_0_38])).

cnf(c_0_55,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( k10_relat_1(esk10_0,esk9_0) = esk8_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( ~ v1_funct_1(esk10_0)
    | ~ v1_funct_2(esk10_0,esk8_0,esk9_0)
    | ~ m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_58,negated_conjecture,
    ( v1_funct_2(esk10_0,esk8_0,X1)
    | ~ r1_tarski(k9_relat_1(esk10_0,esk8_0),X1) ),
    inference(rw,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk10_0,esk8_0),esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_17]),c_0_18])])).

cnf(c_0_60,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_61,negated_conjecture,
    ( ~ m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0)))
    | ~ v1_funct_2(esk10_0,esk8_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_17])])).

cnf(c_0_62,negated_conjecture,
    ( v1_funct_2(esk10_0,esk8_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,X1)))
    | ~ r1_tarski(k2_relat_1(esk10_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_64,negated_conjecture,
    ( ~ m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62])])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,X1)))
    | ~ r1_tarski(k9_relat_1(esk10_0,esk8_0),X1) ),
    inference(rw,[status(thm)],[c_0_63,c_0_54])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_59])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:37:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.43  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S05AN
% 0.20/0.43  # and selection function PSelectComplexExceptUniqMaxPosHorn.
% 0.20/0.43  #
% 0.20/0.43  # Preprocessing time       : 0.029 s
% 0.20/0.43  # Presaturation interreduction done
% 0.20/0.43  
% 0.20/0.43  # Proof found!
% 0.20/0.43  # SZS status Theorem
% 0.20/0.43  # SZS output start CNFRefutation
% 0.20/0.43  fof(d12_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(X3=k9_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:((r2_hidden(X5,k1_relat_1(X1))&r2_hidden(X5,X2))&X4=k1_funct_1(X1,X5))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_1)).
% 0.20/0.43  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 0.20/0.43  fof(t5_funct_2, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X3)=X1&![X4]:(r2_hidden(X4,X1)=>r2_hidden(k1_funct_1(X3,X4),X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_funct_2)).
% 0.20/0.43  fof(d13_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(X3=k10_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,k1_relat_1(X1))&r2_hidden(k1_funct_1(X1,X4),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_funct_1)).
% 0.20/0.43  fof(t4_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(k2_relat_1(X2),X1)=>((v1_funct_1(X2)&v1_funct_2(X2,k1_relat_1(X2),X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 0.20/0.43  fof(t145_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 0.20/0.43  fof(c_0_6, plain, ![X6, X7, X8, X9, X11, X12, X13, X14, X16]:(((((r2_hidden(esk1_4(X6,X7,X8,X9),k1_relat_1(X6))|~r2_hidden(X9,X8)|X8!=k9_relat_1(X6,X7)|(~v1_relat_1(X6)|~v1_funct_1(X6)))&(r2_hidden(esk1_4(X6,X7,X8,X9),X7)|~r2_hidden(X9,X8)|X8!=k9_relat_1(X6,X7)|(~v1_relat_1(X6)|~v1_funct_1(X6))))&(X9=k1_funct_1(X6,esk1_4(X6,X7,X8,X9))|~r2_hidden(X9,X8)|X8!=k9_relat_1(X6,X7)|(~v1_relat_1(X6)|~v1_funct_1(X6))))&(~r2_hidden(X12,k1_relat_1(X6))|~r2_hidden(X12,X7)|X11!=k1_funct_1(X6,X12)|r2_hidden(X11,X8)|X8!=k9_relat_1(X6,X7)|(~v1_relat_1(X6)|~v1_funct_1(X6))))&((~r2_hidden(esk2_3(X6,X13,X14),X14)|(~r2_hidden(X16,k1_relat_1(X6))|~r2_hidden(X16,X13)|esk2_3(X6,X13,X14)!=k1_funct_1(X6,X16))|X14=k9_relat_1(X6,X13)|(~v1_relat_1(X6)|~v1_funct_1(X6)))&(((r2_hidden(esk3_3(X6,X13,X14),k1_relat_1(X6))|r2_hidden(esk2_3(X6,X13,X14),X14)|X14=k9_relat_1(X6,X13)|(~v1_relat_1(X6)|~v1_funct_1(X6)))&(r2_hidden(esk3_3(X6,X13,X14),X13)|r2_hidden(esk2_3(X6,X13,X14),X14)|X14=k9_relat_1(X6,X13)|(~v1_relat_1(X6)|~v1_funct_1(X6))))&(esk2_3(X6,X13,X14)=k1_funct_1(X6,esk3_3(X6,X13,X14))|r2_hidden(esk2_3(X6,X13,X14),X14)|X14=k9_relat_1(X6,X13)|(~v1_relat_1(X6)|~v1_funct_1(X6)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).
% 0.20/0.43  fof(c_0_7, plain, ![X26, X27, X28, X30, X31, X32, X34]:((((r2_hidden(esk5_3(X26,X27,X28),k1_relat_1(X26))|~r2_hidden(X28,X27)|X27!=k2_relat_1(X26)|(~v1_relat_1(X26)|~v1_funct_1(X26)))&(X28=k1_funct_1(X26,esk5_3(X26,X27,X28))|~r2_hidden(X28,X27)|X27!=k2_relat_1(X26)|(~v1_relat_1(X26)|~v1_funct_1(X26))))&(~r2_hidden(X31,k1_relat_1(X26))|X30!=k1_funct_1(X26,X31)|r2_hidden(X30,X27)|X27!=k2_relat_1(X26)|(~v1_relat_1(X26)|~v1_funct_1(X26))))&((~r2_hidden(esk6_2(X26,X32),X32)|(~r2_hidden(X34,k1_relat_1(X26))|esk6_2(X26,X32)!=k1_funct_1(X26,X34))|X32=k2_relat_1(X26)|(~v1_relat_1(X26)|~v1_funct_1(X26)))&((r2_hidden(esk7_2(X26,X32),k1_relat_1(X26))|r2_hidden(esk6_2(X26,X32),X32)|X32=k2_relat_1(X26)|(~v1_relat_1(X26)|~v1_funct_1(X26)))&(esk6_2(X26,X32)=k1_funct_1(X26,esk7_2(X26,X32))|r2_hidden(esk6_2(X26,X32),X32)|X32=k2_relat_1(X26)|(~v1_relat_1(X26)|~v1_funct_1(X26)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.20/0.43  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X3)=X1&![X4]:(r2_hidden(X4,X1)=>r2_hidden(k1_funct_1(X3,X4),X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))))), inference(assume_negation,[status(cth)],[t5_funct_2])).
% 0.20/0.43  cnf(c_0_9, plain, (r2_hidden(X4,X5)|~r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(X1,X3)|X4!=k1_funct_1(X2,X1)|X5!=k9_relat_1(X2,X3)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.43  cnf(c_0_10, plain, (X1=k1_funct_1(X2,esk5_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.43  cnf(c_0_11, plain, (r2_hidden(esk5_3(X1,X2,X3),k1_relat_1(X1))|~r2_hidden(X3,X2)|X2!=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.43  fof(c_0_12, negated_conjecture, ![X43]:((v1_relat_1(esk10_0)&v1_funct_1(esk10_0))&((k1_relat_1(esk10_0)=esk8_0&(~r2_hidden(X43,esk8_0)|r2_hidden(k1_funct_1(esk10_0,X43),esk9_0)))&(~v1_funct_1(esk10_0)|~v1_funct_2(esk10_0,esk8_0,esk9_0)|~m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0)))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).
% 0.20/0.43  cnf(c_0_13, plain, (r2_hidden(k1_funct_1(X1,X2),k9_relat_1(X1,X3))|~r2_hidden(X2,k1_relat_1(X1))|~r2_hidden(X2,X3)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_9])])).
% 0.20/0.43  cnf(c_0_14, plain, (k1_funct_1(X1,esk5_3(X1,k2_relat_1(X1),X2))=X2|~r2_hidden(X2,k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_10])).
% 0.20/0.43  cnf(c_0_15, plain, (r2_hidden(esk5_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))|~r2_hidden(X2,k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_11])).
% 0.20/0.43  cnf(c_0_16, negated_conjecture, (k1_relat_1(esk10_0)=esk8_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.43  cnf(c_0_17, negated_conjecture, (v1_funct_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.43  cnf(c_0_18, negated_conjecture, (v1_relat_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.43  cnf(c_0_19, plain, (r2_hidden(X3,X4)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|X4!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.43  cnf(c_0_20, plain, (X1=k1_funct_1(X2,esk1_4(X2,X3,X4,X1))|~r2_hidden(X1,X4)|X4!=k9_relat_1(X2,X3)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.43  cnf(c_0_21, plain, (r2_hidden(esk1_4(X1,X2,X3,X4),k1_relat_1(X1))|~r2_hidden(X4,X3)|X3!=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.43  cnf(c_0_22, plain, (r2_hidden(X1,k9_relat_1(X2,X3))|~r2_hidden(esk5_3(X2,k2_relat_1(X2),X1),X3)|~r2_hidden(X1,k2_relat_1(X2))|~v1_funct_1(X2)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15])).
% 0.20/0.43  cnf(c_0_23, negated_conjecture, (r2_hidden(esk5_3(esk10_0,k2_relat_1(esk10_0),X1),esk8_0)|~r2_hidden(X1,k2_relat_1(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18])])).
% 0.20/0.43  cnf(c_0_24, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~r2_hidden(X2,k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_19])])).
% 0.20/0.43  cnf(c_0_25, plain, (k1_funct_1(X1,esk1_4(X1,X2,k9_relat_1(X1,X2),X3))=X3|~r2_hidden(X3,k9_relat_1(X1,X2))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_20])).
% 0.20/0.43  cnf(c_0_26, plain, (r2_hidden(esk1_4(X1,X2,k9_relat_1(X1,X2),X3),k1_relat_1(X1))|~r2_hidden(X3,k9_relat_1(X1,X2))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_21])).
% 0.20/0.43  cnf(c_0_27, negated_conjecture, (r2_hidden(X1,k9_relat_1(esk10_0,esk8_0))|~r2_hidden(X1,k2_relat_1(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_17]), c_0_18])])).
% 0.20/0.43  cnf(c_0_28, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(X1,k9_relat_1(X2,X3))|~v1_funct_1(X2)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])).
% 0.20/0.43  cnf(c_0_29, negated_conjecture, (r2_hidden(k1_funct_1(esk10_0,X1),k9_relat_1(esk10_0,esk8_0))|~r2_hidden(X1,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_24]), c_0_16]), c_0_17]), c_0_18])])).
% 0.20/0.43  cnf(c_0_30, plain, (esk6_2(X1,X2)=k1_funct_1(X1,esk7_2(X1,X2))|r2_hidden(esk6_2(X1,X2),X2)|X2=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.43  cnf(c_0_31, plain, (r2_hidden(esk7_2(X1,X2),k1_relat_1(X1))|r2_hidden(esk6_2(X1,X2),X2)|X2=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.43  cnf(c_0_32, negated_conjecture, (r2_hidden(k1_funct_1(esk10_0,X1),k2_relat_1(esk10_0))|~r2_hidden(X1,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_17]), c_0_18])])).
% 0.20/0.43  cnf(c_0_33, negated_conjecture, (r2_hidden(esk1_4(esk10_0,X1,k9_relat_1(esk10_0,X1),X2),esk8_0)|~r2_hidden(X2,k9_relat_1(esk10_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_16]), c_0_17]), c_0_18])])).
% 0.20/0.43  cnf(c_0_34, negated_conjecture, (k1_funct_1(esk10_0,esk7_2(esk10_0,X1))=esk6_2(esk10_0,X1)|X1=k2_relat_1(esk10_0)|r2_hidden(esk6_2(esk10_0,X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_17]), c_0_18])])).
% 0.20/0.43  cnf(c_0_35, negated_conjecture, (X1=k2_relat_1(esk10_0)|r2_hidden(esk7_2(esk10_0,X1),esk8_0)|r2_hidden(esk6_2(esk10_0,X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_17]), c_0_16]), c_0_18])])).
% 0.20/0.43  cnf(c_0_36, negated_conjecture, (r2_hidden(X1,k2_relat_1(esk10_0))|~r2_hidden(X1,k9_relat_1(esk10_0,X2))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_25]), c_0_17]), c_0_18])]), c_0_33])).
% 0.20/0.43  cnf(c_0_37, negated_conjecture, (X1=k2_relat_1(esk10_0)|r2_hidden(esk6_2(esk10_0,X1),k2_relat_1(esk10_0))|r2_hidden(esk6_2(esk10_0,X1),X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_34]), c_0_16]), c_0_17]), c_0_18])]), c_0_35])).
% 0.20/0.43  cnf(c_0_38, negated_conjecture, (k9_relat_1(esk10_0,X1)=k2_relat_1(esk10_0)|r2_hidden(esk6_2(esk10_0,k9_relat_1(esk10_0,X1)),k2_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.43  fof(c_0_39, plain, ![X18, X19, X20, X21, X22, X23, X24]:((((r2_hidden(X21,k1_relat_1(X18))|~r2_hidden(X21,X20)|X20!=k10_relat_1(X18,X19)|(~v1_relat_1(X18)|~v1_funct_1(X18)))&(r2_hidden(k1_funct_1(X18,X21),X19)|~r2_hidden(X21,X20)|X20!=k10_relat_1(X18,X19)|(~v1_relat_1(X18)|~v1_funct_1(X18))))&(~r2_hidden(X22,k1_relat_1(X18))|~r2_hidden(k1_funct_1(X18,X22),X19)|r2_hidden(X22,X20)|X20!=k10_relat_1(X18,X19)|(~v1_relat_1(X18)|~v1_funct_1(X18))))&((~r2_hidden(esk4_3(X18,X23,X24),X24)|(~r2_hidden(esk4_3(X18,X23,X24),k1_relat_1(X18))|~r2_hidden(k1_funct_1(X18,esk4_3(X18,X23,X24)),X23))|X24=k10_relat_1(X18,X23)|(~v1_relat_1(X18)|~v1_funct_1(X18)))&((r2_hidden(esk4_3(X18,X23,X24),k1_relat_1(X18))|r2_hidden(esk4_3(X18,X23,X24),X24)|X24=k10_relat_1(X18,X23)|(~v1_relat_1(X18)|~v1_funct_1(X18)))&(r2_hidden(k1_funct_1(X18,esk4_3(X18,X23,X24)),X23)|r2_hidden(esk4_3(X18,X23,X24),X24)|X24=k10_relat_1(X18,X23)|(~v1_relat_1(X18)|~v1_funct_1(X18)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_funct_1])])])])])])).
% 0.20/0.43  cnf(c_0_40, plain, (X2=k2_relat_1(X1)|~r2_hidden(esk6_2(X1,X2),X2)|~r2_hidden(X3,k1_relat_1(X1))|esk6_2(X1,X2)!=k1_funct_1(X1,X3)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.43  cnf(c_0_41, negated_conjecture, (k9_relat_1(esk10_0,X1)=k2_relat_1(esk10_0)|r2_hidden(esk6_2(esk10_0,k9_relat_1(esk10_0,X1)),k9_relat_1(esk10_0,esk8_0))), inference(spm,[status(thm)],[c_0_27, c_0_38])).
% 0.20/0.43  cnf(c_0_42, plain, (r2_hidden(esk4_3(X1,X2,X3),k1_relat_1(X1))|r2_hidden(esk4_3(X1,X2,X3),X3)|X3=k10_relat_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.43  fof(c_0_43, plain, ![X38, X39]:(((v1_funct_1(X39)|~r1_tarski(k2_relat_1(X39),X38)|(~v1_relat_1(X39)|~v1_funct_1(X39)))&(v1_funct_2(X39,k1_relat_1(X39),X38)|~r1_tarski(k2_relat_1(X39),X38)|(~v1_relat_1(X39)|~v1_funct_1(X39))))&(m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X39),X38)))|~r1_tarski(k2_relat_1(X39),X38)|(~v1_relat_1(X39)|~v1_funct_1(X39)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).
% 0.20/0.43  cnf(c_0_44, negated_conjecture, (k2_relat_1(esk10_0)=k9_relat_1(esk10_0,esk8_0)|esk6_2(esk10_0,k9_relat_1(esk10_0,esk8_0))!=k1_funct_1(esk10_0,X1)|~r2_hidden(X1,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_16]), c_0_17]), c_0_18])])).
% 0.20/0.43  cnf(c_0_45, plain, (X3=k10_relat_1(X1,X2)|~r2_hidden(esk4_3(X1,X2,X3),X3)|~r2_hidden(esk4_3(X1,X2,X3),k1_relat_1(X1))|~r2_hidden(k1_funct_1(X1,esk4_3(X1,X2,X3)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.43  cnf(c_0_46, negated_conjecture, (r2_hidden(k1_funct_1(esk10_0,X1),esk9_0)|~r2_hidden(X1,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.43  cnf(c_0_47, plain, (k10_relat_1(X1,X2)=k1_relat_1(X1)|r2_hidden(esk4_3(X1,X2,k1_relat_1(X1)),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(ef,[status(thm)],[c_0_42])).
% 0.20/0.43  cnf(c_0_48, plain, (v1_funct_2(X1,k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.43  cnf(c_0_49, negated_conjecture, (k2_relat_1(esk10_0)=k9_relat_1(esk10_0,esk8_0)|~r2_hidden(esk5_3(esk10_0,k2_relat_1(esk10_0),esk6_2(esk10_0,k9_relat_1(esk10_0,esk8_0))),esk8_0)), inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_14]), c_0_17]), c_0_18])])]), c_0_38])).
% 0.20/0.43  fof(c_0_50, plain, ![X36, X37]:(~v1_relat_1(X37)|~v1_funct_1(X37)|r1_tarski(k9_relat_1(X37,k10_relat_1(X37,X36)),X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).
% 0.20/0.43  cnf(c_0_51, negated_conjecture, (X1=k10_relat_1(esk10_0,esk9_0)|~r2_hidden(esk4_3(esk10_0,esk9_0,X1),esk8_0)|~r2_hidden(esk4_3(esk10_0,esk9_0,X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_16]), c_0_17]), c_0_18])])).
% 0.20/0.43  cnf(c_0_52, negated_conjecture, (k10_relat_1(esk10_0,X1)=esk8_0|r2_hidden(esk4_3(esk10_0,X1,esk8_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_17]), c_0_16]), c_0_16]), c_0_16]), c_0_18])])).
% 0.20/0.43  cnf(c_0_53, negated_conjecture, (v1_funct_2(esk10_0,esk8_0,X1)|~r1_tarski(k2_relat_1(esk10_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_16]), c_0_17]), c_0_18])])).
% 0.20/0.43  cnf(c_0_54, negated_conjecture, (k2_relat_1(esk10_0)=k9_relat_1(esk10_0,esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_23]), c_0_38])).
% 0.20/0.43  cnf(c_0_55, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.43  cnf(c_0_56, negated_conjecture, (k10_relat_1(esk10_0,esk9_0)=esk8_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_52])).
% 0.20/0.43  cnf(c_0_57, negated_conjecture, (~v1_funct_1(esk10_0)|~v1_funct_2(esk10_0,esk8_0,esk9_0)|~m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.43  cnf(c_0_58, negated_conjecture, (v1_funct_2(esk10_0,esk8_0,X1)|~r1_tarski(k9_relat_1(esk10_0,esk8_0),X1)), inference(rw,[status(thm)],[c_0_53, c_0_54])).
% 0.20/0.43  cnf(c_0_59, negated_conjecture, (r1_tarski(k9_relat_1(esk10_0,esk8_0),esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_17]), c_0_18])])).
% 0.20/0.43  cnf(c_0_60, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.43  cnf(c_0_61, negated_conjecture, (~m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0)))|~v1_funct_2(esk10_0,esk8_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_17])])).
% 0.20/0.43  cnf(c_0_62, negated_conjecture, (v1_funct_2(esk10_0,esk8_0,esk9_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.20/0.43  cnf(c_0_63, negated_conjecture, (m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,X1)))|~r1_tarski(k2_relat_1(esk10_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_16]), c_0_17]), c_0_18])])).
% 0.20/0.43  cnf(c_0_64, negated_conjecture, (~m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62])])).
% 0.20/0.43  cnf(c_0_65, negated_conjecture, (m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,X1)))|~r1_tarski(k9_relat_1(esk10_0,esk8_0),X1)), inference(rw,[status(thm)],[c_0_63, c_0_54])).
% 0.20/0.43  cnf(c_0_66, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_59])]), ['proof']).
% 0.20/0.43  # SZS output end CNFRefutation
% 0.20/0.43  # Proof object total steps             : 67
% 0.20/0.43  # Proof object clause steps            : 54
% 0.20/0.43  # Proof object formula steps           : 13
% 0.20/0.43  # Proof object conjectures             : 34
% 0.20/0.43  # Proof object clause conjectures      : 31
% 0.20/0.43  # Proof object formula conjectures     : 3
% 0.20/0.43  # Proof object initial clauses used    : 19
% 0.20/0.43  # Proof object initial formulas used   : 6
% 0.20/0.43  # Proof object generating inferences   : 25
% 0.20/0.43  # Proof object simplifying inferences  : 77
% 0.20/0.43  # Training examples: 0 positive, 0 negative
% 0.20/0.43  # Parsed axioms                        : 6
% 0.20/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.43  # Initial clauses                      : 29
% 0.20/0.43  # Removed in clause preprocessing      : 1
% 0.20/0.43  # Initial clauses in saturation        : 28
% 0.20/0.43  # Processed clauses                    : 484
% 0.20/0.43  # ...of these trivial                  : 0
% 0.20/0.43  # ...subsumed                          : 233
% 0.20/0.43  # ...remaining for further processing  : 251
% 0.20/0.43  # Other redundant clauses eliminated   : 20
% 0.20/0.43  # Clauses deleted for lack of memory   : 0
% 0.20/0.43  # Backward-subsumed                    : 9
% 0.20/0.43  # Backward-rewritten                   : 96
% 0.20/0.43  # Generated clauses                    : 1244
% 0.20/0.43  # ...of the previous two non-trivial   : 1268
% 0.20/0.43  # Contextual simplify-reflections      : 25
% 0.20/0.43  # Paramodulations                      : 1212
% 0.20/0.43  # Factorizations                       : 13
% 0.20/0.43  # Equation resolutions                 : 21
% 0.20/0.43  # Propositional unsat checks           : 0
% 0.20/0.43  #    Propositional check models        : 0
% 0.20/0.43  #    Propositional check unsatisfiable : 0
% 0.20/0.43  #    Propositional clauses             : 0
% 0.20/0.43  #    Propositional clauses after purity: 0
% 0.20/0.43  #    Propositional unsat core size     : 0
% 0.20/0.43  #    Propositional preprocessing time  : 0.000
% 0.20/0.43  #    Propositional encoding time       : 0.000
% 0.20/0.43  #    Propositional solver time         : 0.000
% 0.20/0.43  #    Success case prop preproc time    : 0.000
% 0.20/0.43  #    Success case prop encoding time   : 0.000
% 0.20/0.43  #    Success case prop solver time     : 0.000
% 0.20/0.43  # Current number of processed clauses  : 108
% 0.20/0.43  #    Positive orientable unit clauses  : 10
% 0.20/0.43  #    Positive unorientable unit clauses: 0
% 0.20/0.43  #    Negative unit clauses             : 1
% 0.20/0.43  #    Non-unit-clauses                  : 97
% 0.20/0.43  # Current number of unprocessed clauses: 836
% 0.20/0.43  # ...number of literals in the above   : 4661
% 0.20/0.43  # Current number of archived formulas  : 0
% 0.20/0.43  # Current number of archived clauses   : 133
% 0.20/0.43  # Clause-clause subsumption calls (NU) : 4336
% 0.20/0.43  # Rec. Clause-clause subsumption calls : 1422
% 0.20/0.43  # Non-unit clause-clause subsumptions  : 266
% 0.20/0.43  # Unit Clause-clause subsumption calls : 116
% 0.20/0.43  # Rewrite failures with RHS unbound    : 0
% 0.20/0.43  # BW rewrite match attempts            : 8
% 0.20/0.43  # BW rewrite match successes           : 5
% 0.20/0.43  # Condensation attempts                : 0
% 0.20/0.43  # Condensation successes               : 0
% 0.20/0.43  # Termbank termtop insertions          : 35261
% 0.20/0.43  
% 0.20/0.43  # -------------------------------------------------
% 0.20/0.43  # User time                : 0.080 s
% 0.20/0.43  # System time              : 0.005 s
% 0.20/0.43  # Total time               : 0.085 s
% 0.20/0.43  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
