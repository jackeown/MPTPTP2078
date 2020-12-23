%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:46 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 614 expanded)
%              Number of clauses        :   41 ( 312 expanded)
%              Number of leaves         :    5 ( 130 expanded)
%              Depth                    :   10
%              Number of atoms          :  259 (5480 expanded)
%              Number of equality atoms :   59 (2098 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal clause size      :   44 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k1_funct_2(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5] :
              ( v1_relat_1(X5)
              & v1_funct_1(X5)
              & X4 = X5
              & k1_relat_1(X5) = X1
              & r1_tarski(k2_relat_1(X5),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_funct_2)).

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

fof(t121_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( r2_hidden(X3,k1_funct_2(X1,X2))
     => ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t5_funct_2,axiom,(
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

fof(c_0_5,plain,(
    ! [X22,X23,X24,X25,X27,X28,X29,X30,X31,X33] :
      ( ( v1_relat_1(esk5_4(X22,X23,X24,X25))
        | ~ r2_hidden(X25,X24)
        | X24 != k1_funct_2(X22,X23) )
      & ( v1_funct_1(esk5_4(X22,X23,X24,X25))
        | ~ r2_hidden(X25,X24)
        | X24 != k1_funct_2(X22,X23) )
      & ( X25 = esk5_4(X22,X23,X24,X25)
        | ~ r2_hidden(X25,X24)
        | X24 != k1_funct_2(X22,X23) )
      & ( k1_relat_1(esk5_4(X22,X23,X24,X25)) = X22
        | ~ r2_hidden(X25,X24)
        | X24 != k1_funct_2(X22,X23) )
      & ( r1_tarski(k2_relat_1(esk5_4(X22,X23,X24,X25)),X23)
        | ~ r2_hidden(X25,X24)
        | X24 != k1_funct_2(X22,X23) )
      & ( ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28)
        | X27 != X28
        | k1_relat_1(X28) != X22
        | ~ r1_tarski(k2_relat_1(X28),X23)
        | r2_hidden(X27,X24)
        | X24 != k1_funct_2(X22,X23) )
      & ( ~ r2_hidden(esk6_3(X29,X30,X31),X31)
        | ~ v1_relat_1(X33)
        | ~ v1_funct_1(X33)
        | esk6_3(X29,X30,X31) != X33
        | k1_relat_1(X33) != X29
        | ~ r1_tarski(k2_relat_1(X33),X30)
        | X31 = k1_funct_2(X29,X30) )
      & ( v1_relat_1(esk7_3(X29,X30,X31))
        | r2_hidden(esk6_3(X29,X30,X31),X31)
        | X31 = k1_funct_2(X29,X30) )
      & ( v1_funct_1(esk7_3(X29,X30,X31))
        | r2_hidden(esk6_3(X29,X30,X31),X31)
        | X31 = k1_funct_2(X29,X30) )
      & ( esk6_3(X29,X30,X31) = esk7_3(X29,X30,X31)
        | r2_hidden(esk6_3(X29,X30,X31),X31)
        | X31 = k1_funct_2(X29,X30) )
      & ( k1_relat_1(esk7_3(X29,X30,X31)) = X29
        | r2_hidden(esk6_3(X29,X30,X31),X31)
        | X31 = k1_funct_2(X29,X30) )
      & ( r1_tarski(k2_relat_1(esk7_3(X29,X30,X31)),X30)
        | r2_hidden(esk6_3(X29,X30,X31),X31)
        | X31 = k1_funct_2(X29,X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).

fof(c_0_6,plain,(
    ! [X12,X13,X14,X16,X17,X18,X20] :
      ( ( r2_hidden(esk2_3(X12,X13,X14),k1_relat_1(X12))
        | ~ r2_hidden(X14,X13)
        | X13 != k2_relat_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( X14 = k1_funct_1(X12,esk2_3(X12,X13,X14))
        | ~ r2_hidden(X14,X13)
        | X13 != k2_relat_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( ~ r2_hidden(X17,k1_relat_1(X12))
        | X16 != k1_funct_1(X12,X17)
        | r2_hidden(X16,X13)
        | X13 != k2_relat_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( ~ r2_hidden(esk3_2(X12,X18),X18)
        | ~ r2_hidden(X20,k1_relat_1(X12))
        | esk3_2(X12,X18) != k1_funct_1(X12,X20)
        | X18 = k2_relat_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( r2_hidden(esk4_2(X12,X18),k1_relat_1(X12))
        | r2_hidden(esk3_2(X12,X18),X18)
        | X18 = k2_relat_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( esk3_2(X12,X18) = k1_funct_1(X12,esk4_2(X12,X18))
        | r2_hidden(esk3_2(X12,X18),X18)
        | X18 = k2_relat_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

cnf(c_0_7,plain,
    ( k1_relat_1(esk5_4(X1,X2,X3,X4)) = X1
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( X1 = esk5_4(X2,X3,X4,X1)
    | ~ r2_hidden(X1,X4)
    | X4 != k1_funct_2(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r2_hidden(X3,k1_funct_2(X1,X2))
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t121_funct_2])).

cnf(c_0_10,plain,
    ( v1_funct_1(esk5_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,plain,
    ( v1_relat_1(esk5_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_12,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_13,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,plain,
    ( k1_relat_1(esk5_4(X1,X2,k1_funct_2(X1,X2),X3)) = X1
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_7])).

cnf(c_0_15,plain,
    ( esk5_4(X1,X2,k1_funct_2(X1,X2),X3) = X3
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_8])).

fof(c_0_16,negated_conjecture,
    ( r2_hidden(esk11_0,k1_funct_2(esk9_0,esk10_0))
    & ( ~ v1_funct_1(esk11_0)
      | ~ v1_funct_2(esk11_0,esk9_0,esk10_0)
      | ~ m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_17,plain,
    ( v1_funct_1(esk5_4(X1,X2,k1_funct_2(X1,X2),X3))
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( v1_relat_1(esk5_4(X1,X2,k1_funct_2(X1,X2),X3))
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( r1_tarski(k2_relat_1(esk5_4(X1,X2,X3,X4)),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_20,plain,(
    ! [X35,X36,X37] :
      ( ( v1_funct_1(X37)
        | r2_hidden(esk8_3(X35,X36,X37),X35)
        | k1_relat_1(X37) != X35
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37) )
      & ( v1_funct_2(X37,X35,X36)
        | r2_hidden(esk8_3(X35,X36,X37),X35)
        | k1_relat_1(X37) != X35
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37) )
      & ( m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
        | r2_hidden(esk8_3(X35,X36,X37),X35)
        | k1_relat_1(X37) != X35
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37) )
      & ( v1_funct_1(X37)
        | ~ r2_hidden(k1_funct_1(X37,esk8_3(X35,X36,X37)),X36)
        | k1_relat_1(X37) != X35
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37) )
      & ( v1_funct_2(X37,X35,X36)
        | ~ r2_hidden(k1_funct_1(X37,esk8_3(X35,X36,X37)),X36)
        | k1_relat_1(X37) != X35
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37) )
      & ( m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
        | ~ r2_hidden(k1_funct_1(X37,esk8_3(X35,X36,X37)),X36)
        | k1_relat_1(X37) != X35
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_funct_2])])])])).

cnf(c_0_21,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_13])])).

cnf(c_0_23,plain,
    ( k1_relat_1(X1) = X2
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk11_0,k1_funct_2(esk9_0,esk10_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( v1_funct_1(X1)
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_15])).

cnf(c_0_26,plain,
    ( v1_relat_1(X1)
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_15])).

cnf(c_0_27,plain,
    ( r1_tarski(k2_relat_1(esk5_4(X1,X2,k1_funct_2(X1,X2),X3)),X2)
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | r2_hidden(esk8_3(X2,X3,X1),X2)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( v1_funct_2(X1,X2,X3)
    | r2_hidden(esk8_3(X2,X3,X1),X2)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( r2_hidden(k1_funct_1(X1,X2),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( k1_relat_1(esk11_0) = esk9_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_1(esk11_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( v1_relat_1(esk11_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_24])).

cnf(c_0_34,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ r2_hidden(X1,k1_funct_2(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_15])).

cnf(c_0_35,negated_conjecture,
    ( ~ v1_funct_1(esk11_0)
    | ~ v1_funct_2(esk11_0,esk9_0,esk10_0)
    | ~ m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_36,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | r2_hidden(esk8_3(k1_relat_1(X1),X2,X1),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),X2)
    | r2_hidden(esk8_3(k1_relat_1(X1),X2,X1),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ r2_hidden(k1_funct_1(X1,esk8_3(X2,X3,X1)),X3)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk11_0,X1),X2)
    | ~ r2_hidden(X1,esk9_0)
    | ~ r1_tarski(k2_relat_1(esk11_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33])])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk11_0),esk10_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_24])).

cnf(c_0_41,negated_conjecture,
    ( ~ m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0)))
    | ~ v1_funct_2(esk11_0,esk9_0,esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_32])])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,X1)))
    | r2_hidden(esk8_3(esk9_0,X1,esk11_0),esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_32]),c_0_31]),c_0_31]),c_0_31]),c_0_33])])).

cnf(c_0_43,negated_conjecture,
    ( v1_funct_2(esk11_0,esk9_0,X1)
    | r2_hidden(esk8_3(esk9_0,X1,esk11_0),esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_32]),c_0_31]),c_0_31]),c_0_31]),c_0_33])])).

cnf(c_0_44,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k1_funct_1(X1,esk8_3(k1_relat_1(X1),X2,X1)),X2) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk11_0,X1),esk10_0)
    | ~ r2_hidden(X1,esk9_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk8_3(esk9_0,esk10_0,esk11_0),esk9_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

cnf(c_0_47,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(k1_funct_1(X1,esk8_3(X2,X3,X1)),X3)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_48,negated_conjecture,
    ( v1_funct_2(esk11_0,esk9_0,esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_31]),c_0_32]),c_0_33]),c_0_31]),c_0_46])])).

cnf(c_0_49,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k1_funct_1(X1,esk8_3(k1_relat_1(X1),X2,X1)),X2) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( ~ m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_48])])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_45]),c_0_31]),c_0_32]),c_0_33]),c_0_31]),c_0_46])]),c_0_50]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:59:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.028 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(d2_funct_2, axiom, ![X1, X2, X3]:(X3=k1_funct_2(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:((((v1_relat_1(X5)&v1_funct_1(X5))&X4=X5)&k1_relat_1(X5)=X1)&r1_tarski(k2_relat_1(X5),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_funct_2)).
% 0.19/0.38  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 0.19/0.38  fof(t121_funct_2, conjecture, ![X1, X2, X3]:(r2_hidden(X3,k1_funct_2(X1,X2))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_2)).
% 0.19/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.38  fof(t5_funct_2, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X3)=X1&![X4]:(r2_hidden(X4,X1)=>r2_hidden(k1_funct_1(X3,X4),X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_funct_2)).
% 0.19/0.38  fof(c_0_5, plain, ![X22, X23, X24, X25, X27, X28, X29, X30, X31, X33]:(((((((v1_relat_1(esk5_4(X22,X23,X24,X25))|~r2_hidden(X25,X24)|X24!=k1_funct_2(X22,X23))&(v1_funct_1(esk5_4(X22,X23,X24,X25))|~r2_hidden(X25,X24)|X24!=k1_funct_2(X22,X23)))&(X25=esk5_4(X22,X23,X24,X25)|~r2_hidden(X25,X24)|X24!=k1_funct_2(X22,X23)))&(k1_relat_1(esk5_4(X22,X23,X24,X25))=X22|~r2_hidden(X25,X24)|X24!=k1_funct_2(X22,X23)))&(r1_tarski(k2_relat_1(esk5_4(X22,X23,X24,X25)),X23)|~r2_hidden(X25,X24)|X24!=k1_funct_2(X22,X23)))&(~v1_relat_1(X28)|~v1_funct_1(X28)|X27!=X28|k1_relat_1(X28)!=X22|~r1_tarski(k2_relat_1(X28),X23)|r2_hidden(X27,X24)|X24!=k1_funct_2(X22,X23)))&((~r2_hidden(esk6_3(X29,X30,X31),X31)|(~v1_relat_1(X33)|~v1_funct_1(X33)|esk6_3(X29,X30,X31)!=X33|k1_relat_1(X33)!=X29|~r1_tarski(k2_relat_1(X33),X30))|X31=k1_funct_2(X29,X30))&(((((v1_relat_1(esk7_3(X29,X30,X31))|r2_hidden(esk6_3(X29,X30,X31),X31)|X31=k1_funct_2(X29,X30))&(v1_funct_1(esk7_3(X29,X30,X31))|r2_hidden(esk6_3(X29,X30,X31),X31)|X31=k1_funct_2(X29,X30)))&(esk6_3(X29,X30,X31)=esk7_3(X29,X30,X31)|r2_hidden(esk6_3(X29,X30,X31),X31)|X31=k1_funct_2(X29,X30)))&(k1_relat_1(esk7_3(X29,X30,X31))=X29|r2_hidden(esk6_3(X29,X30,X31),X31)|X31=k1_funct_2(X29,X30)))&(r1_tarski(k2_relat_1(esk7_3(X29,X30,X31)),X30)|r2_hidden(esk6_3(X29,X30,X31),X31)|X31=k1_funct_2(X29,X30))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).
% 0.19/0.38  fof(c_0_6, plain, ![X12, X13, X14, X16, X17, X18, X20]:((((r2_hidden(esk2_3(X12,X13,X14),k1_relat_1(X12))|~r2_hidden(X14,X13)|X13!=k2_relat_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12)))&(X14=k1_funct_1(X12,esk2_3(X12,X13,X14))|~r2_hidden(X14,X13)|X13!=k2_relat_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12))))&(~r2_hidden(X17,k1_relat_1(X12))|X16!=k1_funct_1(X12,X17)|r2_hidden(X16,X13)|X13!=k2_relat_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12))))&((~r2_hidden(esk3_2(X12,X18),X18)|(~r2_hidden(X20,k1_relat_1(X12))|esk3_2(X12,X18)!=k1_funct_1(X12,X20))|X18=k2_relat_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12)))&((r2_hidden(esk4_2(X12,X18),k1_relat_1(X12))|r2_hidden(esk3_2(X12,X18),X18)|X18=k2_relat_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12)))&(esk3_2(X12,X18)=k1_funct_1(X12,esk4_2(X12,X18))|r2_hidden(esk3_2(X12,X18),X18)|X18=k2_relat_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.19/0.38  cnf(c_0_7, plain, (k1_relat_1(esk5_4(X1,X2,X3,X4))=X1|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.38  cnf(c_0_8, plain, (X1=esk5_4(X2,X3,X4,X1)|~r2_hidden(X1,X4)|X4!=k1_funct_2(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.38  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3]:(r2_hidden(X3,k1_funct_2(X1,X2))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t121_funct_2])).
% 0.19/0.38  cnf(c_0_10, plain, (v1_funct_1(esk5_4(X1,X2,X3,X4))|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.38  cnf(c_0_11, plain, (v1_relat_1(esk5_4(X1,X2,X3,X4))|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.38  fof(c_0_12, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.38  cnf(c_0_13, plain, (r2_hidden(X3,X4)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|X4!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.38  cnf(c_0_14, plain, (k1_relat_1(esk5_4(X1,X2,k1_funct_2(X1,X2),X3))=X1|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_7])).
% 0.19/0.38  cnf(c_0_15, plain, (esk5_4(X1,X2,k1_funct_2(X1,X2),X3)=X3|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_8])).
% 0.19/0.38  fof(c_0_16, negated_conjecture, (r2_hidden(esk11_0,k1_funct_2(esk9_0,esk10_0))&(~v1_funct_1(esk11_0)|~v1_funct_2(esk11_0,esk9_0,esk10_0)|~m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.19/0.38  cnf(c_0_17, plain, (v1_funct_1(esk5_4(X1,X2,k1_funct_2(X1,X2),X3))|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_10])).
% 0.19/0.38  cnf(c_0_18, plain, (v1_relat_1(esk5_4(X1,X2,k1_funct_2(X1,X2),X3))|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_19, plain, (r1_tarski(k2_relat_1(esk5_4(X1,X2,X3,X4)),X2)|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.38  fof(c_0_20, plain, ![X35, X36, X37]:((((v1_funct_1(X37)|(r2_hidden(esk8_3(X35,X36,X37),X35)|k1_relat_1(X37)!=X35)|(~v1_relat_1(X37)|~v1_funct_1(X37)))&(v1_funct_2(X37,X35,X36)|(r2_hidden(esk8_3(X35,X36,X37),X35)|k1_relat_1(X37)!=X35)|(~v1_relat_1(X37)|~v1_funct_1(X37))))&(m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|(r2_hidden(esk8_3(X35,X36,X37),X35)|k1_relat_1(X37)!=X35)|(~v1_relat_1(X37)|~v1_funct_1(X37))))&(((v1_funct_1(X37)|(~r2_hidden(k1_funct_1(X37,esk8_3(X35,X36,X37)),X36)|k1_relat_1(X37)!=X35)|(~v1_relat_1(X37)|~v1_funct_1(X37)))&(v1_funct_2(X37,X35,X36)|(~r2_hidden(k1_funct_1(X37,esk8_3(X35,X36,X37)),X36)|k1_relat_1(X37)!=X35)|(~v1_relat_1(X37)|~v1_funct_1(X37))))&(m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|(~r2_hidden(k1_funct_1(X37,esk8_3(X35,X36,X37)),X36)|k1_relat_1(X37)!=X35)|(~v1_relat_1(X37)|~v1_funct_1(X37))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_funct_2])])])])).
% 0.19/0.38  cnf(c_0_21, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_22, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_13])])).
% 0.19/0.38  cnf(c_0_23, plain, (k1_relat_1(X1)=X2|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.38  cnf(c_0_24, negated_conjecture, (r2_hidden(esk11_0,k1_funct_2(esk9_0,esk10_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_25, plain, (v1_funct_1(X1)|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(spm,[status(thm)],[c_0_17, c_0_15])).
% 0.19/0.38  cnf(c_0_26, plain, (v1_relat_1(X1)|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(spm,[status(thm)],[c_0_18, c_0_15])).
% 0.19/0.38  cnf(c_0_27, plain, (r1_tarski(k2_relat_1(esk5_4(X1,X2,k1_funct_2(X1,X2),X3)),X2)|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_19])).
% 0.19/0.38  cnf(c_0_28, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|r2_hidden(esk8_3(X2,X3,X1),X2)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.38  cnf(c_0_29, plain, (v1_funct_2(X1,X2,X3)|r2_hidden(esk8_3(X2,X3,X1),X2)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.38  cnf(c_0_30, plain, (r2_hidden(k1_funct_1(X1,X2),X3)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~r1_tarski(k2_relat_1(X1),X3)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.38  cnf(c_0_31, negated_conjecture, (k1_relat_1(esk11_0)=esk9_0), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.38  cnf(c_0_32, negated_conjecture, (v1_funct_1(esk11_0)), inference(spm,[status(thm)],[c_0_25, c_0_24])).
% 0.19/0.38  cnf(c_0_33, negated_conjecture, (v1_relat_1(esk11_0)), inference(spm,[status(thm)],[c_0_26, c_0_24])).
% 0.19/0.38  cnf(c_0_34, plain, (r1_tarski(k2_relat_1(X1),X2)|~r2_hidden(X1,k1_funct_2(X3,X2))), inference(spm,[status(thm)],[c_0_27, c_0_15])).
% 0.19/0.38  cnf(c_0_35, negated_conjecture, (~v1_funct_1(esk11_0)|~v1_funct_2(esk11_0,esk9_0,esk10_0)|~m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_36, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))|r2_hidden(esk8_3(k1_relat_1(X1),X2,X1),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_28])).
% 0.19/0.38  cnf(c_0_37, plain, (v1_funct_2(X1,k1_relat_1(X1),X2)|r2_hidden(esk8_3(k1_relat_1(X1),X2,X1),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_29])).
% 0.19/0.38  cnf(c_0_38, plain, (v1_funct_2(X1,X2,X3)|~r2_hidden(k1_funct_1(X1,esk8_3(X2,X3,X1)),X3)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.38  cnf(c_0_39, negated_conjecture, (r2_hidden(k1_funct_1(esk11_0,X1),X2)|~r2_hidden(X1,esk9_0)|~r1_tarski(k2_relat_1(esk11_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33])])).
% 0.19/0.38  cnf(c_0_40, negated_conjecture, (r1_tarski(k2_relat_1(esk11_0),esk10_0)), inference(spm,[status(thm)],[c_0_34, c_0_24])).
% 0.19/0.38  cnf(c_0_41, negated_conjecture, (~m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0)))|~v1_funct_2(esk11_0,esk9_0,esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_32])])).
% 0.19/0.38  cnf(c_0_42, negated_conjecture, (m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,X1)))|r2_hidden(esk8_3(esk9_0,X1,esk11_0),esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_32]), c_0_31]), c_0_31]), c_0_31]), c_0_33])])).
% 0.19/0.38  cnf(c_0_43, negated_conjecture, (v1_funct_2(esk11_0,esk9_0,X1)|r2_hidden(esk8_3(esk9_0,X1,esk11_0),esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_32]), c_0_31]), c_0_31]), c_0_31]), c_0_33])])).
% 0.19/0.38  cnf(c_0_44, plain, (v1_funct_2(X1,k1_relat_1(X1),X2)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(k1_funct_1(X1,esk8_3(k1_relat_1(X1),X2,X1)),X2)), inference(er,[status(thm)],[c_0_38])).
% 0.19/0.38  cnf(c_0_45, negated_conjecture, (r2_hidden(k1_funct_1(esk11_0,X1),esk10_0)|~r2_hidden(X1,esk9_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.38  cnf(c_0_46, negated_conjecture, (r2_hidden(esk8_3(esk9_0,esk10_0,esk11_0),esk9_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])).
% 0.19/0.38  cnf(c_0_47, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(k1_funct_1(X1,esk8_3(X2,X3,X1)),X3)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.38  cnf(c_0_48, negated_conjecture, (v1_funct_2(esk11_0,esk9_0,esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_31]), c_0_32]), c_0_33]), c_0_31]), c_0_46])])).
% 0.19/0.38  cnf(c_0_49, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(k1_funct_1(X1,esk8_3(k1_relat_1(X1),X2,X1)),X2)), inference(er,[status(thm)],[c_0_47])).
% 0.19/0.38  cnf(c_0_50, negated_conjecture, (~m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_48])])).
% 0.19/0.38  cnf(c_0_51, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_45]), c_0_31]), c_0_32]), c_0_33]), c_0_31]), c_0_46])]), c_0_50]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 52
% 0.19/0.38  # Proof object clause steps            : 41
% 0.19/0.38  # Proof object formula steps           : 11
% 0.19/0.38  # Proof object conjectures             : 18
% 0.19/0.38  # Proof object clause conjectures      : 15
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 13
% 0.19/0.38  # Proof object initial formulas used   : 5
% 0.19/0.38  # Proof object generating inferences   : 16
% 0.19/0.38  # Proof object simplifying inferences  : 42
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 5
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 29
% 0.19/0.38  # Removed in clause preprocessing      : 2
% 0.19/0.38  # Initial clauses in saturation        : 27
% 0.19/0.38  # Processed clauses                    : 101
% 0.19/0.38  # ...of these trivial                  : 1
% 0.19/0.38  # ...subsumed                          : 1
% 0.19/0.38  # ...remaining for further processing  : 98
% 0.19/0.38  # Other redundant clauses eliminated   : 17
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 0
% 0.19/0.38  # Backward-rewritten                   : 3
% 0.19/0.38  # Generated clauses                    : 129
% 0.19/0.38  # ...of the previous two non-trivial   : 125
% 0.19/0.38  # Contextual simplify-reflections      : 3
% 0.19/0.38  # Paramodulations                      : 115
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 17
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 54
% 0.19/0.38  #    Positive orientable unit clauses  : 10
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 1
% 0.19/0.38  #    Non-unit-clauses                  : 43
% 0.19/0.38  # Current number of unprocessed clauses: 78
% 0.19/0.38  # ...number of literals in the above   : 298
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 30
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 185
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 101
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 4
% 0.19/0.38  # Unit Clause-clause subsumption calls : 21
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 12
% 0.19/0.38  # BW rewrite match successes           : 3
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 4661
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.033 s
% 0.19/0.38  # System time              : 0.005 s
% 0.19/0.38  # Total time               : 0.039 s
% 0.19/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
