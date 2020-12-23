%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:01:32 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 341 expanded)
%              Number of clauses        :   41 ( 131 expanded)
%              Number of leaves         :   13 (  83 expanded)
%              Depth                    :   13
%              Number of atoms          :  277 (1746 expanded)
%              Number of equality atoms :   78 ( 474 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   44 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t16_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ! [X4] :
            ~ ( r2_hidden(X4,X2)
              & ! [X5] :
                  ~ ( r2_hidden(X5,X1)
                    & X4 = k1_funct_1(X3,X5) ) )
       => k2_relset_1(X1,X2,X3) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).

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

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(d1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
         => ( v1_funct_2(X3,X1,X2)
          <=> X1 = k1_relset_1(X1,X2,X3) ) )
        & ( X2 = k1_xboole_0
         => ( X1 = k1_xboole_0
            | ( v1_funct_2(X3,X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t23_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ! [X4] :
            ~ ( r2_hidden(X4,X2)
              & ! [X5] : ~ r2_hidden(k4_tarski(X5,X4),X3) )
      <=> k2_relset_1(X1,X2,X3) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relset_1)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( ! [X4] :
              ~ ( r2_hidden(X4,X2)
                & ! [X5] :
                    ~ ( r2_hidden(X5,X1)
                      & X4 = k1_funct_1(X3,X5) ) )
         => k2_relset_1(X1,X2,X3) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t16_funct_2])).

fof(c_0_14,plain,(
    ! [X20,X21,X22,X23,X25,X26,X27,X28,X30] :
      ( ( r2_hidden(esk2_4(X20,X21,X22,X23),k1_relat_1(X20))
        | ~ r2_hidden(X23,X22)
        | X22 != k9_relat_1(X20,X21)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) )
      & ( r2_hidden(esk2_4(X20,X21,X22,X23),X21)
        | ~ r2_hidden(X23,X22)
        | X22 != k9_relat_1(X20,X21)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) )
      & ( X23 = k1_funct_1(X20,esk2_4(X20,X21,X22,X23))
        | ~ r2_hidden(X23,X22)
        | X22 != k9_relat_1(X20,X21)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) )
      & ( ~ r2_hidden(X26,k1_relat_1(X20))
        | ~ r2_hidden(X26,X21)
        | X25 != k1_funct_1(X20,X26)
        | r2_hidden(X25,X22)
        | X22 != k9_relat_1(X20,X21)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) )
      & ( ~ r2_hidden(esk3_3(X20,X27,X28),X28)
        | ~ r2_hidden(X30,k1_relat_1(X20))
        | ~ r2_hidden(X30,X27)
        | esk3_3(X20,X27,X28) != k1_funct_1(X20,X30)
        | X28 = k9_relat_1(X20,X27)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) )
      & ( r2_hidden(esk4_3(X20,X27,X28),k1_relat_1(X20))
        | r2_hidden(esk3_3(X20,X27,X28),X28)
        | X28 = k9_relat_1(X20,X27)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) )
      & ( r2_hidden(esk4_3(X20,X27,X28),X27)
        | r2_hidden(esk3_3(X20,X27,X28),X28)
        | X28 = k9_relat_1(X20,X27)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) )
      & ( esk3_3(X20,X27,X28) = k1_funct_1(X20,esk4_3(X20,X27,X28))
        | r2_hidden(esk3_3(X20,X27,X28),X28)
        | X28 = k9_relat_1(X20,X27)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).

fof(c_0_15,plain,(
    ! [X9,X10] :
      ( ~ v1_relat_1(X9)
      | ~ m1_subset_1(X10,k1_zfmisc_1(X9))
      | v1_relat_1(X10) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_16,negated_conjecture,(
    ! [X54] :
      ( v1_funct_1(esk9_0)
      & v1_funct_2(esk9_0,esk7_0,esk8_0)
      & m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0)))
      & ( r2_hidden(esk10_1(X54),esk7_0)
        | ~ r2_hidden(X54,esk8_0) )
      & ( X54 = k1_funct_1(esk9_0,esk10_1(X54))
        | ~ r2_hidden(X54,esk8_0) )
      & k2_relset_1(esk7_0,esk8_0,esk9_0) != esk8_0 ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])])).

fof(c_0_17,plain,(
    ! [X13,X14] : v1_relat_1(k2_zfmisc_1(X13,X14)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_18,plain,(
    ! [X48,X49,X50] :
      ( ( ~ v1_funct_2(X50,X48,X49)
        | X48 = k1_relset_1(X48,X49,X50)
        | X49 = k1_xboole_0
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))) )
      & ( X48 != k1_relset_1(X48,X49,X50)
        | v1_funct_2(X50,X48,X49)
        | X49 = k1_xboole_0
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))) )
      & ( ~ v1_funct_2(X50,X48,X49)
        | X48 = k1_relset_1(X48,X49,X50)
        | X48 != k1_xboole_0
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))) )
      & ( X48 != k1_relset_1(X48,X49,X50)
        | v1_funct_2(X50,X48,X49)
        | X48 != k1_xboole_0
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))) )
      & ( ~ v1_funct_2(X50,X48,X49)
        | X50 = k1_xboole_0
        | X48 = k1_xboole_0
        | X49 != k1_xboole_0
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))) )
      & ( X50 != k1_xboole_0
        | v1_funct_2(X50,X48,X49)
        | X48 = k1_xboole_0
        | X49 != k1_xboole_0
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_19,plain,
    ( r2_hidden(X4,X5)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,X3)
    | X4 != k1_funct_1(X2,X1)
    | X5 != k9_relat_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,plain,(
    ! [X35,X36,X37] :
      ( ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
      | k1_relset_1(X35,X36,X37) = k1_relat_1(X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_24,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_2(esk9_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r2_hidden(X2,X3)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_19])])).

cnf(c_0_27,negated_conjecture,
    ( X1 = k1_funct_1(esk9_0,esk10_1(X1))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( v1_funct_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_29,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

cnf(c_0_30,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( k1_relset_1(esk7_0,esk8_0,esk9_0) = esk7_0
    | esk8_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_21]),c_0_25])])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(X1,k9_relat_1(esk9_0,X2))
    | ~ r2_hidden(esk10_1(X1),k1_relat_1(esk9_0))
    | ~ r2_hidden(esk10_1(X1),X2)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])])).

cnf(c_0_33,negated_conjecture,
    ( k1_relat_1(esk9_0) = esk7_0
    | esk8_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_21])])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk10_1(X1),esk7_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_35,plain,(
    ! [X41,X42,X43,X45,X46] :
      ( ( r2_hidden(esk5_3(X41,X42,X43),X42)
        | k2_relset_1(X41,X42,X43) = X42
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) )
      & ( ~ r2_hidden(k4_tarski(X45,esk5_3(X41,X42,X43)),X43)
        | k2_relset_1(X41,X42,X43) = X42
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) )
      & ( k2_relset_1(X41,X42,X43) != X42
        | ~ r2_hidden(X46,X42)
        | r2_hidden(k4_tarski(esk6_4(X41,X42,X43,X46),X46),X43)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_relset_1])])])])])])).

fof(c_0_36,plain,(
    ! [X15,X16,X17,X19] :
      ( ( r2_hidden(esk1_3(X15,X16,X17),k1_relat_1(X17))
        | ~ r2_hidden(X15,k9_relat_1(X17,X16))
        | ~ v1_relat_1(X17) )
      & ( r2_hidden(k4_tarski(esk1_3(X15,X16,X17),X15),X17)
        | ~ r2_hidden(X15,k9_relat_1(X17,X16))
        | ~ v1_relat_1(X17) )
      & ( r2_hidden(esk1_3(X15,X16,X17),X16)
        | ~ r2_hidden(X15,k9_relat_1(X17,X16))
        | ~ v1_relat_1(X17) )
      & ( ~ r2_hidden(X19,k1_relat_1(X17))
        | ~ r2_hidden(k4_tarski(X19,X15),X17)
        | ~ r2_hidden(X19,X16)
        | r2_hidden(X15,k9_relat_1(X17,X16))
        | ~ v1_relat_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

cnf(c_0_37,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | r2_hidden(X1,k9_relat_1(esk9_0,X2))
    | ~ r2_hidden(esk10_1(X1),X2)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

cnf(c_0_38,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X2)
    | k2_relset_1(X1,X2,X3) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( k2_relset_1(esk7_0,esk8_0,esk9_0) != esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_40,plain,(
    ! [X38,X39,X40] :
      ( ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
      | k2_relset_1(X38,X39,X40) = k2_relat_1(X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_41,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_42,plain,(
    ! [X8] : r1_tarski(k1_xboole_0,X8) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_43,plain,(
    ! [X32,X33,X34] :
      ( ( v4_relat_1(X34,X32)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( v5_relat_1(X34,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_44,plain,
    ( k2_relset_1(X2,X3,X4) = X3
    | ~ r2_hidden(k4_tarski(X1,esk5_3(X2,X3,X4)),X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,plain,
    ( r2_hidden(k4_tarski(esk1_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | r2_hidden(X1,k9_relat_1(esk9_0,esk7_0))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_34])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk5_3(esk7_0,esk8_0,esk9_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_21]),c_0_39])).

cnf(c_0_48,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_50,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_51,plain,(
    ! [X11,X12] :
      ( ( ~ v5_relat_1(X12,X11)
        | r1_tarski(k2_relat_1(X12),X11)
        | ~ v1_relat_1(X12) )
      & ( ~ r1_tarski(k2_relat_1(X12),X11)
        | v5_relat_1(X12,X11)
        | ~ v1_relat_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_52,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,plain,
    ( k2_relset_1(X1,X2,X3) = X2
    | ~ r2_hidden(esk5_3(X1,X2,X3),k9_relat_1(X3,X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | r2_hidden(esk5_3(esk7_0,esk8_0,esk9_0),k9_relat_1(esk9_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_55,plain,
    ( k2_relset_1(X1,X2,X3) = k2_relset_1(X4,X5,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_48])).

cnf(c_0_56,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_57,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( v5_relat_1(esk9_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_21])).

cnf(c_0_59,negated_conjecture,
    ( esk8_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_21]),c_0_29])]),c_0_39])).

cnf(c_0_60,negated_conjecture,
    ( k2_relset_1(X1,X2,esk9_0) != esk8_0
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_55]),c_0_21])])).

cnf(c_0_61,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | ~ v5_relat_1(X1,k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( v5_relat_1(esk9_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( k2_relat_1(esk9_0) != esk8_0
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_48])).

cnf(c_0_64,negated_conjecture,
    ( k2_relat_1(esk9_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_29])])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[c_0_21,c_0_59])).

cnf(c_0_66,negated_conjecture,
    ( ~ m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_59]),c_0_64])])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_65,c_0_66]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:40:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.029 s
% 0.12/0.38  # Presaturation interreduction done
% 0.12/0.38  
% 0.12/0.38  # Proof found!
% 0.12/0.38  # SZS status Theorem
% 0.12/0.38  # SZS output start CNFRefutation
% 0.12/0.38  fof(t16_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(![X4]:~((r2_hidden(X4,X2)&![X5]:~((r2_hidden(X5,X1)&X4=k1_funct_1(X3,X5)))))=>k2_relset_1(X1,X2,X3)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_2)).
% 0.12/0.38  fof(d12_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(X3=k9_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:((r2_hidden(X5,k1_relat_1(X1))&r2_hidden(X5,X2))&X4=k1_funct_1(X1,X5))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_1)).
% 0.12/0.38  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.12/0.38  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.12/0.38  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.12/0.38  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.12/0.38  fof(t23_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(![X4]:~((r2_hidden(X4,X2)&![X5]:~(r2_hidden(k4_tarski(X5,X4),X3))))<=>k2_relset_1(X1,X2,X3)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_relset_1)).
% 0.12/0.38  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 0.12/0.38  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.12/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.12/0.38  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.12/0.38  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.12/0.38  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 0.12/0.38  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(![X4]:~((r2_hidden(X4,X2)&![X5]:~((r2_hidden(X5,X1)&X4=k1_funct_1(X3,X5)))))=>k2_relset_1(X1,X2,X3)=X2))), inference(assume_negation,[status(cth)],[t16_funct_2])).
% 0.12/0.38  fof(c_0_14, plain, ![X20, X21, X22, X23, X25, X26, X27, X28, X30]:(((((r2_hidden(esk2_4(X20,X21,X22,X23),k1_relat_1(X20))|~r2_hidden(X23,X22)|X22!=k9_relat_1(X20,X21)|(~v1_relat_1(X20)|~v1_funct_1(X20)))&(r2_hidden(esk2_4(X20,X21,X22,X23),X21)|~r2_hidden(X23,X22)|X22!=k9_relat_1(X20,X21)|(~v1_relat_1(X20)|~v1_funct_1(X20))))&(X23=k1_funct_1(X20,esk2_4(X20,X21,X22,X23))|~r2_hidden(X23,X22)|X22!=k9_relat_1(X20,X21)|(~v1_relat_1(X20)|~v1_funct_1(X20))))&(~r2_hidden(X26,k1_relat_1(X20))|~r2_hidden(X26,X21)|X25!=k1_funct_1(X20,X26)|r2_hidden(X25,X22)|X22!=k9_relat_1(X20,X21)|(~v1_relat_1(X20)|~v1_funct_1(X20))))&((~r2_hidden(esk3_3(X20,X27,X28),X28)|(~r2_hidden(X30,k1_relat_1(X20))|~r2_hidden(X30,X27)|esk3_3(X20,X27,X28)!=k1_funct_1(X20,X30))|X28=k9_relat_1(X20,X27)|(~v1_relat_1(X20)|~v1_funct_1(X20)))&(((r2_hidden(esk4_3(X20,X27,X28),k1_relat_1(X20))|r2_hidden(esk3_3(X20,X27,X28),X28)|X28=k9_relat_1(X20,X27)|(~v1_relat_1(X20)|~v1_funct_1(X20)))&(r2_hidden(esk4_3(X20,X27,X28),X27)|r2_hidden(esk3_3(X20,X27,X28),X28)|X28=k9_relat_1(X20,X27)|(~v1_relat_1(X20)|~v1_funct_1(X20))))&(esk3_3(X20,X27,X28)=k1_funct_1(X20,esk4_3(X20,X27,X28))|r2_hidden(esk3_3(X20,X27,X28),X28)|X28=k9_relat_1(X20,X27)|(~v1_relat_1(X20)|~v1_funct_1(X20)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).
% 0.12/0.38  fof(c_0_15, plain, ![X9, X10]:(~v1_relat_1(X9)|(~m1_subset_1(X10,k1_zfmisc_1(X9))|v1_relat_1(X10))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.12/0.38  fof(c_0_16, negated_conjecture, ![X54]:(((v1_funct_1(esk9_0)&v1_funct_2(esk9_0,esk7_0,esk8_0))&m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0))))&(((r2_hidden(esk10_1(X54),esk7_0)|~r2_hidden(X54,esk8_0))&(X54=k1_funct_1(esk9_0,esk10_1(X54))|~r2_hidden(X54,esk8_0)))&k2_relset_1(esk7_0,esk8_0,esk9_0)!=esk8_0)), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])])).
% 0.12/0.38  fof(c_0_17, plain, ![X13, X14]:v1_relat_1(k2_zfmisc_1(X13,X14)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.12/0.38  fof(c_0_18, plain, ![X48, X49, X50]:((((~v1_funct_2(X50,X48,X49)|X48=k1_relset_1(X48,X49,X50)|X49=k1_xboole_0|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))))&(X48!=k1_relset_1(X48,X49,X50)|v1_funct_2(X50,X48,X49)|X49=k1_xboole_0|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))))&((~v1_funct_2(X50,X48,X49)|X48=k1_relset_1(X48,X49,X50)|X48!=k1_xboole_0|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))))&(X48!=k1_relset_1(X48,X49,X50)|v1_funct_2(X50,X48,X49)|X48!=k1_xboole_0|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))))))&((~v1_funct_2(X50,X48,X49)|X50=k1_xboole_0|X48=k1_xboole_0|X49!=k1_xboole_0|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))))&(X50!=k1_xboole_0|v1_funct_2(X50,X48,X49)|X48=k1_xboole_0|X49!=k1_xboole_0|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.12/0.38  cnf(c_0_19, plain, (r2_hidden(X4,X5)|~r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(X1,X3)|X4!=k1_funct_1(X2,X1)|X5!=k9_relat_1(X2,X3)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.38  cnf(c_0_20, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.38  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.38  cnf(c_0_22, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.38  fof(c_0_23, plain, ![X35, X36, X37]:(~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|k1_relset_1(X35,X36,X37)=k1_relat_1(X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.12/0.38  cnf(c_0_24, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.38  cnf(c_0_25, negated_conjecture, (v1_funct_2(esk9_0,esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.38  cnf(c_0_26, plain, (r2_hidden(k1_funct_1(X1,X2),k9_relat_1(X1,X3))|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~r2_hidden(X2,X3)|~v1_relat_1(X1)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_19])])).
% 0.12/0.38  cnf(c_0_27, negated_conjecture, (X1=k1_funct_1(esk9_0,esk10_1(X1))|~r2_hidden(X1,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.38  cnf(c_0_28, negated_conjecture, (v1_funct_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.38  cnf(c_0_29, negated_conjecture, (v1_relat_1(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])])).
% 0.12/0.38  cnf(c_0_30, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.38  cnf(c_0_31, negated_conjecture, (k1_relset_1(esk7_0,esk8_0,esk9_0)=esk7_0|esk8_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_21]), c_0_25])])).
% 0.12/0.38  cnf(c_0_32, negated_conjecture, (r2_hidden(X1,k9_relat_1(esk9_0,X2))|~r2_hidden(esk10_1(X1),k1_relat_1(esk9_0))|~r2_hidden(esk10_1(X1),X2)|~r2_hidden(X1,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29])])).
% 0.12/0.38  cnf(c_0_33, negated_conjecture, (k1_relat_1(esk9_0)=esk7_0|esk8_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_21])])).
% 0.12/0.38  cnf(c_0_34, negated_conjecture, (r2_hidden(esk10_1(X1),esk7_0)|~r2_hidden(X1,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.38  fof(c_0_35, plain, ![X41, X42, X43, X45, X46]:(((r2_hidden(esk5_3(X41,X42,X43),X42)|k2_relset_1(X41,X42,X43)=X42|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))))&(~r2_hidden(k4_tarski(X45,esk5_3(X41,X42,X43)),X43)|k2_relset_1(X41,X42,X43)=X42|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))))&(k2_relset_1(X41,X42,X43)!=X42|(~r2_hidden(X46,X42)|r2_hidden(k4_tarski(esk6_4(X41,X42,X43,X46),X46),X43))|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_relset_1])])])])])])).
% 0.12/0.38  fof(c_0_36, plain, ![X15, X16, X17, X19]:((((r2_hidden(esk1_3(X15,X16,X17),k1_relat_1(X17))|~r2_hidden(X15,k9_relat_1(X17,X16))|~v1_relat_1(X17))&(r2_hidden(k4_tarski(esk1_3(X15,X16,X17),X15),X17)|~r2_hidden(X15,k9_relat_1(X17,X16))|~v1_relat_1(X17)))&(r2_hidden(esk1_3(X15,X16,X17),X16)|~r2_hidden(X15,k9_relat_1(X17,X16))|~v1_relat_1(X17)))&(~r2_hidden(X19,k1_relat_1(X17))|~r2_hidden(k4_tarski(X19,X15),X17)|~r2_hidden(X19,X16)|r2_hidden(X15,k9_relat_1(X17,X16))|~v1_relat_1(X17))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 0.12/0.38  cnf(c_0_37, negated_conjecture, (esk8_0=k1_xboole_0|r2_hidden(X1,k9_relat_1(esk9_0,X2))|~r2_hidden(esk10_1(X1),X2)|~r2_hidden(X1,esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])).
% 0.12/0.38  cnf(c_0_38, plain, (r2_hidden(esk5_3(X1,X2,X3),X2)|k2_relset_1(X1,X2,X3)=X2|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.12/0.38  cnf(c_0_39, negated_conjecture, (k2_relset_1(esk7_0,esk8_0,esk9_0)!=esk8_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.38  fof(c_0_40, plain, ![X38, X39, X40]:(~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))|k2_relset_1(X38,X39,X40)=k2_relat_1(X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.12/0.38  fof(c_0_41, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.12/0.38  fof(c_0_42, plain, ![X8]:r1_tarski(k1_xboole_0,X8), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.12/0.38  fof(c_0_43, plain, ![X32, X33, X34]:((v4_relat_1(X34,X32)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))&(v5_relat_1(X34,X33)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.12/0.38  cnf(c_0_44, plain, (k2_relset_1(X2,X3,X4)=X3|~r2_hidden(k4_tarski(X1,esk5_3(X2,X3,X4)),X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.12/0.38  cnf(c_0_45, plain, (r2_hidden(k4_tarski(esk1_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.12/0.38  cnf(c_0_46, negated_conjecture, (esk8_0=k1_xboole_0|r2_hidden(X1,k9_relat_1(esk9_0,esk7_0))|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_37, c_0_34])).
% 0.12/0.38  cnf(c_0_47, negated_conjecture, (r2_hidden(esk5_3(esk7_0,esk8_0,esk9_0),esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_21]), c_0_39])).
% 0.12/0.38  cnf(c_0_48, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.12/0.38  cnf(c_0_49, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.12/0.38  cnf(c_0_50, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.12/0.38  fof(c_0_51, plain, ![X11, X12]:((~v5_relat_1(X12,X11)|r1_tarski(k2_relat_1(X12),X11)|~v1_relat_1(X12))&(~r1_tarski(k2_relat_1(X12),X11)|v5_relat_1(X12,X11)|~v1_relat_1(X12))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.12/0.38  cnf(c_0_52, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.12/0.38  cnf(c_0_53, plain, (k2_relset_1(X1,X2,X3)=X2|~r2_hidden(esk5_3(X1,X2,X3),k9_relat_1(X3,X4))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_relat_1(X3)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.12/0.38  cnf(c_0_54, negated_conjecture, (esk8_0=k1_xboole_0|r2_hidden(esk5_3(esk7_0,esk8_0,esk9_0),k9_relat_1(esk9_0,esk7_0))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.12/0.38  cnf(c_0_55, plain, (k2_relset_1(X1,X2,X3)=k2_relset_1(X4,X5,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))), inference(spm,[status(thm)],[c_0_48, c_0_48])).
% 0.12/0.38  cnf(c_0_56, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.12/0.38  cnf(c_0_57, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.12/0.38  cnf(c_0_58, negated_conjecture, (v5_relat_1(esk9_0,esk8_0)), inference(spm,[status(thm)],[c_0_52, c_0_21])).
% 0.12/0.38  cnf(c_0_59, negated_conjecture, (esk8_0=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_21]), c_0_29])]), c_0_39])).
% 0.12/0.38  cnf(c_0_60, negated_conjecture, (k2_relset_1(X1,X2,esk9_0)!=esk8_0|~m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_55]), c_0_21])])).
% 0.12/0.38  cnf(c_0_61, plain, (k2_relat_1(X1)=k1_xboole_0|~v5_relat_1(X1,k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.12/0.38  cnf(c_0_62, negated_conjecture, (v5_relat_1(esk9_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_58, c_0_59])).
% 0.12/0.38  cnf(c_0_63, negated_conjecture, (k2_relat_1(esk9_0)!=esk8_0|~m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_60, c_0_48])).
% 0.12/0.38  cnf(c_0_64, negated_conjecture, (k2_relat_1(esk9_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_29])])).
% 0.12/0.38  cnf(c_0_65, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,k1_xboole_0)))), inference(rw,[status(thm)],[c_0_21, c_0_59])).
% 0.12/0.38  cnf(c_0_66, negated_conjecture, (~m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_59]), c_0_64])])).
% 0.12/0.38  cnf(c_0_67, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_65, c_0_66]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 68
% 0.12/0.38  # Proof object clause steps            : 41
% 0.12/0.38  # Proof object formula steps           : 27
% 0.12/0.38  # Proof object conjectures             : 26
% 0.12/0.38  # Proof object clause conjectures      : 23
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 19
% 0.12/0.38  # Proof object initial formulas used   : 13
% 0.12/0.38  # Proof object generating inferences   : 17
% 0.12/0.38  # Proof object simplifying inferences  : 27
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 13
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 39
% 0.12/0.38  # Removed in clause preprocessing      : 0
% 0.12/0.38  # Initial clauses in saturation        : 39
% 0.12/0.38  # Processed clauses                    : 158
% 0.12/0.38  # ...of these trivial                  : 0
% 0.12/0.38  # ...subsumed                          : 18
% 0.12/0.38  # ...remaining for further processing  : 140
% 0.12/0.38  # Other redundant clauses eliminated   : 12
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 1
% 0.12/0.38  # Backward-rewritten                   : 35
% 0.12/0.38  # Generated clauses                    : 163
% 0.12/0.38  # ...of the previous two non-trivial   : 161
% 0.12/0.38  # Contextual simplify-reflections      : 4
% 0.12/0.38  # Paramodulations                      : 152
% 0.12/0.38  # Factorizations                       : 0
% 0.12/0.38  # Equation resolutions                 : 12
% 0.12/0.38  # Propositional unsat checks           : 0
% 0.12/0.38  #    Propositional check models        : 0
% 0.12/0.38  #    Propositional check unsatisfiable : 0
% 0.12/0.38  #    Propositional clauses             : 0
% 0.12/0.38  #    Propositional clauses after purity: 0
% 0.12/0.38  #    Propositional unsat core size     : 0
% 0.12/0.38  #    Propositional preprocessing time  : 0.000
% 0.12/0.38  #    Propositional encoding time       : 0.000
% 0.12/0.38  #    Propositional solver time         : 0.000
% 0.12/0.38  #    Success case prop preproc time    : 0.000
% 0.12/0.38  #    Success case prop encoding time   : 0.000
% 0.12/0.38  #    Success case prop solver time     : 0.000
% 0.12/0.38  # Current number of processed clauses  : 55
% 0.12/0.38  #    Positive orientable unit clauses  : 10
% 0.12/0.38  #    Positive unorientable unit clauses: 0
% 0.12/0.38  #    Negative unit clauses             : 2
% 0.12/0.38  #    Non-unit-clauses                  : 43
% 0.12/0.38  # Current number of unprocessed clauses: 80
% 0.12/0.38  # ...number of literals in the above   : 327
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 75
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 1037
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 602
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 23
% 0.12/0.38  # Unit Clause-clause subsumption calls : 45
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 3
% 0.12/0.38  # BW rewrite match successes           : 2
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 6700
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.038 s
% 0.12/0.38  # System time              : 0.006 s
% 0.12/0.38  # Total time               : 0.044 s
% 0.12/0.38  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
