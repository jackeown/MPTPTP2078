%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:05:51 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 452 expanded)
%              Number of clauses        :   38 ( 169 expanded)
%              Number of leaves         :   10 ( 110 expanded)
%              Depth                    :   16
%              Number of atoms          :  213 (2952 expanded)
%              Number of equality atoms :   44 ( 706 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   23 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t77_funct_2,conjecture,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => ( v2_funct_1(X2)
      <=> ! [X3,X4] :
            ( ( r2_hidden(X3,X1)
              & r2_hidden(X4,X1)
              & k1_funct_1(X2,X3) = k1_funct_1(X2,X4) )
           => X3 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_funct_2)).

fof(t32_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( v2_funct_1(X4)
          & r2_hidden(X3,X1) )
       => ( X2 = k1_xboole_0
          | k1_funct_1(k2_funct_1(X4),k1_funct_1(X4,X3)) = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(d8_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( r2_hidden(X2,k1_relat_1(X1))
              & r2_hidden(X3,k1_relat_1(X1))
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_funct_2(X2,X1,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
       => ( v2_funct_1(X2)
        <=> ! [X3,X4] :
              ( ( r2_hidden(X3,X1)
                & r2_hidden(X4,X1)
                & k1_funct_1(X2,X3) = k1_funct_1(X2,X4) )
             => X3 = X4 ) ) ) ),
    inference(assume_negation,[status(cth)],[t77_funct_2])).

fof(c_0_11,plain,(
    ! [X29,X30,X31,X32] :
      ( ~ v1_funct_1(X32)
      | ~ v1_funct_2(X32,X29,X30)
      | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
      | ~ v2_funct_1(X32)
      | ~ r2_hidden(X31,X29)
      | X30 = k1_xboole_0
      | k1_funct_1(k2_funct_1(X32),k1_funct_1(X32,X31)) = X31 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_funct_2])])).

fof(c_0_12,negated_conjecture,(
    ! [X37,X38] :
      ( v1_funct_1(esk6_0)
      & v1_funct_2(esk6_0,esk5_0,esk5_0)
      & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk5_0)))
      & ( r2_hidden(esk7_0,esk5_0)
        | ~ v2_funct_1(esk6_0) )
      & ( r2_hidden(esk8_0,esk5_0)
        | ~ v2_funct_1(esk6_0) )
      & ( k1_funct_1(esk6_0,esk7_0) = k1_funct_1(esk6_0,esk8_0)
        | ~ v2_funct_1(esk6_0) )
      & ( esk7_0 != esk8_0
        | ~ v2_funct_1(esk6_0) )
      & ( v2_funct_1(esk6_0)
        | ~ r2_hidden(X37,esk5_0)
        | ~ r2_hidden(X38,esk5_0)
        | k1_funct_1(esk6_0,X37) != k1_funct_1(esk6_0,X38)
        | X37 = X38 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])])).

cnf(c_0_13,plain,
    ( X3 = k1_xboole_0
    | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X4)) = X4
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v2_funct_1(X1)
    | ~ r2_hidden(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( v1_funct_2(esk6_0,esk5_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( k1_funct_1(k2_funct_1(esk6_0),k1_funct_1(esk6_0,X1)) = X1
    | esk5_0 = k1_xboole_0
    | ~ v2_funct_1(esk6_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16])])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk8_0,esk5_0)
    | ~ v2_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_19,plain,(
    ! [X26,X27,X28] :
      ( ( v4_relat_1(X28,X26)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( v5_relat_1(X28,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_20,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X15)
      | ~ m1_subset_1(X16,k1_zfmisc_1(X15))
      | v1_relat_1(X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_21,plain,(
    ! [X19,X20] : v1_relat_1(k2_zfmisc_1(X19,X20)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_22,negated_conjecture,
    ( k1_funct_1(k2_funct_1(esk6_0),k1_funct_1(esk6_0,esk8_0)) = esk8_0
    | esk5_0 = k1_xboole_0
    | ~ v2_funct_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( k1_funct_1(esk6_0,esk7_0) = k1_funct_1(esk6_0,esk8_0)
    | ~ v2_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_24,plain,(
    ! [X17,X18] :
      ( ( ~ v4_relat_1(X18,X17)
        | r1_tarski(k1_relat_1(X18),X17)
        | ~ v1_relat_1(X18) )
      & ( ~ r1_tarski(k1_relat_1(X18),X17)
        | v4_relat_1(X18,X17)
        | ~ v1_relat_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_25,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_28,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_29,negated_conjecture,
    ( esk7_0 != esk8_0
    | ~ v2_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_30,negated_conjecture,
    ( esk8_0 = k1_funct_1(k2_funct_1(esk6_0),k1_funct_1(esk6_0,esk7_0))
    | esk5_0 = k1_xboole_0
    | ~ v2_funct_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_31,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk2_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_32,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( v4_relat_1(esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_16])).

cnf(c_0_34,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_16]),c_0_27])])).

cnf(c_0_35,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk7_0,esk5_0)
    | ~ v2_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_37,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | k1_funct_1(k2_funct_1(esk6_0),k1_funct_1(esk6_0,esk7_0)) != esk7_0
    | ~ v2_funct_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_38,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk6_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])])).

cnf(c_0_40,negated_conjecture,
    ( ~ v2_funct_1(esk6_0)
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_18])).

cnf(c_0_41,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | ~ v2_funct_1(esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_36]),c_0_37])).

cnf(c_0_42,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_43,negated_conjecture,
    ( v2_funct_1(esk6_0)
    | X1 = X2
    | ~ r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X2,esk5_0)
    | k1_funct_1(esk6_0,X1) != k1_funct_1(esk6_0,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,k1_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( ~ v2_funct_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])])).

cnf(c_0_46,negated_conjecture,
    ( X1 = X2
    | k1_funct_1(esk6_0,X1) != k1_funct_1(esk6_0,X2)
    | ~ r2_hidden(X2,k1_relat_1(esk6_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])).

fof(c_0_47,plain,(
    ! [X21,X22,X23] :
      ( ( ~ v2_funct_1(X21)
        | ~ r2_hidden(X22,k1_relat_1(X21))
        | ~ r2_hidden(X23,k1_relat_1(X21))
        | k1_funct_1(X21,X22) != k1_funct_1(X21,X23)
        | X22 = X23
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( r2_hidden(esk3_1(X21),k1_relat_1(X21))
        | v2_funct_1(X21)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( r2_hidden(esk4_1(X21),k1_relat_1(X21))
        | v2_funct_1(X21)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( k1_funct_1(X21,esk3_1(X21)) = k1_funct_1(X21,esk4_1(X21))
        | v2_funct_1(X21)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( esk3_1(X21) != esk4_1(X21)
        | v2_funct_1(X21)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).

cnf(c_0_48,negated_conjecture,
    ( X1 = X2
    | k1_funct_1(esk6_0,X1) != k1_funct_1(esk6_0,X2)
    | ~ r2_hidden(X2,k1_relat_1(esk6_0))
    | ~ r2_hidden(X1,k1_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_44])).

cnf(c_0_49,plain,
    ( k1_funct_1(X1,esk3_1(X1)) = k1_funct_1(X1,esk4_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( X1 = esk4_1(esk6_0)
    | k1_funct_1(esk6_0,X1) != k1_funct_1(esk6_0,esk3_1(esk6_0))
    | ~ r2_hidden(esk4_1(esk6_0),k1_relat_1(esk6_0))
    | ~ r2_hidden(X1,k1_relat_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_15]),c_0_34])]),c_0_45])).

cnf(c_0_51,plain,
    ( r2_hidden(esk4_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( X1 = esk4_1(esk6_0)
    | k1_funct_1(esk6_0,X1) != k1_funct_1(esk6_0,esk3_1(esk6_0))
    | ~ r2_hidden(X1,k1_relat_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_15]),c_0_34])]),c_0_45])).

cnf(c_0_53,plain,
    ( v2_funct_1(X1)
    | esk3_1(X1) != esk4_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( esk4_1(esk6_0) = esk3_1(esk6_0)
    | ~ r2_hidden(esk3_1(esk6_0),k1_relat_1(esk6_0)) ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_55,negated_conjecture,
    ( ~ r2_hidden(esk3_1(esk6_0),k1_relat_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_15]),c_0_34])]),c_0_45])).

cnf(c_0_56,plain,
    ( r2_hidden(esk3_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_15]),c_0_34])]),c_0_45]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:14:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0Y
% 0.20/0.40  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.051 s
% 0.20/0.40  # Presaturation interreduction done
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(t77_funct_2, conjecture, ![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(v2_funct_1(X2)<=>![X3, X4]:(((r2_hidden(X3,X1)&r2_hidden(X4,X1))&k1_funct_1(X2,X3)=k1_funct_1(X2,X4))=>X3=X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_funct_2)).
% 0.20/0.40  fof(t32_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X4)&r2_hidden(X3,X1))=>(X2=k1_xboole_0|k1_funct_1(k2_funct_1(X4),k1_funct_1(X4,X3))=X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_funct_2)).
% 0.20/0.40  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.20/0.40  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.20/0.40  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.20/0.40  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 0.20/0.40  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.40  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.40  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.40  fof(d8_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)<=>![X2, X3]:(((r2_hidden(X2,k1_relat_1(X1))&r2_hidden(X3,k1_relat_1(X1)))&k1_funct_1(X1,X2)=k1_funct_1(X1,X3))=>X2=X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_funct_1)).
% 0.20/0.40  fof(c_0_10, negated_conjecture, ~(![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(v2_funct_1(X2)<=>![X3, X4]:(((r2_hidden(X3,X1)&r2_hidden(X4,X1))&k1_funct_1(X2,X3)=k1_funct_1(X2,X4))=>X3=X4)))), inference(assume_negation,[status(cth)],[t77_funct_2])).
% 0.20/0.40  fof(c_0_11, plain, ![X29, X30, X31, X32]:(~v1_funct_1(X32)|~v1_funct_2(X32,X29,X30)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|(~v2_funct_1(X32)|~r2_hidden(X31,X29)|(X30=k1_xboole_0|k1_funct_1(k2_funct_1(X32),k1_funct_1(X32,X31))=X31))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_funct_2])])).
% 0.20/0.40  fof(c_0_12, negated_conjecture, ![X37, X38]:(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk5_0,esk5_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk5_0))))&(((((r2_hidden(esk7_0,esk5_0)|~v2_funct_1(esk6_0))&(r2_hidden(esk8_0,esk5_0)|~v2_funct_1(esk6_0)))&(k1_funct_1(esk6_0,esk7_0)=k1_funct_1(esk6_0,esk8_0)|~v2_funct_1(esk6_0)))&(esk7_0!=esk8_0|~v2_funct_1(esk6_0)))&(v2_funct_1(esk6_0)|(~r2_hidden(X37,esk5_0)|~r2_hidden(X38,esk5_0)|k1_funct_1(esk6_0,X37)!=k1_funct_1(esk6_0,X38)|X37=X38)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])])).
% 0.20/0.40  cnf(c_0_13, plain, (X3=k1_xboole_0|k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X4))=X4|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v2_funct_1(X1)|~r2_hidden(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_14, negated_conjecture, (v1_funct_2(esk6_0,esk5_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.40  cnf(c_0_15, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.40  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.40  cnf(c_0_17, negated_conjecture, (k1_funct_1(k2_funct_1(esk6_0),k1_funct_1(esk6_0,X1))=X1|esk5_0=k1_xboole_0|~v2_funct_1(esk6_0)|~r2_hidden(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15]), c_0_16])])).
% 0.20/0.40  cnf(c_0_18, negated_conjecture, (r2_hidden(esk8_0,esk5_0)|~v2_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.40  fof(c_0_19, plain, ![X26, X27, X28]:((v4_relat_1(X28,X26)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))&(v5_relat_1(X28,X27)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.20/0.40  fof(c_0_20, plain, ![X15, X16]:(~v1_relat_1(X15)|(~m1_subset_1(X16,k1_zfmisc_1(X15))|v1_relat_1(X16))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.20/0.40  fof(c_0_21, plain, ![X19, X20]:v1_relat_1(k2_zfmisc_1(X19,X20)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.20/0.40  cnf(c_0_22, negated_conjecture, (k1_funct_1(k2_funct_1(esk6_0),k1_funct_1(esk6_0,esk8_0))=esk8_0|esk5_0=k1_xboole_0|~v2_funct_1(esk6_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.40  cnf(c_0_23, negated_conjecture, (k1_funct_1(esk6_0,esk7_0)=k1_funct_1(esk6_0,esk8_0)|~v2_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.40  fof(c_0_24, plain, ![X17, X18]:((~v4_relat_1(X18,X17)|r1_tarski(k1_relat_1(X18),X17)|~v1_relat_1(X18))&(~r1_tarski(k1_relat_1(X18),X17)|v4_relat_1(X18,X17)|~v1_relat_1(X18))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.20/0.40  cnf(c_0_25, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.40  cnf(c_0_26, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.40  cnf(c_0_27, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.40  fof(c_0_28, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.40  cnf(c_0_29, negated_conjecture, (esk7_0!=esk8_0|~v2_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.40  cnf(c_0_30, negated_conjecture, (esk8_0=k1_funct_1(k2_funct_1(esk6_0),k1_funct_1(esk6_0,esk7_0))|esk5_0=k1_xboole_0|~v2_funct_1(esk6_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.40  fof(c_0_31, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk2_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk2_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.40  cnf(c_0_32, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.40  cnf(c_0_33, negated_conjecture, (v4_relat_1(esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_25, c_0_16])).
% 0.20/0.40  cnf(c_0_34, negated_conjecture, (v1_relat_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_16]), c_0_27])])).
% 0.20/0.40  cnf(c_0_35, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.40  cnf(c_0_36, negated_conjecture, (r2_hidden(esk7_0,esk5_0)|~v2_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.40  cnf(c_0_37, negated_conjecture, (esk5_0=k1_xboole_0|k1_funct_1(k2_funct_1(esk6_0),k1_funct_1(esk6_0,esk7_0))!=esk7_0|~v2_funct_1(esk6_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.40  cnf(c_0_38, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.40  cnf(c_0_39, negated_conjecture, (r1_tarski(k1_relat_1(esk6_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])])).
% 0.20/0.40  cnf(c_0_40, negated_conjecture, (~v2_funct_1(esk6_0)|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_35, c_0_18])).
% 0.20/0.40  cnf(c_0_41, negated_conjecture, (esk5_0=k1_xboole_0|~v2_funct_1(esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_36]), c_0_37])).
% 0.20/0.40  cnf(c_0_42, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.40  cnf(c_0_43, negated_conjecture, (v2_funct_1(esk6_0)|X1=X2|~r2_hidden(X1,esk5_0)|~r2_hidden(X2,esk5_0)|k1_funct_1(esk6_0,X1)!=k1_funct_1(esk6_0,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.40  cnf(c_0_44, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,k1_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.40  cnf(c_0_45, negated_conjecture, (~v2_funct_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])])).
% 0.20/0.40  cnf(c_0_46, negated_conjecture, (X1=X2|k1_funct_1(esk6_0,X1)!=k1_funct_1(esk6_0,X2)|~r2_hidden(X2,k1_relat_1(esk6_0))|~r2_hidden(X1,esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])).
% 0.20/0.40  fof(c_0_47, plain, ![X21, X22, X23]:((~v2_funct_1(X21)|(~r2_hidden(X22,k1_relat_1(X21))|~r2_hidden(X23,k1_relat_1(X21))|k1_funct_1(X21,X22)!=k1_funct_1(X21,X23)|X22=X23)|(~v1_relat_1(X21)|~v1_funct_1(X21)))&((((r2_hidden(esk3_1(X21),k1_relat_1(X21))|v2_funct_1(X21)|(~v1_relat_1(X21)|~v1_funct_1(X21)))&(r2_hidden(esk4_1(X21),k1_relat_1(X21))|v2_funct_1(X21)|(~v1_relat_1(X21)|~v1_funct_1(X21))))&(k1_funct_1(X21,esk3_1(X21))=k1_funct_1(X21,esk4_1(X21))|v2_funct_1(X21)|(~v1_relat_1(X21)|~v1_funct_1(X21))))&(esk3_1(X21)!=esk4_1(X21)|v2_funct_1(X21)|(~v1_relat_1(X21)|~v1_funct_1(X21))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).
% 0.20/0.40  cnf(c_0_48, negated_conjecture, (X1=X2|k1_funct_1(esk6_0,X1)!=k1_funct_1(esk6_0,X2)|~r2_hidden(X2,k1_relat_1(esk6_0))|~r2_hidden(X1,k1_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_46, c_0_44])).
% 0.20/0.40  cnf(c_0_49, plain, (k1_funct_1(X1,esk3_1(X1))=k1_funct_1(X1,esk4_1(X1))|v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.40  cnf(c_0_50, negated_conjecture, (X1=esk4_1(esk6_0)|k1_funct_1(esk6_0,X1)!=k1_funct_1(esk6_0,esk3_1(esk6_0))|~r2_hidden(esk4_1(esk6_0),k1_relat_1(esk6_0))|~r2_hidden(X1,k1_relat_1(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_15]), c_0_34])]), c_0_45])).
% 0.20/0.40  cnf(c_0_51, plain, (r2_hidden(esk4_1(X1),k1_relat_1(X1))|v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.40  cnf(c_0_52, negated_conjecture, (X1=esk4_1(esk6_0)|k1_funct_1(esk6_0,X1)!=k1_funct_1(esk6_0,esk3_1(esk6_0))|~r2_hidden(X1,k1_relat_1(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_15]), c_0_34])]), c_0_45])).
% 0.20/0.40  cnf(c_0_53, plain, (v2_funct_1(X1)|esk3_1(X1)!=esk4_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.40  cnf(c_0_54, negated_conjecture, (esk4_1(esk6_0)=esk3_1(esk6_0)|~r2_hidden(esk3_1(esk6_0),k1_relat_1(esk6_0))), inference(er,[status(thm)],[c_0_52])).
% 0.20/0.40  cnf(c_0_55, negated_conjecture, (~r2_hidden(esk3_1(esk6_0),k1_relat_1(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_15]), c_0_34])]), c_0_45])).
% 0.20/0.40  cnf(c_0_56, plain, (r2_hidden(esk3_1(X1),k1_relat_1(X1))|v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.40  cnf(c_0_57, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_15]), c_0_34])]), c_0_45]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 58
% 0.20/0.40  # Proof object clause steps            : 38
% 0.20/0.40  # Proof object formula steps           : 20
% 0.20/0.40  # Proof object conjectures             : 29
% 0.20/0.40  # Proof object clause conjectures      : 26
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 20
% 0.20/0.40  # Proof object initial formulas used   : 10
% 0.20/0.40  # Proof object generating inferences   : 18
% 0.20/0.40  # Proof object simplifying inferences  : 27
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 10
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 26
% 0.20/0.40  # Removed in clause preprocessing      : 0
% 0.20/0.40  # Initial clauses in saturation        : 26
% 0.20/0.40  # Processed clauses                    : 107
% 0.20/0.40  # ...of these trivial                  : 0
% 0.20/0.40  # ...subsumed                          : 24
% 0.20/0.40  # ...remaining for further processing  : 83
% 0.20/0.40  # Other redundant clauses eliminated   : 0
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 5
% 0.20/0.40  # Backward-rewritten                   : 0
% 0.20/0.40  # Generated clauses                    : 81
% 0.20/0.40  # ...of the previous two non-trivial   : 62
% 0.20/0.40  # Contextual simplify-reflections      : 3
% 0.20/0.40  # Paramodulations                      : 75
% 0.20/0.40  # Factorizations                       : 0
% 0.20/0.40  # Equation resolutions                 : 6
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 52
% 0.20/0.40  #    Positive orientable unit clauses  : 11
% 0.20/0.40  #    Positive unorientable unit clauses: 0
% 0.20/0.40  #    Negative unit clauses             : 3
% 0.20/0.40  #    Non-unit-clauses                  : 38
% 0.20/0.40  # Current number of unprocessed clauses: 1
% 0.20/0.40  # ...number of literals in the above   : 4
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 31
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 343
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 140
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 10
% 0.20/0.40  # Unit Clause-clause subsumption calls : 28
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 4
% 0.20/0.40  # BW rewrite match successes           : 0
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 3315
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.058 s
% 0.20/0.40  # System time              : 0.006 s
% 0.20/0.40  # Total time               : 0.064 s
% 0.20/0.40  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
