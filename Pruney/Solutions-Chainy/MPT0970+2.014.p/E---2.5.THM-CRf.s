%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:01:28 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  146 (8403544 expanded)
%              Number of clauses        :  125 (3385438 expanded)
%              Number of leaves         :   10 (1958687 expanded)
%              Depth                    :   44
%              Number of atoms          :  446 (43916990 expanded)
%              Number of equality atoms :  180 (13541898 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    5 (   2 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_10,negated_conjecture,(
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

fof(c_0_11,plain,(
    ! [X15,X16,X17,X19,X20,X21,X23] :
      ( ( r2_hidden(esk2_3(X15,X16,X17),k1_relat_1(X15))
        | ~ r2_hidden(X17,X16)
        | X16 != k2_relat_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( X17 = k1_funct_1(X15,esk2_3(X15,X16,X17))
        | ~ r2_hidden(X17,X16)
        | X16 != k2_relat_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( ~ r2_hidden(X20,k1_relat_1(X15))
        | X19 != k1_funct_1(X15,X20)
        | r2_hidden(X19,X16)
        | X16 != k2_relat_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( ~ r2_hidden(esk3_2(X15,X21),X21)
        | ~ r2_hidden(X23,k1_relat_1(X15))
        | esk3_2(X15,X21) != k1_funct_1(X15,X23)
        | X21 = k2_relat_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( r2_hidden(esk4_2(X15,X21),k1_relat_1(X15))
        | r2_hidden(esk3_2(X15,X21),X21)
        | X21 = k2_relat_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( esk3_2(X15,X21) = k1_funct_1(X15,esk4_2(X15,X21))
        | r2_hidden(esk3_2(X15,X21),X21)
        | X21 = k2_relat_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_12,plain,(
    ! [X25,X26,X27] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | v1_relat_1(X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_13,negated_conjecture,(
    ! [X43] :
      ( v1_funct_1(esk7_0)
      & v1_funct_2(esk7_0,esk5_0,esk6_0)
      & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))
      & ( r2_hidden(esk8_1(X43),esk5_0)
        | ~ r2_hidden(X43,esk6_0) )
      & ( X43 = k1_funct_1(esk7_0,esk8_1(X43))
        | ~ r2_hidden(X43,esk6_0) )
      & k2_relset_1(esk5_0,esk6_0,esk7_0) != esk6_0 ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])])).

fof(c_0_14,plain,(
    ! [X31,X32,X33] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
      | k1_relset_1(X31,X32,X33) = k1_relat_1(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_15,plain,(
    ! [X34,X35,X36] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
      | k2_relset_1(X34,X35,X36) = k2_relat_1(X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_16,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,plain,(
    ! [X37,X38,X39] :
      ( ( ~ v1_funct_2(X39,X37,X38)
        | X37 = k1_relset_1(X37,X38,X39)
        | X38 = k1_xboole_0
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( X37 != k1_relset_1(X37,X38,X39)
        | v1_funct_2(X39,X37,X38)
        | X38 = k1_xboole_0
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( ~ v1_funct_2(X39,X37,X38)
        | X37 = k1_relset_1(X37,X38,X39)
        | X37 != k1_xboole_0
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( X37 != k1_relset_1(X37,X38,X39)
        | v1_funct_2(X39,X37,X38)
        | X37 != k1_xboole_0
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( ~ v1_funct_2(X39,X37,X38)
        | X39 = k1_xboole_0
        | X37 = k1_xboole_0
        | X38 != k1_xboole_0
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( X39 != k1_xboole_0
        | v1_funct_2(X39,X37,X38)
        | X37 = k1_xboole_0
        | X38 != k1_xboole_0
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_20,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_16])])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_2(esk7_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,negated_conjecture,
    ( k1_relset_1(esk5_0,esk6_0,esk7_0) = k1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_18])).

cnf(c_0_28,plain,
    ( esk3_2(X1,X2) = k1_funct_1(X1,esk4_2(X1,X2))
    | r2_hidden(esk3_2(X1,X2),X2)
    | X2 = k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_29,negated_conjecture,
    ( k2_relset_1(esk5_0,esk6_0,esk7_0) != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_30,negated_conjecture,
    ( k2_relset_1(esk5_0,esk6_0,esk7_0) = k2_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_18])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk7_0,X1),k2_relat_1(esk7_0))
    | ~ r2_hidden(X1,k1_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_32,negated_conjecture,
    ( k1_relat_1(esk7_0) = esk5_0
    | esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_18])])).

cnf(c_0_33,negated_conjecture,
    ( X1 = k1_funct_1(esk7_0,esk8_1(X1))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_34,negated_conjecture,
    ( k1_funct_1(esk7_0,esk4_2(esk7_0,X1)) = esk3_2(esk7_0,X1)
    | X1 = k2_relat_1(esk7_0)
    | r2_hidden(esk3_2(esk7_0,X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_23]),c_0_24])])).

cnf(c_0_35,negated_conjecture,
    ( k2_relat_1(esk7_0) != esk6_0 ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk8_1(X1),esk5_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_37,plain,(
    ! [X13,X14] :
      ( ( ~ v5_relat_1(X14,X13)
        | r1_tarski(k2_relat_1(X14),X13)
        | ~ v1_relat_1(X14) )
      & ( ~ r1_tarski(k2_relat_1(X14),X13)
        | v5_relat_1(X14,X13)
        | ~ v1_relat_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

fof(c_0_38,plain,(
    ! [X28,X29,X30] :
      ( ( v4_relat_1(X30,X28)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29))) )
      & ( v5_relat_1(X30,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_39,plain,
    ( X2 = k2_relat_1(X1)
    | ~ r2_hidden(esk3_2(X1,X2),X2)
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | esk3_2(X1,X2) != k1_funct_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_40,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_41,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(k1_funct_1(esk7_0,X1),k2_relat_1(esk7_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( k1_funct_1(esk7_0,esk8_1(esk3_2(esk7_0,esk6_0))) = esk3_2(esk7_0,esk6_0)
    | k1_funct_1(esk7_0,esk4_2(esk7_0,esk6_0)) = esk3_2(esk7_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( k1_funct_1(esk7_0,esk4_2(esk7_0,esk6_0)) = esk3_2(esk7_0,esk6_0)
    | r2_hidden(esk8_1(esk3_2(esk7_0,esk6_0)),esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_34]),c_0_35])).

cnf(c_0_44,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( X1 = k2_relat_1(esk7_0)
    | esk3_2(esk7_0,X1) != k1_funct_1(esk7_0,X2)
    | ~ r2_hidden(esk3_2(esk7_0,X1),X1)
    | ~ r2_hidden(X2,k1_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_23]),c_0_24])])).

cnf(c_0_47,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( k1_funct_1(esk7_0,esk4_2(esk7_0,esk6_0)) = esk3_2(esk7_0,esk6_0)
    | esk6_0 = k1_xboole_0
    | r2_hidden(esk3_2(esk7_0,esk6_0),k2_relat_1(esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk7_0),X1)
    | ~ v5_relat_1(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_24])).

cnf(c_0_50,negated_conjecture,
    ( v5_relat_1(esk7_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_18])).

cnf(c_0_51,negated_conjecture,
    ( X1 = k2_relat_1(esk7_0)
    | esk6_0 = k1_xboole_0
    | esk3_2(esk7_0,X1) != k1_funct_1(esk7_0,X2)
    | ~ r2_hidden(esk3_2(esk7_0,X1),X1)
    | ~ r2_hidden(X2,esk5_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_32])).

cnf(c_0_52,negated_conjecture,
    ( k1_funct_1(esk7_0,esk4_2(esk7_0,esk6_0)) = esk3_2(esk7_0,esk6_0)
    | esk6_0 = k1_xboole_0
    | r2_hidden(esk3_2(esk7_0,esk6_0),X1)
    | ~ r1_tarski(k2_relat_1(esk7_0),X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk7_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( k1_funct_1(esk7_0,esk4_2(esk7_0,esk6_0)) = esk3_2(esk7_0,esk6_0)
    | X1 = k2_relat_1(esk7_0)
    | esk6_0 = k1_xboole_0
    | esk3_2(esk7_0,X1) != k1_funct_1(esk7_0,esk8_1(esk3_2(esk7_0,esk6_0)))
    | ~ r2_hidden(esk3_2(esk7_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_43])).

cnf(c_0_55,negated_conjecture,
    ( k1_funct_1(esk7_0,esk4_2(esk7_0,esk6_0)) = esk3_2(esk7_0,esk6_0)
    | esk6_0 = k1_xboole_0
    | r2_hidden(esk3_2(esk7_0,esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_56,negated_conjecture,
    ( k1_funct_1(esk7_0,esk4_2(esk7_0,esk6_0)) = esk3_2(esk7_0,esk6_0)
    | esk6_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_35]),c_0_42])).

cnf(c_0_57,plain,
    ( r2_hidden(esk4_2(X1,X2),k1_relat_1(X1))
    | r2_hidden(esk3_2(X1,X2),X2)
    | X2 = k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_58,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk3_2(esk7_0,esk6_0),k2_relat_1(esk7_0))
    | ~ r2_hidden(esk4_2(esk7_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_56])).

cnf(c_0_59,negated_conjecture,
    ( X1 = k2_relat_1(esk7_0)
    | esk6_0 = k1_xboole_0
    | r2_hidden(esk4_2(esk7_0,X1),esk5_0)
    | r2_hidden(esk3_2(esk7_0,X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_32]),c_0_23]),c_0_24])])).

cnf(c_0_60,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk3_2(esk7_0,esk6_0),k2_relat_1(esk7_0))
    | r2_hidden(esk3_2(esk7_0,esk6_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_35])).

cnf(c_0_61,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk3_2(esk7_0,esk6_0),esk6_0)
    | r2_hidden(esk3_2(esk7_0,esk6_0),X1)
    | ~ r1_tarski(k2_relat_1(esk7_0),X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_60])).

cnf(c_0_62,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk3_2(esk7_0,esk6_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(ef,[status(thm)],[c_0_61]),c_0_53])])).

cnf(c_0_63,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk8_1(esk3_2(esk7_0,esk6_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_62])).

cnf(c_0_64,negated_conjecture,
    ( X1 = k2_relat_1(esk7_0)
    | esk6_0 = k1_xboole_0
    | esk3_2(esk7_0,X1) != k1_funct_1(esk7_0,esk8_1(esk3_2(esk7_0,esk6_0)))
    | ~ r2_hidden(esk3_2(esk7_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_63])).

cnf(c_0_65,negated_conjecture,
    ( k1_funct_1(esk7_0,esk8_1(esk3_2(esk7_0,esk6_0))) = esk3_2(esk7_0,esk6_0)
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_62])).

cnf(c_0_66,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_67,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_62]),c_0_35]),c_0_65])).

cnf(c_0_68,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,k1_xboole_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) ),
    inference(er,[status(thm)],[c_0_66])).

cnf(c_0_69,negated_conjecture,
    ( v1_funct_2(esk7_0,esk5_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_26,c_0_67])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[c_0_18,c_0_67])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk8_1(X1),esk5_0)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_36,c_0_67])).

cnf(c_0_72,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70])])).

cnf(c_0_73,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | ~ v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_74,negated_conjecture,
    ( k1_relset_1(esk5_0,k1_xboole_0,esk7_0) = k1_relat_1(esk7_0) ),
    inference(rw,[status(thm)],[c_0_27,c_0_67])).

cnf(c_0_75,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk8_1(X1),k1_xboole_0)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_76,negated_conjecture,
    ( k2_relat_1(esk7_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_35,c_0_67])).

fof(c_0_77,plain,(
    ! [X12] : r1_tarski(k1_xboole_0,X12) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_78,negated_conjecture,
    ( X1 = k2_relat_1(esk7_0)
    | r2_hidden(esk4_2(esk7_0,X1),k1_relat_1(esk7_0))
    | r2_hidden(esk3_2(esk7_0,X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_23]),c_0_24])])).

cnf(c_0_79,plain,
    ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
    | ~ v1_funct_2(X2,k1_xboole_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(er,[status(thm)],[c_0_73])).

cnf(c_0_80,negated_conjecture,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,esk7_0) = k1_relat_1(esk7_0)
    | esk7_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_74,c_0_72])).

cnf(c_0_81,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_70,c_0_72])).

cnf(c_0_82,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | v1_funct_2(esk7_0,k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_72])).

cnf(c_0_83,negated_conjecture,
    ( k1_funct_1(esk7_0,esk4_2(esk7_0,k1_xboole_0)) = esk3_2(esk7_0,k1_xboole_0)
    | esk7_0 = k1_xboole_0
    | r2_hidden(esk8_1(esk3_2(esk7_0,k1_xboole_0)),k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_34]),c_0_76])).

cnf(c_0_84,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_85,negated_conjecture,
    ( k1_funct_1(esk7_0,esk4_2(esk7_0,X1)) = esk3_2(esk7_0,X1)
    | X1 = k2_relat_1(esk7_0)
    | r2_hidden(esk3_2(esk7_0,X1),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_34])).

cnf(c_0_86,negated_conjecture,
    ( X1 = k2_relat_1(esk7_0)
    | r2_hidden(esk3_2(esk7_0,X1),X1)
    | r2_hidden(esk4_2(esk7_0,X1),X2)
    | ~ r1_tarski(k1_relat_1(esk7_0),X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_78])).

cnf(c_0_87,negated_conjecture,
    ( k1_relat_1(esk7_0) = k1_xboole_0
    | esk7_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81]),c_0_82])).

cnf(c_0_88,negated_conjecture,
    ( k1_funct_1(esk7_0,esk4_2(esk7_0,k1_xboole_0)) = esk3_2(esk7_0,k1_xboole_0)
    | esk7_0 = k1_xboole_0
    | r2_hidden(esk8_1(esk3_2(esk7_0,k1_xboole_0)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_83]),c_0_84])])).

cnf(c_0_89,negated_conjecture,
    ( k1_funct_1(esk7_0,esk4_2(esk7_0,k1_xboole_0)) = esk3_2(esk7_0,k1_xboole_0)
    | k2_relat_1(esk7_0) = k1_xboole_0
    | r2_hidden(esk3_2(esk7_0,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_85,c_0_84])).

cnf(c_0_90,negated_conjecture,
    ( X1 = k2_relat_1(esk7_0)
    | esk7_0 = k1_xboole_0
    | r2_hidden(esk4_2(esk7_0,X1),X2)
    | r2_hidden(esk3_2(esk7_0,X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_84])])).

cnf(c_0_91,negated_conjecture,
    ( k1_funct_1(esk7_0,esk4_2(esk7_0,k1_xboole_0)) = esk3_2(esk7_0,k1_xboole_0)
    | X1 = k2_relat_1(esk7_0)
    | esk7_0 = k1_xboole_0
    | esk3_2(esk7_0,X1) != k1_funct_1(esk7_0,esk8_1(esk3_2(esk7_0,k1_xboole_0)))
    | ~ r2_hidden(esk3_2(esk7_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_88])).

cnf(c_0_92,negated_conjecture,
    ( k1_funct_1(esk7_0,esk4_2(esk7_0,k1_xboole_0)) = esk3_2(esk7_0,k1_xboole_0)
    | r2_hidden(esk3_2(esk7_0,k1_xboole_0),X1) ),
    inference(sr,[status(thm)],[c_0_89,c_0_76])).

cnf(c_0_93,negated_conjecture,
    ( k1_funct_1(esk7_0,esk8_1(esk3_2(esk7_0,k1_xboole_0))) = esk3_2(esk7_0,k1_xboole_0)
    | k1_funct_1(esk7_0,esk4_2(esk7_0,k1_xboole_0)) = esk3_2(esk7_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_67]),c_0_67]),c_0_67]),c_0_67])).

cnf(c_0_94,negated_conjecture,
    ( X1 = k2_relat_1(esk7_0)
    | esk7_0 = k1_xboole_0
    | r2_hidden(esk4_2(esk7_0,X1),X2)
    | r2_hidden(esk3_2(esk7_0,X1),X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_47,c_0_90])).

cnf(c_0_95,negated_conjecture,
    ( X1 = k2_relat_1(esk7_0)
    | r2_hidden(esk4_2(esk7_0,X1),k1_relat_1(esk7_0))
    | r2_hidden(esk3_2(esk7_0,X1),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_78])).

cnf(c_0_96,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(k1_funct_1(esk7_0,X1),k2_relat_1(esk7_0))
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_87])).

cnf(c_0_97,negated_conjecture,
    ( k1_funct_1(esk7_0,esk4_2(esk7_0,k1_xboole_0)) = esk3_2(esk7_0,k1_xboole_0)
    | esk7_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_76]),c_0_93])).

cnf(c_0_98,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk3_2(esk7_0,k1_xboole_0),X1)
    | r2_hidden(esk4_2(esk7_0,k1_xboole_0),X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_84]),c_0_76])).

cnf(c_0_99,negated_conjecture,
    ( r2_hidden(esk4_2(esk7_0,k1_xboole_0),k1_relat_1(esk7_0))
    | r2_hidden(esk3_2(esk7_0,k1_xboole_0),X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_84]),c_0_76])).

cnf(c_0_100,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk3_2(esk7_0,k1_xboole_0),k2_relat_1(esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_98])).

cnf(c_0_101,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk7_0,esk4_2(esk7_0,k1_xboole_0)),k2_relat_1(esk7_0))
    | r2_hidden(esk3_2(esk7_0,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_99])).

cnf(c_0_102,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk3_2(esk7_0,k1_xboole_0),X1)
    | ~ r1_tarski(k2_relat_1(esk7_0),X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_100])).

cnf(c_0_103,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk7_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_53,c_0_67])).

cnf(c_0_104,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk7_0,esk4_2(esk7_0,k1_xboole_0)),X1)
    | r2_hidden(esk3_2(esk7_0,k1_xboole_0),X2)
    | ~ r1_tarski(k2_relat_1(esk7_0),X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_101])).

cnf(c_0_105,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk3_2(esk7_0,k1_xboole_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_106,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk7_0,esk4_2(esk7_0,k1_xboole_0)),k1_xboole_0)
    | r2_hidden(esk3_2(esk7_0,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_104,c_0_103])).

cnf(c_0_107,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk3_2(esk7_0,k1_xboole_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_105]),c_0_84])])).

cnf(c_0_108,negated_conjecture,
    ( k1_funct_1(esk7_0,esk8_1(X1)) = X1
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_33,c_0_67])).

cnf(c_0_109,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk7_0,esk4_2(esk7_0,k1_xboole_0)),X1)
    | r2_hidden(esk3_2(esk7_0,k1_xboole_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_106]),c_0_84])])).

cnf(c_0_110,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk8_1(esk3_2(esk7_0,k1_xboole_0)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_107])).

cnf(c_0_111,negated_conjecture,
    ( k1_funct_1(esk7_0,esk8_1(k1_funct_1(esk7_0,esk4_2(esk7_0,k1_xboole_0)))) = k1_funct_1(esk7_0,esk4_2(esk7_0,k1_xboole_0))
    | r2_hidden(esk3_2(esk7_0,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_112,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk8_1(esk3_2(esk7_0,k1_xboole_0)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_110]),c_0_84])])).

cnf(c_0_113,negated_conjecture,
    ( k1_funct_1(esk7_0,esk8_1(k1_funct_1(esk7_0,esk4_2(esk7_0,k1_xboole_0)))) = k1_funct_1(esk7_0,esk4_2(esk7_0,k1_xboole_0))
    | k1_funct_1(esk7_0,esk8_1(esk3_2(esk7_0,k1_xboole_0))) = esk3_2(esk7_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_108,c_0_111])).

cnf(c_0_114,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_115,negated_conjecture,
    ( X1 = k2_relat_1(esk7_0)
    | esk7_0 = k1_xboole_0
    | esk3_2(esk7_0,X1) != k1_funct_1(esk7_0,esk8_1(esk3_2(esk7_0,k1_xboole_0)))
    | ~ r2_hidden(esk3_2(esk7_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_112])).

cnf(c_0_116,negated_conjecture,
    ( k1_funct_1(esk7_0,esk8_1(esk3_2(esk7_0,k1_xboole_0))) = esk3_2(esk7_0,k1_xboole_0)
    | esk7_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_113,c_0_97])).

cnf(c_0_117,plain,
    ( r2_hidden(esk2_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_114])).

cnf(c_0_118,plain,
    ( X1 = k1_funct_1(X2,esk2_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_119,negated_conjecture,
    ( esk7_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_107]),c_0_76]),c_0_116])).

cnf(c_0_120,negated_conjecture,
    ( r2_hidden(esk2_3(esk7_0,k2_relat_1(esk7_0),X1),k1_relat_1(esk7_0))
    | ~ r2_hidden(X1,k2_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_23]),c_0_24])])).

cnf(c_0_121,plain,
    ( k1_funct_1(X1,esk2_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_118])).

cnf(c_0_122,negated_conjecture,
    ( v1_funct_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_23,c_0_119])).

cnf(c_0_123,negated_conjecture,
    ( v1_relat_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_24,c_0_119])).

cnf(c_0_124,negated_conjecture,
    ( k1_funct_1(esk7_0,esk4_2(esk7_0,k1_xboole_0)) = esk3_2(esk7_0,k1_xboole_0)
    | r2_hidden(esk2_3(esk7_0,k2_relat_1(esk7_0),esk3_2(esk7_0,k1_xboole_0)),k1_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_120,c_0_92])).

cnf(c_0_125,negated_conjecture,
    ( k1_funct_1(esk7_0,esk2_3(esk7_0,k2_relat_1(esk7_0),X1)) = X1
    | ~ r2_hidden(X1,k2_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_23]),c_0_24])])).

cnf(c_0_126,negated_conjecture,
    ( X1 = k2_relat_1(k1_xboole_0)
    | esk3_2(k1_xboole_0,X1) != k1_funct_1(k1_xboole_0,X2)
    | ~ r2_hidden(esk3_2(k1_xboole_0,X1),X1)
    | ~ r2_hidden(X2,k1_relat_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_122]),c_0_123])])).

cnf(c_0_127,negated_conjecture,
    ( k1_funct_1(k1_xboole_0,esk4_2(k1_xboole_0,k1_xboole_0)) = esk3_2(k1_xboole_0,k1_xboole_0)
    | r2_hidden(esk2_3(k1_xboole_0,k2_relat_1(k1_xboole_0),esk3_2(k1_xboole_0,k1_xboole_0)),k1_relat_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_124,c_0_119]),c_0_119]),c_0_119]),c_0_119]),c_0_119]),c_0_119]),c_0_119])).

cnf(c_0_128,negated_conjecture,
    ( k1_funct_1(esk7_0,esk2_3(esk7_0,k2_relat_1(esk7_0),esk3_2(esk7_0,k1_xboole_0))) = esk3_2(esk7_0,k1_xboole_0)
    | k1_funct_1(esk7_0,esk4_2(esk7_0,k1_xboole_0)) = esk3_2(esk7_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_125,c_0_92])).

cnf(c_0_129,negated_conjecture,
    ( k1_funct_1(k1_xboole_0,esk4_2(k1_xboole_0,k1_xboole_0)) = esk3_2(k1_xboole_0,k1_xboole_0)
    | X1 = k2_relat_1(k1_xboole_0)
    | esk3_2(k1_xboole_0,X1) != k1_funct_1(k1_xboole_0,esk2_3(k1_xboole_0,k2_relat_1(k1_xboole_0),esk3_2(k1_xboole_0,k1_xboole_0)))
    | ~ r2_hidden(esk3_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_126,c_0_127])).

cnf(c_0_130,negated_conjecture,
    ( k1_funct_1(k1_xboole_0,esk4_2(k1_xboole_0,k1_xboole_0)) = esk3_2(k1_xboole_0,k1_xboole_0)
    | r2_hidden(esk3_2(k1_xboole_0,k1_xboole_0),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_119]),c_0_119]),c_0_119]),c_0_119])).

cnf(c_0_131,negated_conjecture,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_76,c_0_119])).

cnf(c_0_132,negated_conjecture,
    ( k1_funct_1(k1_xboole_0,esk2_3(k1_xboole_0,k2_relat_1(k1_xboole_0),esk3_2(k1_xboole_0,k1_xboole_0))) = esk3_2(k1_xboole_0,k1_xboole_0)
    | k1_funct_1(k1_xboole_0,esk4_2(k1_xboole_0,k1_xboole_0)) = esk3_2(k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_128,c_0_119]),c_0_119]),c_0_119]),c_0_119]),c_0_119]),c_0_119]),c_0_119]),c_0_119])).

cnf(c_0_133,negated_conjecture,
    ( k1_funct_1(k1_xboole_0,esk4_2(k1_xboole_0,k1_xboole_0)) = esk3_2(k1_xboole_0,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_130]),c_0_131]),c_0_132])).

cnf(c_0_134,negated_conjecture,
    ( r2_hidden(esk4_2(k1_xboole_0,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | r2_hidden(esk3_2(k1_xboole_0,k1_xboole_0),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_99,c_0_119]),c_0_119]),c_0_119])).

cnf(c_0_135,negated_conjecture,
    ( r2_hidden(esk3_2(k1_xboole_0,k1_xboole_0),k2_relat_1(k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_133]),c_0_122]),c_0_123])]),c_0_134])).

cnf(c_0_136,negated_conjecture,
    ( r2_hidden(esk3_2(k1_xboole_0,k1_xboole_0),X1)
    | ~ r1_tarski(k2_relat_1(k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_135])).

cnf(c_0_137,negated_conjecture,
    ( r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_103,c_0_119])).

cnf(c_0_138,negated_conjecture,
    ( r2_hidden(esk3_2(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_136,c_0_137])).

cnf(c_0_139,negated_conjecture,
    ( r2_hidden(esk2_3(k1_xboole_0,k2_relat_1(k1_xboole_0),X1),k1_relat_1(k1_xboole_0))
    | ~ r2_hidden(X1,k2_relat_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_122]),c_0_123])])).

cnf(c_0_140,negated_conjecture,
    ( r2_hidden(esk3_2(k1_xboole_0,k1_xboole_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_138]),c_0_84])])).

cnf(c_0_141,negated_conjecture,
    ( r2_hidden(esk2_3(k1_xboole_0,k2_relat_1(k1_xboole_0),esk3_2(k1_xboole_0,k1_xboole_0)),k1_relat_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_139,c_0_140])).

cnf(c_0_142,negated_conjecture,
    ( X1 = k2_relat_1(k1_xboole_0)
    | esk3_2(k1_xboole_0,X1) != k1_funct_1(k1_xboole_0,esk2_3(k1_xboole_0,k2_relat_1(k1_xboole_0),esk3_2(k1_xboole_0,k1_xboole_0)))
    | ~ r2_hidden(esk3_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_126,c_0_141])).

cnf(c_0_143,negated_conjecture,
    ( k1_funct_1(k1_xboole_0,esk2_3(k1_xboole_0,k2_relat_1(k1_xboole_0),X1)) = X1
    | ~ r2_hidden(X1,k2_relat_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_122]),c_0_123])])).

cnf(c_0_144,negated_conjecture,
    ( k1_funct_1(k1_xboole_0,esk2_3(k1_xboole_0,k2_relat_1(k1_xboole_0),esk3_2(k1_xboole_0,k1_xboole_0))) != esk3_2(k1_xboole_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_142,c_0_140]),c_0_131])).

cnf(c_0_145,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_140]),c_0_144]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:36:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.49  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S053I
% 0.19/0.49  # and selection function HSelectMinInfpos.
% 0.19/0.49  #
% 0.19/0.49  # Preprocessing time       : 0.028 s
% 0.19/0.49  # Presaturation interreduction done
% 0.19/0.49  
% 0.19/0.49  # Proof found!
% 0.19/0.49  # SZS status Theorem
% 0.19/0.49  # SZS output start CNFRefutation
% 0.19/0.49  fof(t16_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(![X4]:~((r2_hidden(X4,X2)&![X5]:~((r2_hidden(X5,X1)&X4=k1_funct_1(X3,X5)))))=>k2_relset_1(X1,X2,X3)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_2)).
% 0.19/0.49  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 0.19/0.49  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.49  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.19/0.49  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.19/0.49  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.19/0.49  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 0.19/0.49  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.19/0.49  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.49  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.49  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(![X4]:~((r2_hidden(X4,X2)&![X5]:~((r2_hidden(X5,X1)&X4=k1_funct_1(X3,X5)))))=>k2_relset_1(X1,X2,X3)=X2))), inference(assume_negation,[status(cth)],[t16_funct_2])).
% 0.19/0.49  fof(c_0_11, plain, ![X15, X16, X17, X19, X20, X21, X23]:((((r2_hidden(esk2_3(X15,X16,X17),k1_relat_1(X15))|~r2_hidden(X17,X16)|X16!=k2_relat_1(X15)|(~v1_relat_1(X15)|~v1_funct_1(X15)))&(X17=k1_funct_1(X15,esk2_3(X15,X16,X17))|~r2_hidden(X17,X16)|X16!=k2_relat_1(X15)|(~v1_relat_1(X15)|~v1_funct_1(X15))))&(~r2_hidden(X20,k1_relat_1(X15))|X19!=k1_funct_1(X15,X20)|r2_hidden(X19,X16)|X16!=k2_relat_1(X15)|(~v1_relat_1(X15)|~v1_funct_1(X15))))&((~r2_hidden(esk3_2(X15,X21),X21)|(~r2_hidden(X23,k1_relat_1(X15))|esk3_2(X15,X21)!=k1_funct_1(X15,X23))|X21=k2_relat_1(X15)|(~v1_relat_1(X15)|~v1_funct_1(X15)))&((r2_hidden(esk4_2(X15,X21),k1_relat_1(X15))|r2_hidden(esk3_2(X15,X21),X21)|X21=k2_relat_1(X15)|(~v1_relat_1(X15)|~v1_funct_1(X15)))&(esk3_2(X15,X21)=k1_funct_1(X15,esk4_2(X15,X21))|r2_hidden(esk3_2(X15,X21),X21)|X21=k2_relat_1(X15)|(~v1_relat_1(X15)|~v1_funct_1(X15)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.19/0.49  fof(c_0_12, plain, ![X25, X26, X27]:(~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))|v1_relat_1(X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.49  fof(c_0_13, negated_conjecture, ![X43]:(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,esk5_0,esk6_0))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))))&(((r2_hidden(esk8_1(X43),esk5_0)|~r2_hidden(X43,esk6_0))&(X43=k1_funct_1(esk7_0,esk8_1(X43))|~r2_hidden(X43,esk6_0)))&k2_relset_1(esk5_0,esk6_0,esk7_0)!=esk6_0)), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])])).
% 0.19/0.49  fof(c_0_14, plain, ![X31, X32, X33]:(~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|k1_relset_1(X31,X32,X33)=k1_relat_1(X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.19/0.49  fof(c_0_15, plain, ![X34, X35, X36]:(~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|k2_relset_1(X34,X35,X36)=k2_relat_1(X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.19/0.49  cnf(c_0_16, plain, (r2_hidden(X3,X4)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|X4!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.49  cnf(c_0_17, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.49  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.49  fof(c_0_19, plain, ![X37, X38, X39]:((((~v1_funct_2(X39,X37,X38)|X37=k1_relset_1(X37,X38,X39)|X38=k1_xboole_0|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))&(X37!=k1_relset_1(X37,X38,X39)|v1_funct_2(X39,X37,X38)|X38=k1_xboole_0|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))))&((~v1_funct_2(X39,X37,X38)|X37=k1_relset_1(X37,X38,X39)|X37!=k1_xboole_0|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))&(X37!=k1_relset_1(X37,X38,X39)|v1_funct_2(X39,X37,X38)|X37!=k1_xboole_0|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))))&((~v1_funct_2(X39,X37,X38)|X39=k1_xboole_0|X37=k1_xboole_0|X38!=k1_xboole_0|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))&(X39!=k1_xboole_0|v1_funct_2(X39,X37,X38)|X37=k1_xboole_0|X38!=k1_xboole_0|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.19/0.49  cnf(c_0_20, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.49  cnf(c_0_21, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.49  cnf(c_0_22, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_16])])).
% 0.19/0.49  cnf(c_0_23, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.49  cnf(c_0_24, negated_conjecture, (v1_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.49  cnf(c_0_25, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.49  cnf(c_0_26, negated_conjecture, (v1_funct_2(esk7_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.49  cnf(c_0_27, negated_conjecture, (k1_relset_1(esk5_0,esk6_0,esk7_0)=k1_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_20, c_0_18])).
% 0.19/0.49  cnf(c_0_28, plain, (esk3_2(X1,X2)=k1_funct_1(X1,esk4_2(X1,X2))|r2_hidden(esk3_2(X1,X2),X2)|X2=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.49  cnf(c_0_29, negated_conjecture, (k2_relset_1(esk5_0,esk6_0,esk7_0)!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.49  cnf(c_0_30, negated_conjecture, (k2_relset_1(esk5_0,esk6_0,esk7_0)=k2_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_21, c_0_18])).
% 0.19/0.49  cnf(c_0_31, negated_conjecture, (r2_hidden(k1_funct_1(esk7_0,X1),k2_relat_1(esk7_0))|~r2_hidden(X1,k1_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])])).
% 0.19/0.49  cnf(c_0_32, negated_conjecture, (k1_relat_1(esk7_0)=esk5_0|esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_18])])).
% 0.19/0.49  cnf(c_0_33, negated_conjecture, (X1=k1_funct_1(esk7_0,esk8_1(X1))|~r2_hidden(X1,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.49  cnf(c_0_34, negated_conjecture, (k1_funct_1(esk7_0,esk4_2(esk7_0,X1))=esk3_2(esk7_0,X1)|X1=k2_relat_1(esk7_0)|r2_hidden(esk3_2(esk7_0,X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_23]), c_0_24])])).
% 0.19/0.49  cnf(c_0_35, negated_conjecture, (k2_relat_1(esk7_0)!=esk6_0), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.49  cnf(c_0_36, negated_conjecture, (r2_hidden(esk8_1(X1),esk5_0)|~r2_hidden(X1,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.49  fof(c_0_37, plain, ![X13, X14]:((~v5_relat_1(X14,X13)|r1_tarski(k2_relat_1(X14),X13)|~v1_relat_1(X14))&(~r1_tarski(k2_relat_1(X14),X13)|v5_relat_1(X14,X13)|~v1_relat_1(X14))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.19/0.49  fof(c_0_38, plain, ![X28, X29, X30]:((v4_relat_1(X30,X28)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29))))&(v5_relat_1(X30,X29)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.19/0.49  cnf(c_0_39, plain, (X2=k2_relat_1(X1)|~r2_hidden(esk3_2(X1,X2),X2)|~r2_hidden(X3,k1_relat_1(X1))|esk3_2(X1,X2)!=k1_funct_1(X1,X3)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.49  fof(c_0_40, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.49  cnf(c_0_41, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(k1_funct_1(esk7_0,X1),k2_relat_1(esk7_0))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.49  cnf(c_0_42, negated_conjecture, (k1_funct_1(esk7_0,esk8_1(esk3_2(esk7_0,esk6_0)))=esk3_2(esk7_0,esk6_0)|k1_funct_1(esk7_0,esk4_2(esk7_0,esk6_0))=esk3_2(esk7_0,esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])).
% 0.19/0.49  cnf(c_0_43, negated_conjecture, (k1_funct_1(esk7_0,esk4_2(esk7_0,esk6_0))=esk3_2(esk7_0,esk6_0)|r2_hidden(esk8_1(esk3_2(esk7_0,esk6_0)),esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_34]), c_0_35])).
% 0.19/0.49  cnf(c_0_44, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.49  cnf(c_0_45, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.49  cnf(c_0_46, negated_conjecture, (X1=k2_relat_1(esk7_0)|esk3_2(esk7_0,X1)!=k1_funct_1(esk7_0,X2)|~r2_hidden(esk3_2(esk7_0,X1),X1)|~r2_hidden(X2,k1_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_23]), c_0_24])])).
% 0.19/0.49  cnf(c_0_47, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.49  cnf(c_0_48, negated_conjecture, (k1_funct_1(esk7_0,esk4_2(esk7_0,esk6_0))=esk3_2(esk7_0,esk6_0)|esk6_0=k1_xboole_0|r2_hidden(esk3_2(esk7_0,esk6_0),k2_relat_1(esk7_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])).
% 0.19/0.49  cnf(c_0_49, negated_conjecture, (r1_tarski(k2_relat_1(esk7_0),X1)|~v5_relat_1(esk7_0,X1)), inference(spm,[status(thm)],[c_0_44, c_0_24])).
% 0.19/0.49  cnf(c_0_50, negated_conjecture, (v5_relat_1(esk7_0,esk6_0)), inference(spm,[status(thm)],[c_0_45, c_0_18])).
% 0.19/0.49  cnf(c_0_51, negated_conjecture, (X1=k2_relat_1(esk7_0)|esk6_0=k1_xboole_0|esk3_2(esk7_0,X1)!=k1_funct_1(esk7_0,X2)|~r2_hidden(esk3_2(esk7_0,X1),X1)|~r2_hidden(X2,esk5_0)), inference(spm,[status(thm)],[c_0_46, c_0_32])).
% 0.19/0.49  cnf(c_0_52, negated_conjecture, (k1_funct_1(esk7_0,esk4_2(esk7_0,esk6_0))=esk3_2(esk7_0,esk6_0)|esk6_0=k1_xboole_0|r2_hidden(esk3_2(esk7_0,esk6_0),X1)|~r1_tarski(k2_relat_1(esk7_0),X1)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.19/0.49  cnf(c_0_53, negated_conjecture, (r1_tarski(k2_relat_1(esk7_0),esk6_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.19/0.49  cnf(c_0_54, negated_conjecture, (k1_funct_1(esk7_0,esk4_2(esk7_0,esk6_0))=esk3_2(esk7_0,esk6_0)|X1=k2_relat_1(esk7_0)|esk6_0=k1_xboole_0|esk3_2(esk7_0,X1)!=k1_funct_1(esk7_0,esk8_1(esk3_2(esk7_0,esk6_0)))|~r2_hidden(esk3_2(esk7_0,X1),X1)), inference(spm,[status(thm)],[c_0_51, c_0_43])).
% 0.19/0.49  cnf(c_0_55, negated_conjecture, (k1_funct_1(esk7_0,esk4_2(esk7_0,esk6_0))=esk3_2(esk7_0,esk6_0)|esk6_0=k1_xboole_0|r2_hidden(esk3_2(esk7_0,esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.19/0.49  cnf(c_0_56, negated_conjecture, (k1_funct_1(esk7_0,esk4_2(esk7_0,esk6_0))=esk3_2(esk7_0,esk6_0)|esk6_0=k1_xboole_0), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_35]), c_0_42])).
% 0.19/0.49  cnf(c_0_57, plain, (r2_hidden(esk4_2(X1,X2),k1_relat_1(X1))|r2_hidden(esk3_2(X1,X2),X2)|X2=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.49  cnf(c_0_58, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk3_2(esk7_0,esk6_0),k2_relat_1(esk7_0))|~r2_hidden(esk4_2(esk7_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_41, c_0_56])).
% 0.19/0.49  cnf(c_0_59, negated_conjecture, (X1=k2_relat_1(esk7_0)|esk6_0=k1_xboole_0|r2_hidden(esk4_2(esk7_0,X1),esk5_0)|r2_hidden(esk3_2(esk7_0,X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_32]), c_0_23]), c_0_24])])).
% 0.19/0.49  cnf(c_0_60, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk3_2(esk7_0,esk6_0),k2_relat_1(esk7_0))|r2_hidden(esk3_2(esk7_0,esk6_0),esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_35])).
% 0.19/0.49  cnf(c_0_61, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk3_2(esk7_0,esk6_0),esk6_0)|r2_hidden(esk3_2(esk7_0,esk6_0),X1)|~r1_tarski(k2_relat_1(esk7_0),X1)), inference(spm,[status(thm)],[c_0_47, c_0_60])).
% 0.19/0.49  cnf(c_0_62, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk3_2(esk7_0,esk6_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(ef,[status(thm)],[c_0_61]), c_0_53])])).
% 0.19/0.49  cnf(c_0_63, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk8_1(esk3_2(esk7_0,esk6_0)),esk5_0)), inference(spm,[status(thm)],[c_0_36, c_0_62])).
% 0.19/0.49  cnf(c_0_64, negated_conjecture, (X1=k2_relat_1(esk7_0)|esk6_0=k1_xboole_0|esk3_2(esk7_0,X1)!=k1_funct_1(esk7_0,esk8_1(esk3_2(esk7_0,esk6_0)))|~r2_hidden(esk3_2(esk7_0,X1),X1)), inference(spm,[status(thm)],[c_0_51, c_0_63])).
% 0.19/0.49  cnf(c_0_65, negated_conjecture, (k1_funct_1(esk7_0,esk8_1(esk3_2(esk7_0,esk6_0)))=esk3_2(esk7_0,esk6_0)|esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_33, c_0_62])).
% 0.19/0.49  cnf(c_0_66, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X1,X2,X3)|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.49  cnf(c_0_67, negated_conjecture, (esk6_0=k1_xboole_0), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_62]), c_0_35]), c_0_65])).
% 0.19/0.49  cnf(c_0_68, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X2,X1,k1_xboole_0)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))), inference(er,[status(thm)],[c_0_66])).
% 0.19/0.49  cnf(c_0_69, negated_conjecture, (v1_funct_2(esk7_0,esk5_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_26, c_0_67])).
% 0.19/0.49  cnf(c_0_70, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_xboole_0)))), inference(rw,[status(thm)],[c_0_18, c_0_67])).
% 0.19/0.49  cnf(c_0_71, negated_conjecture, (r2_hidden(esk8_1(X1),esk5_0)|~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[c_0_36, c_0_67])).
% 0.19/0.49  cnf(c_0_72, negated_conjecture, (esk5_0=k1_xboole_0|esk7_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70])])).
% 0.19/0.49  cnf(c_0_73, plain, (X2=k1_relset_1(X2,X3,X1)|~v1_funct_2(X1,X2,X3)|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.49  cnf(c_0_74, negated_conjecture, (k1_relset_1(esk5_0,k1_xboole_0,esk7_0)=k1_relat_1(esk7_0)), inference(rw,[status(thm)],[c_0_27, c_0_67])).
% 0.19/0.49  cnf(c_0_75, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk8_1(X1),k1_xboole_0)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.19/0.49  cnf(c_0_76, negated_conjecture, (k2_relat_1(esk7_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_35, c_0_67])).
% 0.19/0.49  fof(c_0_77, plain, ![X12]:r1_tarski(k1_xboole_0,X12), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.49  cnf(c_0_78, negated_conjecture, (X1=k2_relat_1(esk7_0)|r2_hidden(esk4_2(esk7_0,X1),k1_relat_1(esk7_0))|r2_hidden(esk3_2(esk7_0,X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_23]), c_0_24])])).
% 0.19/0.49  cnf(c_0_79, plain, (k1_relset_1(k1_xboole_0,X1,X2)=k1_xboole_0|~v1_funct_2(X2,k1_xboole_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))), inference(er,[status(thm)],[c_0_73])).
% 0.19/0.49  cnf(c_0_80, negated_conjecture, (k1_relset_1(k1_xboole_0,k1_xboole_0,esk7_0)=k1_relat_1(esk7_0)|esk7_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_74, c_0_72])).
% 0.19/0.49  cnf(c_0_81, negated_conjecture, (esk7_0=k1_xboole_0|m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_70, c_0_72])).
% 0.19/0.49  cnf(c_0_82, negated_conjecture, (esk7_0=k1_xboole_0|v1_funct_2(esk7_0,k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_69, c_0_72])).
% 0.19/0.49  cnf(c_0_83, negated_conjecture, (k1_funct_1(esk7_0,esk4_2(esk7_0,k1_xboole_0))=esk3_2(esk7_0,k1_xboole_0)|esk7_0=k1_xboole_0|r2_hidden(esk8_1(esk3_2(esk7_0,k1_xboole_0)),k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_34]), c_0_76])).
% 0.19/0.49  cnf(c_0_84, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.19/0.49  cnf(c_0_85, negated_conjecture, (k1_funct_1(esk7_0,esk4_2(esk7_0,X1))=esk3_2(esk7_0,X1)|X1=k2_relat_1(esk7_0)|r2_hidden(esk3_2(esk7_0,X1),X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_47, c_0_34])).
% 0.19/0.49  cnf(c_0_86, negated_conjecture, (X1=k2_relat_1(esk7_0)|r2_hidden(esk3_2(esk7_0,X1),X1)|r2_hidden(esk4_2(esk7_0,X1),X2)|~r1_tarski(k1_relat_1(esk7_0),X2)), inference(spm,[status(thm)],[c_0_47, c_0_78])).
% 0.19/0.49  cnf(c_0_87, negated_conjecture, (k1_relat_1(esk7_0)=k1_xboole_0|esk7_0=k1_xboole_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_81]), c_0_82])).
% 0.19/0.49  cnf(c_0_88, negated_conjecture, (k1_funct_1(esk7_0,esk4_2(esk7_0,k1_xboole_0))=esk3_2(esk7_0,k1_xboole_0)|esk7_0=k1_xboole_0|r2_hidden(esk8_1(esk3_2(esk7_0,k1_xboole_0)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_83]), c_0_84])])).
% 0.19/0.49  cnf(c_0_89, negated_conjecture, (k1_funct_1(esk7_0,esk4_2(esk7_0,k1_xboole_0))=esk3_2(esk7_0,k1_xboole_0)|k2_relat_1(esk7_0)=k1_xboole_0|r2_hidden(esk3_2(esk7_0,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_85, c_0_84])).
% 0.19/0.49  cnf(c_0_90, negated_conjecture, (X1=k2_relat_1(esk7_0)|esk7_0=k1_xboole_0|r2_hidden(esk4_2(esk7_0,X1),X2)|r2_hidden(esk3_2(esk7_0,X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_84])])).
% 0.19/0.49  cnf(c_0_91, negated_conjecture, (k1_funct_1(esk7_0,esk4_2(esk7_0,k1_xboole_0))=esk3_2(esk7_0,k1_xboole_0)|X1=k2_relat_1(esk7_0)|esk7_0=k1_xboole_0|esk3_2(esk7_0,X1)!=k1_funct_1(esk7_0,esk8_1(esk3_2(esk7_0,k1_xboole_0)))|~r2_hidden(esk3_2(esk7_0,X1),X1)), inference(spm,[status(thm)],[c_0_46, c_0_88])).
% 0.19/0.49  cnf(c_0_92, negated_conjecture, (k1_funct_1(esk7_0,esk4_2(esk7_0,k1_xboole_0))=esk3_2(esk7_0,k1_xboole_0)|r2_hidden(esk3_2(esk7_0,k1_xboole_0),X1)), inference(sr,[status(thm)],[c_0_89, c_0_76])).
% 0.19/0.49  cnf(c_0_93, negated_conjecture, (k1_funct_1(esk7_0,esk8_1(esk3_2(esk7_0,k1_xboole_0)))=esk3_2(esk7_0,k1_xboole_0)|k1_funct_1(esk7_0,esk4_2(esk7_0,k1_xboole_0))=esk3_2(esk7_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_67]), c_0_67]), c_0_67]), c_0_67])).
% 0.19/0.49  cnf(c_0_94, negated_conjecture, (X1=k2_relat_1(esk7_0)|esk7_0=k1_xboole_0|r2_hidden(esk4_2(esk7_0,X1),X2)|r2_hidden(esk3_2(esk7_0,X1),X3)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_47, c_0_90])).
% 0.19/0.49  cnf(c_0_95, negated_conjecture, (X1=k2_relat_1(esk7_0)|r2_hidden(esk4_2(esk7_0,X1),k1_relat_1(esk7_0))|r2_hidden(esk3_2(esk7_0,X1),X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_47, c_0_78])).
% 0.19/0.49  cnf(c_0_96, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(k1_funct_1(esk7_0,X1),k2_relat_1(esk7_0))|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_31, c_0_87])).
% 0.19/0.49  cnf(c_0_97, negated_conjecture, (k1_funct_1(esk7_0,esk4_2(esk7_0,k1_xboole_0))=esk3_2(esk7_0,k1_xboole_0)|esk7_0=k1_xboole_0), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_76]), c_0_93])).
% 0.19/0.49  cnf(c_0_98, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk3_2(esk7_0,k1_xboole_0),X1)|r2_hidden(esk4_2(esk7_0,k1_xboole_0),X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_84]), c_0_76])).
% 0.19/0.49  cnf(c_0_99, negated_conjecture, (r2_hidden(esk4_2(esk7_0,k1_xboole_0),k1_relat_1(esk7_0))|r2_hidden(esk3_2(esk7_0,k1_xboole_0),X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_84]), c_0_76])).
% 0.19/0.49  cnf(c_0_100, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk3_2(esk7_0,k1_xboole_0),k2_relat_1(esk7_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_98])).
% 0.19/0.49  cnf(c_0_101, negated_conjecture, (r2_hidden(k1_funct_1(esk7_0,esk4_2(esk7_0,k1_xboole_0)),k2_relat_1(esk7_0))|r2_hidden(esk3_2(esk7_0,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_31, c_0_99])).
% 0.19/0.49  cnf(c_0_102, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk3_2(esk7_0,k1_xboole_0),X1)|~r1_tarski(k2_relat_1(esk7_0),X1)), inference(spm,[status(thm)],[c_0_47, c_0_100])).
% 0.19/0.49  cnf(c_0_103, negated_conjecture, (r1_tarski(k2_relat_1(esk7_0),k1_xboole_0)), inference(rw,[status(thm)],[c_0_53, c_0_67])).
% 0.19/0.49  cnf(c_0_104, negated_conjecture, (r2_hidden(k1_funct_1(esk7_0,esk4_2(esk7_0,k1_xboole_0)),X1)|r2_hidden(esk3_2(esk7_0,k1_xboole_0),X2)|~r1_tarski(k2_relat_1(esk7_0),X1)), inference(spm,[status(thm)],[c_0_47, c_0_101])).
% 0.19/0.49  cnf(c_0_105, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk3_2(esk7_0,k1_xboole_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_102, c_0_103])).
% 0.19/0.49  cnf(c_0_106, negated_conjecture, (r2_hidden(k1_funct_1(esk7_0,esk4_2(esk7_0,k1_xboole_0)),k1_xboole_0)|r2_hidden(esk3_2(esk7_0,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_104, c_0_103])).
% 0.19/0.49  cnf(c_0_107, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk3_2(esk7_0,k1_xboole_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_105]), c_0_84])])).
% 0.19/0.49  cnf(c_0_108, negated_conjecture, (k1_funct_1(esk7_0,esk8_1(X1))=X1|~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[c_0_33, c_0_67])).
% 0.19/0.49  cnf(c_0_109, negated_conjecture, (r2_hidden(k1_funct_1(esk7_0,esk4_2(esk7_0,k1_xboole_0)),X1)|r2_hidden(esk3_2(esk7_0,k1_xboole_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_106]), c_0_84])])).
% 0.19/0.49  cnf(c_0_110, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk8_1(esk3_2(esk7_0,k1_xboole_0)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_75, c_0_107])).
% 0.19/0.49  cnf(c_0_111, negated_conjecture, (k1_funct_1(esk7_0,esk8_1(k1_funct_1(esk7_0,esk4_2(esk7_0,k1_xboole_0))))=k1_funct_1(esk7_0,esk4_2(esk7_0,k1_xboole_0))|r2_hidden(esk3_2(esk7_0,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_108, c_0_109])).
% 0.19/0.49  cnf(c_0_112, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk8_1(esk3_2(esk7_0,k1_xboole_0)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_110]), c_0_84])])).
% 0.19/0.49  cnf(c_0_113, negated_conjecture, (k1_funct_1(esk7_0,esk8_1(k1_funct_1(esk7_0,esk4_2(esk7_0,k1_xboole_0))))=k1_funct_1(esk7_0,esk4_2(esk7_0,k1_xboole_0))|k1_funct_1(esk7_0,esk8_1(esk3_2(esk7_0,k1_xboole_0)))=esk3_2(esk7_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_108, c_0_111])).
% 0.19/0.49  cnf(c_0_114, plain, (r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X1))|~r2_hidden(X3,X2)|X2!=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.49  cnf(c_0_115, negated_conjecture, (X1=k2_relat_1(esk7_0)|esk7_0=k1_xboole_0|esk3_2(esk7_0,X1)!=k1_funct_1(esk7_0,esk8_1(esk3_2(esk7_0,k1_xboole_0)))|~r2_hidden(esk3_2(esk7_0,X1),X1)), inference(spm,[status(thm)],[c_0_46, c_0_112])).
% 0.19/0.49  cnf(c_0_116, negated_conjecture, (k1_funct_1(esk7_0,esk8_1(esk3_2(esk7_0,k1_xboole_0)))=esk3_2(esk7_0,k1_xboole_0)|esk7_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_113, c_0_97])).
% 0.19/0.49  cnf(c_0_117, plain, (r2_hidden(esk2_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_114])).
% 0.19/0.49  cnf(c_0_118, plain, (X1=k1_funct_1(X2,esk2_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.49  cnf(c_0_119, negated_conjecture, (esk7_0=k1_xboole_0), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_107]), c_0_76]), c_0_116])).
% 0.19/0.49  cnf(c_0_120, negated_conjecture, (r2_hidden(esk2_3(esk7_0,k2_relat_1(esk7_0),X1),k1_relat_1(esk7_0))|~r2_hidden(X1,k2_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_23]), c_0_24])])).
% 0.19/0.49  cnf(c_0_121, plain, (k1_funct_1(X1,esk2_3(X1,k2_relat_1(X1),X2))=X2|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_118])).
% 0.19/0.49  cnf(c_0_122, negated_conjecture, (v1_funct_1(k1_xboole_0)), inference(rw,[status(thm)],[c_0_23, c_0_119])).
% 0.19/0.49  cnf(c_0_123, negated_conjecture, (v1_relat_1(k1_xboole_0)), inference(rw,[status(thm)],[c_0_24, c_0_119])).
% 0.19/0.49  cnf(c_0_124, negated_conjecture, (k1_funct_1(esk7_0,esk4_2(esk7_0,k1_xboole_0))=esk3_2(esk7_0,k1_xboole_0)|r2_hidden(esk2_3(esk7_0,k2_relat_1(esk7_0),esk3_2(esk7_0,k1_xboole_0)),k1_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_120, c_0_92])).
% 0.19/0.49  cnf(c_0_125, negated_conjecture, (k1_funct_1(esk7_0,esk2_3(esk7_0,k2_relat_1(esk7_0),X1))=X1|~r2_hidden(X1,k2_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_23]), c_0_24])])).
% 0.19/0.49  cnf(c_0_126, negated_conjecture, (X1=k2_relat_1(k1_xboole_0)|esk3_2(k1_xboole_0,X1)!=k1_funct_1(k1_xboole_0,X2)|~r2_hidden(esk3_2(k1_xboole_0,X1),X1)|~r2_hidden(X2,k1_relat_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_122]), c_0_123])])).
% 0.19/0.49  cnf(c_0_127, negated_conjecture, (k1_funct_1(k1_xboole_0,esk4_2(k1_xboole_0,k1_xboole_0))=esk3_2(k1_xboole_0,k1_xboole_0)|r2_hidden(esk2_3(k1_xboole_0,k2_relat_1(k1_xboole_0),esk3_2(k1_xboole_0,k1_xboole_0)),k1_relat_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_124, c_0_119]), c_0_119]), c_0_119]), c_0_119]), c_0_119]), c_0_119]), c_0_119])).
% 0.19/0.49  cnf(c_0_128, negated_conjecture, (k1_funct_1(esk7_0,esk2_3(esk7_0,k2_relat_1(esk7_0),esk3_2(esk7_0,k1_xboole_0)))=esk3_2(esk7_0,k1_xboole_0)|k1_funct_1(esk7_0,esk4_2(esk7_0,k1_xboole_0))=esk3_2(esk7_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_125, c_0_92])).
% 0.19/0.49  cnf(c_0_129, negated_conjecture, (k1_funct_1(k1_xboole_0,esk4_2(k1_xboole_0,k1_xboole_0))=esk3_2(k1_xboole_0,k1_xboole_0)|X1=k2_relat_1(k1_xboole_0)|esk3_2(k1_xboole_0,X1)!=k1_funct_1(k1_xboole_0,esk2_3(k1_xboole_0,k2_relat_1(k1_xboole_0),esk3_2(k1_xboole_0,k1_xboole_0)))|~r2_hidden(esk3_2(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_126, c_0_127])).
% 0.19/0.49  cnf(c_0_130, negated_conjecture, (k1_funct_1(k1_xboole_0,esk4_2(k1_xboole_0,k1_xboole_0))=esk3_2(k1_xboole_0,k1_xboole_0)|r2_hidden(esk3_2(k1_xboole_0,k1_xboole_0),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92, c_0_119]), c_0_119]), c_0_119]), c_0_119])).
% 0.19/0.49  cnf(c_0_131, negated_conjecture, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_76, c_0_119])).
% 0.19/0.49  cnf(c_0_132, negated_conjecture, (k1_funct_1(k1_xboole_0,esk2_3(k1_xboole_0,k2_relat_1(k1_xboole_0),esk3_2(k1_xboole_0,k1_xboole_0)))=esk3_2(k1_xboole_0,k1_xboole_0)|k1_funct_1(k1_xboole_0,esk4_2(k1_xboole_0,k1_xboole_0))=esk3_2(k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_128, c_0_119]), c_0_119]), c_0_119]), c_0_119]), c_0_119]), c_0_119]), c_0_119]), c_0_119])).
% 0.19/0.49  cnf(c_0_133, negated_conjecture, (k1_funct_1(k1_xboole_0,esk4_2(k1_xboole_0,k1_xboole_0))=esk3_2(k1_xboole_0,k1_xboole_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_129, c_0_130]), c_0_131]), c_0_132])).
% 0.19/0.49  cnf(c_0_134, negated_conjecture, (r2_hidden(esk4_2(k1_xboole_0,k1_xboole_0),k1_relat_1(k1_xboole_0))|r2_hidden(esk3_2(k1_xboole_0,k1_xboole_0),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_99, c_0_119]), c_0_119]), c_0_119])).
% 0.19/0.49  cnf(c_0_135, negated_conjecture, (r2_hidden(esk3_2(k1_xboole_0,k1_xboole_0),k2_relat_1(k1_xboole_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_133]), c_0_122]), c_0_123])]), c_0_134])).
% 0.19/0.49  cnf(c_0_136, negated_conjecture, (r2_hidden(esk3_2(k1_xboole_0,k1_xboole_0),X1)|~r1_tarski(k2_relat_1(k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_47, c_0_135])).
% 0.19/0.49  cnf(c_0_137, negated_conjecture, (r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0)), inference(rw,[status(thm)],[c_0_103, c_0_119])).
% 0.19/0.49  cnf(c_0_138, negated_conjecture, (r2_hidden(esk3_2(k1_xboole_0,k1_xboole_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_136, c_0_137])).
% 0.19/0.49  cnf(c_0_139, negated_conjecture, (r2_hidden(esk2_3(k1_xboole_0,k2_relat_1(k1_xboole_0),X1),k1_relat_1(k1_xboole_0))|~r2_hidden(X1,k2_relat_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_122]), c_0_123])])).
% 0.19/0.49  cnf(c_0_140, negated_conjecture, (r2_hidden(esk3_2(k1_xboole_0,k1_xboole_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_138]), c_0_84])])).
% 0.19/0.49  cnf(c_0_141, negated_conjecture, (r2_hidden(esk2_3(k1_xboole_0,k2_relat_1(k1_xboole_0),esk3_2(k1_xboole_0,k1_xboole_0)),k1_relat_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_139, c_0_140])).
% 0.19/0.49  cnf(c_0_142, negated_conjecture, (X1=k2_relat_1(k1_xboole_0)|esk3_2(k1_xboole_0,X1)!=k1_funct_1(k1_xboole_0,esk2_3(k1_xboole_0,k2_relat_1(k1_xboole_0),esk3_2(k1_xboole_0,k1_xboole_0)))|~r2_hidden(esk3_2(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_126, c_0_141])).
% 0.19/0.49  cnf(c_0_143, negated_conjecture, (k1_funct_1(k1_xboole_0,esk2_3(k1_xboole_0,k2_relat_1(k1_xboole_0),X1))=X1|~r2_hidden(X1,k2_relat_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_122]), c_0_123])])).
% 0.19/0.49  cnf(c_0_144, negated_conjecture, (k1_funct_1(k1_xboole_0,esk2_3(k1_xboole_0,k2_relat_1(k1_xboole_0),esk3_2(k1_xboole_0,k1_xboole_0)))!=esk3_2(k1_xboole_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_142, c_0_140]), c_0_131])).
% 0.19/0.49  cnf(c_0_145, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_140]), c_0_144]), ['proof']).
% 0.19/0.49  # SZS output end CNFRefutation
% 0.19/0.49  # Proof object total steps             : 146
% 0.19/0.49  # Proof object clause steps            : 125
% 0.19/0.49  # Proof object formula steps           : 21
% 0.19/0.49  # Proof object conjectures             : 107
% 0.19/0.49  # Proof object clause conjectures      : 104
% 0.19/0.49  # Proof object formula conjectures     : 3
% 0.19/0.49  # Proof object initial clauses used    : 22
% 0.19/0.49  # Proof object initial formulas used   : 10
% 0.19/0.49  # Proof object generating inferences   : 80
% 0.19/0.49  # Proof object simplifying inferences  : 111
% 0.19/0.49  # Training examples: 0 positive, 0 negative
% 0.19/0.49  # Parsed axioms                        : 10
% 0.19/0.49  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.49  # Initial clauses                      : 29
% 0.19/0.49  # Removed in clause preprocessing      : 0
% 0.19/0.49  # Initial clauses in saturation        : 29
% 0.19/0.49  # Processed clauses                    : 1123
% 0.19/0.49  # ...of these trivial                  : 19
% 0.19/0.49  # ...subsumed                          : 393
% 0.19/0.49  # ...remaining for further processing  : 710
% 0.19/0.49  # Other redundant clauses eliminated   : 14
% 0.19/0.49  # Clauses deleted for lack of memory   : 0
% 0.19/0.49  # Backward-subsumed                    : 223
% 0.19/0.49  # Backward-rewritten                   : 327
% 0.19/0.49  # Generated clauses                    : 3084
% 0.19/0.49  # ...of the previous two non-trivial   : 3190
% 0.19/0.49  # Contextual simplify-reflections      : 14
% 0.19/0.49  # Paramodulations                      : 3042
% 0.19/0.49  # Factorizations                       : 27
% 0.19/0.49  # Equation resolutions                 : 14
% 0.19/0.49  # Propositional unsat checks           : 0
% 0.19/0.49  #    Propositional check models        : 0
% 0.19/0.49  #    Propositional check unsatisfiable : 0
% 0.19/0.49  #    Propositional clauses             : 0
% 0.19/0.49  #    Propositional clauses after purity: 0
% 0.19/0.49  #    Propositional unsat core size     : 0
% 0.19/0.49  #    Propositional preprocessing time  : 0.000
% 0.19/0.49  #    Propositional encoding time       : 0.000
% 0.19/0.49  #    Propositional solver time         : 0.000
% 0.19/0.49  #    Success case prop preproc time    : 0.000
% 0.19/0.49  #    Success case prop encoding time   : 0.000
% 0.19/0.49  #    Success case prop solver time     : 0.000
% 0.19/0.49  # Current number of processed clauses  : 121
% 0.19/0.49  #    Positive orientable unit clauses  : 23
% 0.19/0.49  #    Positive unorientable unit clauses: 0
% 0.19/0.49  #    Negative unit clauses             : 5
% 0.19/0.49  #    Non-unit-clauses                  : 93
% 0.19/0.49  # Current number of unprocessed clauses: 546
% 0.19/0.49  # ...number of literals in the above   : 1988
% 0.19/0.49  # Current number of archived formulas  : 0
% 0.19/0.49  # Current number of archived clauses   : 582
% 0.19/0.49  # Clause-clause subsumption calls (NU) : 22111
% 0.19/0.49  # Rec. Clause-clause subsumption calls : 7253
% 0.19/0.49  # Non-unit clause-clause subsumptions  : 619
% 0.19/0.49  # Unit Clause-clause subsumption calls : 420
% 0.19/0.49  # Rewrite failures with RHS unbound    : 0
% 0.19/0.49  # BW rewrite match attempts            : 28
% 0.19/0.49  # BW rewrite match successes           : 15
% 0.19/0.49  # Condensation attempts                : 0
% 0.19/0.49  # Condensation successes               : 0
% 0.19/0.49  # Termbank termtop insertions          : 65587
% 0.19/0.49  
% 0.19/0.49  # -------------------------------------------------
% 0.19/0.49  # User time                : 0.141 s
% 0.19/0.49  # System time              : 0.007 s
% 0.19/0.49  # Total time               : 0.148 s
% 0.19/0.49  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
