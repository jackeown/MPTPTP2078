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
% DateTime   : Thu Dec  3 10:58:37 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 123 expanded)
%              Number of clauses        :   32 (  52 expanded)
%              Number of leaves         :   14 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :  154 ( 385 expanded)
%              Number of equality atoms :   32 (  78 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t50_relset_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
             => ~ ( k2_relset_1(X2,X1,X3) != k1_xboole_0
                  & ! [X4] :
                      ( m1_subset_1(X4,X2)
                     => ~ r2_hidden(X4,k1_relset_1(X2,X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t65_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k1_relat_1(X1) = k1_xboole_0
      <=> k2_relat_1(X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(c_0_14,plain,(
    ! [X21,X22] :
      ( ~ v1_relat_1(X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(X21))
      | v1_relat_1(X22) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_15,plain,(
    ! [X25,X26] : v1_relat_1(k2_zfmisc_1(X25,X26)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
               => ~ ( k2_relset_1(X2,X1,X3) != k1_xboole_0
                    & ! [X4] :
                        ( m1_subset_1(X4,X2)
                       => ~ r2_hidden(X4,k1_relset_1(X2,X1,X3)) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t50_relset_1])).

cnf(c_0_17,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,negated_conjecture,(
    ! [X42] :
      ( ~ v1_xboole_0(esk3_0)
      & ~ v1_xboole_0(esk4_0)
      & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))
      & k2_relset_1(esk4_0,esk3_0,esk5_0) != k1_xboole_0
      & ( ~ m1_subset_1(X42,esk4_0)
        | ~ r2_hidden(X42,k1_relset_1(esk4_0,esk3_0,esk5_0)) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])])).

fof(c_0_20,plain,(
    ! [X23,X24] :
      ( ( ~ v4_relat_1(X24,X23)
        | r1_tarski(k1_relat_1(X24),X23)
        | ~ v1_relat_1(X24) )
      & ( ~ r1_tarski(k1_relat_1(X24),X23)
        | v4_relat_1(X24,X23)
        | ~ v1_relat_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_21,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_23,plain,(
    ! [X30,X31,X32] :
      ( ( v4_relat_1(X32,X30)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( v5_relat_1(X32,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_24,plain,(
    ! [X9,X10,X11,X12,X13,X14] :
      ( ( ~ r2_hidden(X11,X10)
        | r1_tarski(X11,X9)
        | X10 != k1_zfmisc_1(X9) )
      & ( ~ r1_tarski(X12,X9)
        | r2_hidden(X12,X10)
        | X10 != k1_zfmisc_1(X9) )
      & ( ~ r2_hidden(esk2_2(X13,X14),X14)
        | ~ r1_tarski(esk2_2(X13,X14),X13)
        | X14 = k1_zfmisc_1(X13) )
      & ( r2_hidden(esk2_2(X13,X14),X14)
        | r1_tarski(esk2_2(X13,X14),X13)
        | X14 = k1_zfmisc_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_25,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk5_0),X1)
    | ~ v4_relat_1(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( v4_relat_1(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_22])).

fof(c_0_31,plain,(
    ! [X33,X34,X35] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
      | k1_relset_1(X33,X34,X35) = k1_relat_1(X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_32,plain,(
    ! [X16,X17] :
      ( ~ r2_hidden(X16,X17)
      | m1_subset_1(X16,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk5_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_36,plain,(
    ! [X18,X19,X20] :
      ( ~ r2_hidden(X18,X19)
      | ~ m1_subset_1(X19,k1_zfmisc_1(X20))
      | m1_subset_1(X18,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_37,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(k1_relat_1(esk5_0),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( ~ m1_subset_1(X1,esk4_0)
    | ~ r2_hidden(X1,k1_relset_1(esk4_0,esk3_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_40,negated_conjecture,
    ( k1_relset_1(esk4_0,esk3_0,esk5_0) = k1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_22])).

fof(c_0_41,plain,(
    ! [X36,X37,X38] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
      | k2_relset_1(X36,X37,X38) = k2_relat_1(X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_42,plain,(
    ! [X5,X6] :
      ( ( ~ r2_hidden(esk1_2(X5,X6),X5)
        | ~ r2_hidden(esk1_2(X5,X6),X6)
        | X5 = X6 )
      & ( r2_hidden(esk1_2(X5,X6),X5)
        | r2_hidden(esk1_2(X5,X6),X6)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

cnf(c_0_43,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(k1_relat_1(esk5_0),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( ~ m1_subset_1(X1,esk4_0)
    | ~ r2_hidden(X1,k1_relat_1(esk5_0)) ),
    inference(rw,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_47,plain,(
    ! [X28,X29] :
      ( ~ r2_hidden(X28,X29)
      | ~ r1_tarski(X29,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_48,plain,(
    ! [X8] : r1_tarski(k1_xboole_0,X8) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_49,plain,(
    ! [X27] :
      ( ( k1_relat_1(X27) != k1_xboole_0
        | k2_relat_1(X27) = k1_xboole_0
        | ~ v1_relat_1(X27) )
      & ( k2_relat_1(X27) != k1_xboole_0
        | k1_relat_1(X27) = k1_xboole_0
        | ~ v1_relat_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).

cnf(c_0_50,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r2_hidden(esk1_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_51,negated_conjecture,
    ( ~ r2_hidden(X1,k1_relat_1(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( k2_relset_1(esk4_0,esk3_0,esk5_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_53,negated_conjecture,
    ( k2_relset_1(esk4_0,esk3_0,esk5_0) = k2_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_22])).

cnf(c_0_54,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_55,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_57,negated_conjecture,
    ( X1 = k1_relat_1(esk5_0)
    | r2_hidden(esk1_2(X1,k1_relat_1(esk5_0)),X1) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_50]),c_0_40]),c_0_40]),c_0_40]),c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( k2_relat_1(esk5_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_59,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_26])]),c_0_58])]),c_0_59]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:04:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.42  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S074A
% 0.20/0.42  # and selection function SelectCQIArEqFirst.
% 0.20/0.42  #
% 0.20/0.42  # Preprocessing time       : 0.027 s
% 0.20/0.42  # Presaturation interreduction done
% 0.20/0.42  
% 0.20/0.42  # Proof found!
% 0.20/0.42  # SZS status Theorem
% 0.20/0.42  # SZS output start CNFRefutation
% 0.20/0.42  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.20/0.42  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.20/0.42  fof(t50_relset_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>~((k2_relset_1(X2,X1,X3)!=k1_xboole_0&![X4]:(m1_subset_1(X4,X2)=>~(r2_hidden(X4,k1_relset_1(X2,X1,X3))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_relset_1)).
% 0.20/0.42  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 0.20/0.42  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.20/0.42  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.20/0.42  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.20/0.42  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 0.20/0.42  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.20/0.42  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.20/0.42  fof(t2_tarski, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)<=>r2_hidden(X3,X2))=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 0.20/0.42  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.20/0.42  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.42  fof(t65_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k1_relat_1(X1)=k1_xboole_0<=>k2_relat_1(X1)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 0.20/0.42  fof(c_0_14, plain, ![X21, X22]:(~v1_relat_1(X21)|(~m1_subset_1(X22,k1_zfmisc_1(X21))|v1_relat_1(X22))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.20/0.42  fof(c_0_15, plain, ![X25, X26]:v1_relat_1(k2_zfmisc_1(X25,X26)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.20/0.42  fof(c_0_16, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>~((k2_relset_1(X2,X1,X3)!=k1_xboole_0&![X4]:(m1_subset_1(X4,X2)=>~(r2_hidden(X4,k1_relset_1(X2,X1,X3)))))))))), inference(assume_negation,[status(cth)],[t50_relset_1])).
% 0.20/0.42  cnf(c_0_17, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.42  cnf(c_0_18, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.42  fof(c_0_19, negated_conjecture, ![X42]:(~v1_xboole_0(esk3_0)&(~v1_xboole_0(esk4_0)&(m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))&(k2_relset_1(esk4_0,esk3_0,esk5_0)!=k1_xboole_0&(~m1_subset_1(X42,esk4_0)|~r2_hidden(X42,k1_relset_1(esk4_0,esk3_0,esk5_0))))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])])).
% 0.20/0.42  fof(c_0_20, plain, ![X23, X24]:((~v4_relat_1(X24,X23)|r1_tarski(k1_relat_1(X24),X23)|~v1_relat_1(X24))&(~r1_tarski(k1_relat_1(X24),X23)|v4_relat_1(X24,X23)|~v1_relat_1(X24))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.20/0.42  cnf(c_0_21, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.42  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.42  fof(c_0_23, plain, ![X30, X31, X32]:((v4_relat_1(X32,X30)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))&(v5_relat_1(X32,X31)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.20/0.42  fof(c_0_24, plain, ![X9, X10, X11, X12, X13, X14]:(((~r2_hidden(X11,X10)|r1_tarski(X11,X9)|X10!=k1_zfmisc_1(X9))&(~r1_tarski(X12,X9)|r2_hidden(X12,X10)|X10!=k1_zfmisc_1(X9)))&((~r2_hidden(esk2_2(X13,X14),X14)|~r1_tarski(esk2_2(X13,X14),X13)|X14=k1_zfmisc_1(X13))&(r2_hidden(esk2_2(X13,X14),X14)|r1_tarski(esk2_2(X13,X14),X13)|X14=k1_zfmisc_1(X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.20/0.42  cnf(c_0_25, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.42  cnf(c_0_26, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.42  cnf(c_0_27, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.42  cnf(c_0_28, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.42  cnf(c_0_29, negated_conjecture, (r1_tarski(k1_relat_1(esk5_0),X1)|~v4_relat_1(esk5_0,X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.42  cnf(c_0_30, negated_conjecture, (v4_relat_1(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_27, c_0_22])).
% 0.20/0.42  fof(c_0_31, plain, ![X33, X34, X35]:(~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|k1_relset_1(X33,X34,X35)=k1_relat_1(X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.20/0.42  fof(c_0_32, plain, ![X16, X17]:(~r2_hidden(X16,X17)|m1_subset_1(X16,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.20/0.42  cnf(c_0_33, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_28])).
% 0.20/0.42  cnf(c_0_34, negated_conjecture, (r1_tarski(k1_relat_1(esk5_0),esk4_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.42  cnf(c_0_35, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.42  fof(c_0_36, plain, ![X18, X19, X20]:(~r2_hidden(X18,X19)|~m1_subset_1(X19,k1_zfmisc_1(X20))|m1_subset_1(X18,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.20/0.42  cnf(c_0_37, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.42  cnf(c_0_38, negated_conjecture, (r2_hidden(k1_relat_1(esk5_0),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.42  cnf(c_0_39, negated_conjecture, (~m1_subset_1(X1,esk4_0)|~r2_hidden(X1,k1_relset_1(esk4_0,esk3_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.42  cnf(c_0_40, negated_conjecture, (k1_relset_1(esk4_0,esk3_0,esk5_0)=k1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_35, c_0_22])).
% 0.20/0.42  fof(c_0_41, plain, ![X36, X37, X38]:(~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))|k2_relset_1(X36,X37,X38)=k2_relat_1(X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.20/0.42  fof(c_0_42, plain, ![X5, X6]:((~r2_hidden(esk1_2(X5,X6),X5)|~r2_hidden(esk1_2(X5,X6),X6)|X5=X6)&(r2_hidden(esk1_2(X5,X6),X5)|r2_hidden(esk1_2(X5,X6),X6)|X5=X6)), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).
% 0.20/0.42  cnf(c_0_43, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.42  cnf(c_0_44, negated_conjecture, (m1_subset_1(k1_relat_1(esk5_0),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.42  cnf(c_0_45, negated_conjecture, (~m1_subset_1(X1,esk4_0)|~r2_hidden(X1,k1_relat_1(esk5_0))), inference(rw,[status(thm)],[c_0_39, c_0_40])).
% 0.20/0.42  cnf(c_0_46, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.42  fof(c_0_47, plain, ![X28, X29]:(~r2_hidden(X28,X29)|~r1_tarski(X29,X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.20/0.42  fof(c_0_48, plain, ![X8]:r1_tarski(k1_xboole_0,X8), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.42  fof(c_0_49, plain, ![X27]:((k1_relat_1(X27)!=k1_xboole_0|k2_relat_1(X27)=k1_xboole_0|~v1_relat_1(X27))&(k2_relat_1(X27)!=k1_xboole_0|k1_relat_1(X27)=k1_xboole_0|~v1_relat_1(X27))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).
% 0.20/0.42  cnf(c_0_50, plain, (r2_hidden(esk1_2(X1,X2),X1)|r2_hidden(esk1_2(X1,X2),X2)|X1=X2), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.42  cnf(c_0_51, negated_conjecture, (~r2_hidden(X1,k1_relat_1(esk5_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])).
% 0.20/0.42  cnf(c_0_52, negated_conjecture, (k2_relset_1(esk4_0,esk3_0,esk5_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.42  cnf(c_0_53, negated_conjecture, (k2_relset_1(esk4_0,esk3_0,esk5_0)=k2_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_46, c_0_22])).
% 0.20/0.42  cnf(c_0_54, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.42  cnf(c_0_55, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.42  cnf(c_0_56, plain, (k2_relat_1(X1)=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.42  cnf(c_0_57, negated_conjecture, (X1=k1_relat_1(esk5_0)|r2_hidden(esk1_2(X1,k1_relat_1(esk5_0)),X1)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_50]), c_0_40]), c_0_40]), c_0_40]), c_0_51])).
% 0.20/0.42  cnf(c_0_58, negated_conjecture, (k2_relat_1(esk5_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_52, c_0_53])).
% 0.20/0.42  cnf(c_0_59, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.20/0.42  cnf(c_0_60, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_26])]), c_0_58])]), c_0_59]), ['proof']).
% 0.20/0.42  # SZS output end CNFRefutation
% 0.20/0.42  # Proof object total steps             : 61
% 0.20/0.42  # Proof object clause steps            : 32
% 0.20/0.42  # Proof object formula steps           : 29
% 0.20/0.42  # Proof object conjectures             : 19
% 0.20/0.42  # Proof object clause conjectures      : 16
% 0.20/0.42  # Proof object formula conjectures     : 3
% 0.20/0.42  # Proof object initial clauses used    : 16
% 0.20/0.42  # Proof object initial formulas used   : 14
% 0.20/0.42  # Proof object generating inferences   : 13
% 0.20/0.42  # Proof object simplifying inferences  : 13
% 0.20/0.42  # Training examples: 0 positive, 0 negative
% 0.20/0.42  # Parsed axioms                        : 14
% 0.20/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.42  # Initial clauses                      : 25
% 0.20/0.42  # Removed in clause preprocessing      : 0
% 0.20/0.42  # Initial clauses in saturation        : 25
% 0.20/0.42  # Processed clauses                    : 292
% 0.20/0.42  # ...of these trivial                  : 16
% 0.20/0.42  # ...subsumed                          : 48
% 0.20/0.42  # ...remaining for further processing  : 228
% 0.20/0.42  # Other redundant clauses eliminated   : 11
% 0.20/0.42  # Clauses deleted for lack of memory   : 0
% 0.20/0.42  # Backward-subsumed                    : 0
% 0.20/0.42  # Backward-rewritten                   : 10
% 0.20/0.42  # Generated clauses                    : 2668
% 0.20/0.42  # ...of the previous two non-trivial   : 2370
% 0.20/0.42  # Contextual simplify-reflections      : 1
% 0.20/0.42  # Paramodulations                      : 2657
% 0.20/0.42  # Factorizations                       : 0
% 0.20/0.42  # Equation resolutions                 : 11
% 0.20/0.42  # Propositional unsat checks           : 0
% 0.20/0.42  #    Propositional check models        : 0
% 0.20/0.42  #    Propositional check unsatisfiable : 0
% 0.20/0.42  #    Propositional clauses             : 0
% 0.20/0.42  #    Propositional clauses after purity: 0
% 0.20/0.42  #    Propositional unsat core size     : 0
% 0.20/0.42  #    Propositional preprocessing time  : 0.000
% 0.20/0.42  #    Propositional encoding time       : 0.000
% 0.20/0.42  #    Propositional solver time         : 0.000
% 0.20/0.42  #    Success case prop preproc time    : 0.000
% 0.20/0.42  #    Success case prop encoding time   : 0.000
% 0.20/0.42  #    Success case prop solver time     : 0.000
% 0.20/0.42  # Current number of processed clauses  : 191
% 0.20/0.42  #    Positive orientable unit clauses  : 81
% 0.20/0.42  #    Positive unorientable unit clauses: 0
% 0.20/0.42  #    Negative unit clauses             : 12
% 0.20/0.42  #    Non-unit-clauses                  : 98
% 0.20/0.42  # Current number of unprocessed clauses: 1870
% 0.20/0.42  # ...number of literals in the above   : 5508
% 0.20/0.42  # Current number of archived formulas  : 0
% 0.20/0.42  # Current number of archived clauses   : 35
% 0.20/0.42  # Clause-clause subsumption calls (NU) : 2022
% 0.20/0.42  # Rec. Clause-clause subsumption calls : 1274
% 0.20/0.42  # Non-unit clause-clause subsumptions  : 41
% 0.20/0.42  # Unit Clause-clause subsumption calls : 402
% 0.20/0.42  # Rewrite failures with RHS unbound    : 0
% 0.20/0.42  # BW rewrite match attempts            : 131
% 0.20/0.42  # BW rewrite match successes           : 9
% 0.20/0.42  # Condensation attempts                : 0
% 0.20/0.42  # Condensation successes               : 0
% 0.20/0.42  # Termbank termtop insertions          : 29991
% 0.20/0.42  
% 0.20/0.42  # -------------------------------------------------
% 0.20/0.42  # User time                : 0.058 s
% 0.20/0.42  # System time              : 0.009 s
% 0.20/0.42  # Total time               : 0.066 s
% 0.20/0.42  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
