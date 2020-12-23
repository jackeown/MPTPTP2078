%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:58:45 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 160 expanded)
%              Number of clauses        :   26 (  66 expanded)
%              Number of leaves         :    8 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :  176 ( 892 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t53_relset_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ~ v1_xboole_0(X3)
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
                 => ! [X5] :
                      ( m1_subset_1(X5,X1)
                     => ( r2_hidden(X5,k8_relset_1(X1,X3,X4,X2))
                      <=> ? [X6] :
                            ( m1_subset_1(X6,X3)
                            & r2_hidden(k4_tarski(X5,X6),X4)
                            & r2_hidden(X6,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t166_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k10_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k2_relat_1(X3))
            & r2_hidden(k4_tarski(X1,X4),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(t202_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1) )
     => ! [X3] :
          ( r2_hidden(X3,k2_relat_1(X2))
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t202_relat_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(d14_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k10_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(k4_tarski(X4,X5),X1)
                  & r2_hidden(X5,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

fof(redefinition_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k8_relset_1(X1,X2,X3,X4) = k10_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ~ v1_xboole_0(X3)
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
                   => ! [X5] :
                        ( m1_subset_1(X5,X1)
                       => ( r2_hidden(X5,k8_relset_1(X1,X3,X4,X2))
                        <=> ? [X6] :
                              ( m1_subset_1(X6,X3)
                              & r2_hidden(k4_tarski(X5,X6),X4)
                              & r2_hidden(X6,X2) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t53_relset_1])).

fof(c_0_9,plain,(
    ! [X29,X30,X31] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
      | v1_relat_1(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_10,negated_conjecture,(
    ! [X44] :
      ( ~ v1_xboole_0(esk5_0)
      & ~ v1_xboole_0(esk6_0)
      & ~ v1_xboole_0(esk7_0)
      & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk7_0)))
      & m1_subset_1(esk9_0,esk5_0)
      & ( ~ r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))
        | ~ m1_subset_1(X44,esk7_0)
        | ~ r2_hidden(k4_tarski(esk9_0,X44),esk8_0)
        | ~ r2_hidden(X44,esk6_0) )
      & ( m1_subset_1(esk10_0,esk7_0)
        | r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0)) )
      & ( r2_hidden(k4_tarski(esk9_0,esk10_0),esk8_0)
        | r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0)) )
      & ( r2_hidden(esk10_0,esk6_0)
        | r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])])).

fof(c_0_11,plain,(
    ! [X21,X22,X23,X25] :
      ( ( r2_hidden(esk4_3(X21,X22,X23),k2_relat_1(X23))
        | ~ r2_hidden(X21,k10_relat_1(X23,X22))
        | ~ v1_relat_1(X23) )
      & ( r2_hidden(k4_tarski(X21,esk4_3(X21,X22,X23)),X23)
        | ~ r2_hidden(X21,k10_relat_1(X23,X22))
        | ~ v1_relat_1(X23) )
      & ( r2_hidden(esk4_3(X21,X22,X23),X22)
        | ~ r2_hidden(X21,k10_relat_1(X23,X22))
        | ~ v1_relat_1(X23) )
      & ( ~ r2_hidden(X25,k2_relat_1(X23))
        | ~ r2_hidden(k4_tarski(X21,X25),X23)
        | ~ r2_hidden(X25,X22)
        | r2_hidden(X21,k10_relat_1(X23,X22))
        | ~ v1_relat_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).

cnf(c_0_12,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( ~ r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))
    | ~ m1_subset_1(X1,esk7_0)
    | ~ r2_hidden(k4_tarski(esk9_0,X1),esk8_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( r2_hidden(k4_tarski(X1,esk4_3(X1,X2,X3)),X3)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

fof(c_0_17,plain,(
    ! [X7,X8] :
      ( ~ r2_hidden(X7,X8)
      | m1_subset_1(X7,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

fof(c_0_18,plain,(
    ! [X26,X27,X28] :
      ( ~ v1_relat_1(X27)
      | ~ v5_relat_1(X27,X26)
      | ~ r2_hidden(X28,k2_relat_1(X27))
      | r2_hidden(X28,X26) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t202_relat_1])])])).

fof(c_0_19,plain,(
    ! [X32,X33,X34] :
      ( ( v4_relat_1(X34,X32)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( v5_relat_1(X34,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_20,negated_conjecture,
    ( ~ m1_subset_1(esk4_3(esk9_0,X1,esk8_0),esk7_0)
    | ~ r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))
    | ~ r2_hidden(esk4_3(esk9_0,X1,esk8_0),esk6_0)
    | ~ r2_hidden(esk9_0,k10_relat_1(esk8_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])])).

cnf(c_0_21,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( r2_hidden(X3,X2)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2)
    | ~ r2_hidden(X3,k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),k2_relat_1(X3))
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_24,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,plain,(
    ! [X9,X10,X11,X12,X14,X15,X16,X17,X19] :
      ( ( r2_hidden(k4_tarski(X12,esk1_4(X9,X10,X11,X12)),X9)
        | ~ r2_hidden(X12,X11)
        | X11 != k10_relat_1(X9,X10)
        | ~ v1_relat_1(X9) )
      & ( r2_hidden(esk1_4(X9,X10,X11,X12),X10)
        | ~ r2_hidden(X12,X11)
        | X11 != k10_relat_1(X9,X10)
        | ~ v1_relat_1(X9) )
      & ( ~ r2_hidden(k4_tarski(X14,X15),X9)
        | ~ r2_hidden(X15,X10)
        | r2_hidden(X14,X11)
        | X11 != k10_relat_1(X9,X10)
        | ~ v1_relat_1(X9) )
      & ( ~ r2_hidden(esk2_3(X9,X16,X17),X17)
        | ~ r2_hidden(k4_tarski(esk2_3(X9,X16,X17),X19),X9)
        | ~ r2_hidden(X19,X16)
        | X17 = k10_relat_1(X9,X16)
        | ~ v1_relat_1(X9) )
      & ( r2_hidden(k4_tarski(esk2_3(X9,X16,X17),esk3_3(X9,X16,X17)),X9)
        | r2_hidden(esk2_3(X9,X16,X17),X17)
        | X17 = k10_relat_1(X9,X16)
        | ~ v1_relat_1(X9) )
      & ( r2_hidden(esk3_3(X9,X16,X17),X16)
        | r2_hidden(esk2_3(X9,X16,X17),X17)
        | X17 = k10_relat_1(X9,X16)
        | ~ v1_relat_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).

cnf(c_0_26,negated_conjecture,
    ( ~ r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))
    | ~ r2_hidden(esk4_3(esk9_0,X1,esk8_0),esk6_0)
    | ~ r2_hidden(esk4_3(esk9_0,X1,esk8_0),esk7_0)
    | ~ r2_hidden(esk9_0,k10_relat_1(esk8_0,X1)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_28,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X4)
    | ~ v5_relat_1(X3,X4)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( v5_relat_1(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_13])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | X5 != k10_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(k4_tarski(esk9_0,esk10_0),esk8_0)
    | r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_32,negated_conjecture,
    ( ~ r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))
    | ~ r2_hidden(esk4_3(esk9_0,esk6_0,esk8_0),esk7_0)
    | ~ r2_hidden(esk9_0,k10_relat_1(esk8_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_16])])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk4_3(X1,X2,esk8_0),esk7_0)
    | ~ r2_hidden(X1,k10_relat_1(esk8_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_16])])).

fof(c_0_34,plain,(
    ! [X35,X36,X37,X38] :
      ( ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
      | k8_relset_1(X35,X36,X37,X38) = k10_relat_1(X37,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))
    | r2_hidden(esk9_0,X1)
    | X1 != k10_relat_1(esk8_0,X2)
    | ~ r2_hidden(esk10_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_16])])).

cnf(c_0_36,negated_conjecture,
    ( ~ r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))
    | ~ r2_hidden(esk9_0,k10_relat_1(esk8_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))
    | r2_hidden(esk9_0,k10_relat_1(esk8_0,X1))
    | ~ r2_hidden(esk10_0,X1) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk10_0,esk6_0)
    | r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_40,negated_conjecture,
    ( ~ r2_hidden(esk9_0,k10_relat_1(esk8_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_13])])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_37]),c_0_13])]),c_0_40]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:12:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.37  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.20/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.37  #
% 0.20/0.37  # Preprocessing time       : 0.027 s
% 0.20/0.37  # Presaturation interreduction done
% 0.20/0.37  
% 0.20/0.37  # Proof found!
% 0.20/0.37  # SZS status Theorem
% 0.20/0.37  # SZS output start CNFRefutation
% 0.20/0.37  fof(t53_relset_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))=>![X5]:(m1_subset_1(X5,X1)=>(r2_hidden(X5,k8_relset_1(X1,X3,X4,X2))<=>?[X6]:((m1_subset_1(X6,X3)&r2_hidden(k4_tarski(X5,X6),X4))&r2_hidden(X6,X2)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_relset_1)).
% 0.20/0.37  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.20/0.37  fof(t166_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 0.20/0.37  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 0.20/0.37  fof(t202_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v5_relat_1(X2,X1))=>![X3]:(r2_hidden(X3,k2_relat_1(X2))=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t202_relat_1)).
% 0.20/0.37  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.20/0.37  fof(d14_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k10_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:(r2_hidden(k4_tarski(X4,X5),X1)&r2_hidden(X5,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d14_relat_1)).
% 0.20/0.37  fof(redefinition_k8_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k8_relset_1(X1,X2,X3,X4)=k10_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 0.20/0.37  fof(c_0_8, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))=>![X5]:(m1_subset_1(X5,X1)=>(r2_hidden(X5,k8_relset_1(X1,X3,X4,X2))<=>?[X6]:((m1_subset_1(X6,X3)&r2_hidden(k4_tarski(X5,X6),X4))&r2_hidden(X6,X2))))))))), inference(assume_negation,[status(cth)],[t53_relset_1])).
% 0.20/0.37  fof(c_0_9, plain, ![X29, X30, X31]:(~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|v1_relat_1(X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.20/0.37  fof(c_0_10, negated_conjecture, ![X44]:(~v1_xboole_0(esk5_0)&(~v1_xboole_0(esk6_0)&(~v1_xboole_0(esk7_0)&(m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk7_0)))&(m1_subset_1(esk9_0,esk5_0)&((~r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))|(~m1_subset_1(X44,esk7_0)|~r2_hidden(k4_tarski(esk9_0,X44),esk8_0)|~r2_hidden(X44,esk6_0)))&(((m1_subset_1(esk10_0,esk7_0)|r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0)))&(r2_hidden(k4_tarski(esk9_0,esk10_0),esk8_0)|r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))))&(r2_hidden(esk10_0,esk6_0)|r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0)))))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])])).
% 0.20/0.37  fof(c_0_11, plain, ![X21, X22, X23, X25]:((((r2_hidden(esk4_3(X21,X22,X23),k2_relat_1(X23))|~r2_hidden(X21,k10_relat_1(X23,X22))|~v1_relat_1(X23))&(r2_hidden(k4_tarski(X21,esk4_3(X21,X22,X23)),X23)|~r2_hidden(X21,k10_relat_1(X23,X22))|~v1_relat_1(X23)))&(r2_hidden(esk4_3(X21,X22,X23),X22)|~r2_hidden(X21,k10_relat_1(X23,X22))|~v1_relat_1(X23)))&(~r2_hidden(X25,k2_relat_1(X23))|~r2_hidden(k4_tarski(X21,X25),X23)|~r2_hidden(X25,X22)|r2_hidden(X21,k10_relat_1(X23,X22))|~v1_relat_1(X23))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).
% 0.20/0.38  cnf(c_0_12, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  cnf(c_0_14, negated_conjecture, (~r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))|~m1_subset_1(X1,esk7_0)|~r2_hidden(k4_tarski(esk9_0,X1),esk8_0)|~r2_hidden(X1,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  cnf(c_0_15, plain, (r2_hidden(k4_tarski(X1,esk4_3(X1,X2,X3)),X3)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.38  cnf(c_0_16, negated_conjecture, (v1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.20/0.38  fof(c_0_17, plain, ![X7, X8]:(~r2_hidden(X7,X8)|m1_subset_1(X7,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.20/0.38  fof(c_0_18, plain, ![X26, X27, X28]:(~v1_relat_1(X27)|~v5_relat_1(X27,X26)|(~r2_hidden(X28,k2_relat_1(X27))|r2_hidden(X28,X26))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t202_relat_1])])])).
% 0.20/0.38  fof(c_0_19, plain, ![X32, X33, X34]:((v4_relat_1(X34,X32)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))&(v5_relat_1(X34,X33)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.20/0.38  cnf(c_0_20, negated_conjecture, (~m1_subset_1(esk4_3(esk9_0,X1,esk8_0),esk7_0)|~r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))|~r2_hidden(esk4_3(esk9_0,X1,esk8_0),esk6_0)|~r2_hidden(esk9_0,k10_relat_1(esk8_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16])])).
% 0.20/0.38  cnf(c_0_21, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  cnf(c_0_22, plain, (r2_hidden(X3,X2)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)|~r2_hidden(X3,k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_23, plain, (r2_hidden(esk4_3(X1,X2,X3),k2_relat_1(X3))|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.38  cnf(c_0_24, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.38  fof(c_0_25, plain, ![X9, X10, X11, X12, X14, X15, X16, X17, X19]:((((r2_hidden(k4_tarski(X12,esk1_4(X9,X10,X11,X12)),X9)|~r2_hidden(X12,X11)|X11!=k10_relat_1(X9,X10)|~v1_relat_1(X9))&(r2_hidden(esk1_4(X9,X10,X11,X12),X10)|~r2_hidden(X12,X11)|X11!=k10_relat_1(X9,X10)|~v1_relat_1(X9)))&(~r2_hidden(k4_tarski(X14,X15),X9)|~r2_hidden(X15,X10)|r2_hidden(X14,X11)|X11!=k10_relat_1(X9,X10)|~v1_relat_1(X9)))&((~r2_hidden(esk2_3(X9,X16,X17),X17)|(~r2_hidden(k4_tarski(esk2_3(X9,X16,X17),X19),X9)|~r2_hidden(X19,X16))|X17=k10_relat_1(X9,X16)|~v1_relat_1(X9))&((r2_hidden(k4_tarski(esk2_3(X9,X16,X17),esk3_3(X9,X16,X17)),X9)|r2_hidden(esk2_3(X9,X16,X17),X17)|X17=k10_relat_1(X9,X16)|~v1_relat_1(X9))&(r2_hidden(esk3_3(X9,X16,X17),X16)|r2_hidden(esk2_3(X9,X16,X17),X17)|X17=k10_relat_1(X9,X16)|~v1_relat_1(X9))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).
% 0.20/0.38  cnf(c_0_26, negated_conjecture, (~r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))|~r2_hidden(esk4_3(esk9_0,X1,esk8_0),esk6_0)|~r2_hidden(esk4_3(esk9_0,X1,esk8_0),esk7_0)|~r2_hidden(esk9_0,k10_relat_1(esk8_0,X1))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.38  cnf(c_0_27, plain, (r2_hidden(esk4_3(X1,X2,X3),X2)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.38  cnf(c_0_28, plain, (r2_hidden(esk4_3(X1,X2,X3),X4)|~v5_relat_1(X3,X4)|~v1_relat_1(X3)|~r2_hidden(X1,k10_relat_1(X3,X2))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.38  cnf(c_0_29, negated_conjecture, (v5_relat_1(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_24, c_0_13])).
% 0.20/0.38  cnf(c_0_30, plain, (r2_hidden(X1,X5)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X2,X4)|X5!=k10_relat_1(X3,X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.38  cnf(c_0_31, negated_conjecture, (r2_hidden(k4_tarski(esk9_0,esk10_0),esk8_0)|r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  cnf(c_0_32, negated_conjecture, (~r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))|~r2_hidden(esk4_3(esk9_0,esk6_0,esk8_0),esk7_0)|~r2_hidden(esk9_0,k10_relat_1(esk8_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_16])])).
% 0.20/0.38  cnf(c_0_33, negated_conjecture, (r2_hidden(esk4_3(X1,X2,esk8_0),esk7_0)|~r2_hidden(X1,k10_relat_1(esk8_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_16])])).
% 0.20/0.38  fof(c_0_34, plain, ![X35, X36, X37, X38]:(~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|k8_relset_1(X35,X36,X37,X38)=k10_relat_1(X37,X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).
% 0.20/0.38  cnf(c_0_35, negated_conjecture, (r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))|r2_hidden(esk9_0,X1)|X1!=k10_relat_1(esk8_0,X2)|~r2_hidden(esk10_0,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_16])])).
% 0.20/0.38  cnf(c_0_36, negated_conjecture, (~r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))|~r2_hidden(esk9_0,k10_relat_1(esk8_0,esk6_0))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.38  cnf(c_0_37, plain, (k8_relset_1(X2,X3,X1,X4)=k10_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.38  cnf(c_0_38, negated_conjecture, (r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))|r2_hidden(esk9_0,k10_relat_1(esk8_0,X1))|~r2_hidden(esk10_0,X1)), inference(er,[status(thm)],[c_0_35])).
% 0.20/0.38  cnf(c_0_39, negated_conjecture, (r2_hidden(esk10_0,esk6_0)|r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  cnf(c_0_40, negated_conjecture, (~r2_hidden(esk9_0,k10_relat_1(esk8_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_13])])).
% 0.20/0.38  cnf(c_0_41, negated_conjecture, (r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])).
% 0.20/0.38  cnf(c_0_42, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_37]), c_0_13])]), c_0_40]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 43
% 0.20/0.38  # Proof object clause steps            : 26
% 0.20/0.38  # Proof object formula steps           : 17
% 0.20/0.38  # Proof object conjectures             : 19
% 0.20/0.38  # Proof object clause conjectures      : 16
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 13
% 0.20/0.38  # Proof object initial formulas used   : 8
% 0.20/0.38  # Proof object generating inferences   : 13
% 0.20/0.38  # Proof object simplifying inferences  : 14
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 8
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 25
% 0.20/0.38  # Removed in clause preprocessing      : 0
% 0.20/0.38  # Initial clauses in saturation        : 25
% 0.20/0.38  # Processed clauses                    : 69
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 0
% 0.20/0.38  # ...remaining for further processing  : 69
% 0.20/0.38  # Other redundant clauses eliminated   : 0
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 1
% 0.20/0.38  # Backward-rewritten                   : 12
% 0.20/0.38  # Generated clauses                    : 55
% 0.20/0.38  # ...of the previous two non-trivial   : 59
% 0.20/0.38  # Contextual simplify-reflections      : 0
% 0.20/0.38  # Paramodulations                      : 54
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 1
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 31
% 0.20/0.38  #    Positive orientable unit clauses  : 6
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 4
% 0.20/0.38  #    Non-unit-clauses                  : 21
% 0.20/0.38  # Current number of unprocessed clauses: 33
% 0.20/0.38  # ...number of literals in the above   : 150
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 38
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 236
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 61
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 1
% 0.20/0.38  # Unit Clause-clause subsumption calls : 14
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 1
% 0.20/0.38  # BW rewrite match successes           : 1
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 3360
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.034 s
% 0.20/0.38  # System time              : 0.001 s
% 0.20/0.38  # Total time               : 0.035 s
% 0.20/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
