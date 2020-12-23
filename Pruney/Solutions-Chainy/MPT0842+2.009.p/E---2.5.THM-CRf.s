%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:58:46 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 142 expanded)
%              Number of clauses        :   29 (  58 expanded)
%              Number of leaves         :    8 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :  161 ( 824 expanded)
%              Number of equality atoms :   13 (  26 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   15 (   2 average)
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

fof(dt_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

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

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

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
      | m1_subset_1(k2_relset_1(X29,X30,X31),k1_zfmisc_1(X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).

fof(c_0_10,plain,(
    ! [X32,X33,X34] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
      | k2_relset_1(X32,X33,X34) = k2_relat_1(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_11,plain,(
    ! [X26,X27,X28] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | v1_relat_1(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_12,negated_conjecture,(
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

cnf(c_0_13,plain,
    ( m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
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

cnf(c_0_16,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X10,X11,X12,X14,X15,X16,X17,X19] :
      ( ( ~ r2_hidden(X12,X11)
        | r2_hidden(k4_tarski(esk1_3(X10,X11,X12),X12),X10)
        | X11 != k2_relat_1(X10) )
      & ( ~ r2_hidden(k4_tarski(X15,X14),X10)
        | r2_hidden(X14,X11)
        | X11 != k2_relat_1(X10) )
      & ( ~ r2_hidden(esk2_2(X16,X17),X17)
        | ~ r2_hidden(k4_tarski(X19,esk2_2(X16,X17)),X16)
        | X17 = k2_relat_1(X16) )
      & ( r2_hidden(esk2_2(X16,X17),X17)
        | r2_hidden(k4_tarski(esk3_2(X16,X17),esk2_2(X16,X17)),X16)
        | X17 = k2_relat_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

fof(c_0_19,plain,(
    ! [X7,X8,X9] :
      ( ~ r2_hidden(X7,X8)
      | ~ m1_subset_1(X8,k1_zfmisc_1(X9))
      | m1_subset_1(X7,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_20,plain,
    ( m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_21,plain,
    ( r2_hidden(X3,k10_relat_1(X2,X4))
    | ~ r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(k4_tarski(esk9_0,esk10_0),esk8_0)
    | r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( ~ r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))
    | ~ m1_subset_1(X1,esk7_0)
    | ~ r2_hidden(k4_tarski(esk9_0,X1),esk8_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_26,plain,
    ( r2_hidden(k4_tarski(X1,esk4_3(X1,X2,X3)),X3)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(k2_relat_1(esk8_0),k1_zfmisc_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_17])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))
    | r2_hidden(esk9_0,k10_relat_1(esk8_0,X1))
    | ~ r2_hidden(esk10_0,k2_relat_1(esk8_0))
    | ~ r2_hidden(esk10_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))
    | r2_hidden(esk10_0,X1)
    | X1 != k2_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( ~ v1_relat_1(esk8_0)
    | ~ m1_subset_1(esk4_3(esk9_0,X1,esk8_0),esk7_0)
    | ~ r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))
    | ~ r2_hidden(esk4_3(esk9_0,X1,esk8_0),esk6_0)
    | ~ r2_hidden(esk9_0,k10_relat_1(esk8_0,X1)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(X1,esk7_0)
    | ~ r2_hidden(X1,k2_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),k2_relat_1(X3))
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))
    | r2_hidden(esk9_0,k10_relat_1(esk8_0,X1))
    | ~ r2_hidden(esk10_0,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk10_0,esk6_0)
    | r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_36,plain,(
    ! [X35,X36,X37,X38] :
      ( ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
      | k8_relset_1(X35,X36,X37,X38) = k10_relat_1(X37,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

cnf(c_0_37,negated_conjecture,
    ( ~ m1_subset_1(esk4_3(esk9_0,X1,esk8_0),esk7_0)
    | ~ r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))
    | ~ r2_hidden(esk4_3(esk9_0,X1,esk8_0),esk6_0)
    | ~ r2_hidden(esk9_0,k10_relat_1(esk8_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_23])])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk4_3(X1,X2,esk8_0),esk7_0)
    | ~ r2_hidden(X1,k10_relat_1(esk8_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_23])])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))
    | r2_hidden(esk9_0,k10_relat_1(esk8_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( ~ r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))
    | ~ r2_hidden(esk4_3(esk9_0,X1,esk8_0),esk6_0)
    | ~ r2_hidden(esk9_0,k10_relat_1(esk8_0,X1)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk9_0,k10_relat_1(esk8_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_17])])).

cnf(c_0_44,negated_conjecture,
    ( ~ r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_23])])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_40]),c_0_43]),c_0_17])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:18:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.12/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.027 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t53_relset_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))=>![X5]:(m1_subset_1(X5,X1)=>(r2_hidden(X5,k8_relset_1(X1,X3,X4,X2))<=>?[X6]:((m1_subset_1(X6,X3)&r2_hidden(k4_tarski(X5,X6),X4))&r2_hidden(X6,X2)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_relset_1)).
% 0.12/0.37  fof(dt_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 0.12/0.37  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.12/0.37  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.12/0.37  fof(t166_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 0.12/0.37  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 0.12/0.37  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.12/0.37  fof(redefinition_k8_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k8_relset_1(X1,X2,X3,X4)=k10_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 0.12/0.37  fof(c_0_8, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))=>![X5]:(m1_subset_1(X5,X1)=>(r2_hidden(X5,k8_relset_1(X1,X3,X4,X2))<=>?[X6]:((m1_subset_1(X6,X3)&r2_hidden(k4_tarski(X5,X6),X4))&r2_hidden(X6,X2))))))))), inference(assume_negation,[status(cth)],[t53_relset_1])).
% 0.12/0.37  fof(c_0_9, plain, ![X29, X30, X31]:(~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|m1_subset_1(k2_relset_1(X29,X30,X31),k1_zfmisc_1(X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).
% 0.12/0.37  fof(c_0_10, plain, ![X32, X33, X34]:(~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|k2_relset_1(X32,X33,X34)=k2_relat_1(X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.12/0.37  fof(c_0_11, plain, ![X26, X27, X28]:(~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|v1_relat_1(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.12/0.37  fof(c_0_12, negated_conjecture, ![X44]:(~v1_xboole_0(esk5_0)&(~v1_xboole_0(esk6_0)&(~v1_xboole_0(esk7_0)&(m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk7_0)))&(m1_subset_1(esk9_0,esk5_0)&((~r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))|(~m1_subset_1(X44,esk7_0)|~r2_hidden(k4_tarski(esk9_0,X44),esk8_0)|~r2_hidden(X44,esk6_0)))&(((m1_subset_1(esk10_0,esk7_0)|r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0)))&(r2_hidden(k4_tarski(esk9_0,esk10_0),esk8_0)|r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))))&(r2_hidden(esk10_0,esk6_0)|r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0)))))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])])).
% 0.12/0.37  cnf(c_0_13, plain, (m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.37  cnf(c_0_14, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  fof(c_0_15, plain, ![X21, X22, X23, X25]:((((r2_hidden(esk4_3(X21,X22,X23),k2_relat_1(X23))|~r2_hidden(X21,k10_relat_1(X23,X22))|~v1_relat_1(X23))&(r2_hidden(k4_tarski(X21,esk4_3(X21,X22,X23)),X23)|~r2_hidden(X21,k10_relat_1(X23,X22))|~v1_relat_1(X23)))&(r2_hidden(esk4_3(X21,X22,X23),X22)|~r2_hidden(X21,k10_relat_1(X23,X22))|~v1_relat_1(X23)))&(~r2_hidden(X25,k2_relat_1(X23))|~r2_hidden(k4_tarski(X21,X25),X23)|~r2_hidden(X25,X22)|r2_hidden(X21,k10_relat_1(X23,X22))|~v1_relat_1(X23))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).
% 0.12/0.37  cnf(c_0_16, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  fof(c_0_18, plain, ![X10, X11, X12, X14, X15, X16, X17, X19]:(((~r2_hidden(X12,X11)|r2_hidden(k4_tarski(esk1_3(X10,X11,X12),X12),X10)|X11!=k2_relat_1(X10))&(~r2_hidden(k4_tarski(X15,X14),X10)|r2_hidden(X14,X11)|X11!=k2_relat_1(X10)))&((~r2_hidden(esk2_2(X16,X17),X17)|~r2_hidden(k4_tarski(X19,esk2_2(X16,X17)),X16)|X17=k2_relat_1(X16))&(r2_hidden(esk2_2(X16,X17),X17)|r2_hidden(k4_tarski(esk3_2(X16,X17),esk2_2(X16,X17)),X16)|X17=k2_relat_1(X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.12/0.37  fof(c_0_19, plain, ![X7, X8, X9]:(~r2_hidden(X7,X8)|~m1_subset_1(X8,k1_zfmisc_1(X9))|m1_subset_1(X7,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.12/0.37  cnf(c_0_20, plain, (m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.12/0.37  cnf(c_0_21, plain, (r2_hidden(X3,k10_relat_1(X2,X4))|~r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X1,X4)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  cnf(c_0_22, negated_conjecture, (r2_hidden(k4_tarski(esk9_0,esk10_0),esk8_0)|r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_23, negated_conjecture, (v1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.12/0.37  cnf(c_0_24, plain, (r2_hidden(X2,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.37  cnf(c_0_25, negated_conjecture, (~r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))|~m1_subset_1(X1,esk7_0)|~r2_hidden(k4_tarski(esk9_0,X1),esk8_0)|~r2_hidden(X1,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_26, plain, (r2_hidden(k4_tarski(X1,esk4_3(X1,X2,X3)),X3)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  cnf(c_0_27, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.37  cnf(c_0_28, negated_conjecture, (m1_subset_1(k2_relat_1(esk8_0),k1_zfmisc_1(esk7_0))), inference(spm,[status(thm)],[c_0_20, c_0_17])).
% 0.12/0.37  cnf(c_0_29, negated_conjecture, (r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))|r2_hidden(esk9_0,k10_relat_1(esk8_0,X1))|~r2_hidden(esk10_0,k2_relat_1(esk8_0))|~r2_hidden(esk10_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])])).
% 0.12/0.37  cnf(c_0_30, negated_conjecture, (r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))|r2_hidden(esk10_0,X1)|X1!=k2_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_24, c_0_22])).
% 0.12/0.37  cnf(c_0_31, negated_conjecture, (~v1_relat_1(esk8_0)|~m1_subset_1(esk4_3(esk9_0,X1,esk8_0),esk7_0)|~r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))|~r2_hidden(esk4_3(esk9_0,X1,esk8_0),esk6_0)|~r2_hidden(esk9_0,k10_relat_1(esk8_0,X1))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.12/0.37  cnf(c_0_32, negated_conjecture, (m1_subset_1(X1,esk7_0)|~r2_hidden(X1,k2_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.12/0.37  cnf(c_0_33, plain, (r2_hidden(esk4_3(X1,X2,X3),k2_relat_1(X3))|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  cnf(c_0_34, negated_conjecture, (r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))|r2_hidden(esk9_0,k10_relat_1(esk8_0,X1))|~r2_hidden(esk10_0,X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.12/0.37  cnf(c_0_35, negated_conjecture, (r2_hidden(esk10_0,esk6_0)|r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  fof(c_0_36, plain, ![X35, X36, X37, X38]:(~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|k8_relset_1(X35,X36,X37,X38)=k10_relat_1(X37,X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).
% 0.12/0.37  cnf(c_0_37, negated_conjecture, (~m1_subset_1(esk4_3(esk9_0,X1,esk8_0),esk7_0)|~r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))|~r2_hidden(esk4_3(esk9_0,X1,esk8_0),esk6_0)|~r2_hidden(esk9_0,k10_relat_1(esk8_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_23])])).
% 0.12/0.37  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk4_3(X1,X2,esk8_0),esk7_0)|~r2_hidden(X1,k10_relat_1(esk8_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_23])])).
% 0.12/0.37  cnf(c_0_39, negated_conjecture, (r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))|r2_hidden(esk9_0,k10_relat_1(esk8_0,esk6_0))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.12/0.37  cnf(c_0_40, plain, (k8_relset_1(X2,X3,X1,X4)=k10_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.12/0.37  cnf(c_0_41, negated_conjecture, (~r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))|~r2_hidden(esk4_3(esk9_0,X1,esk8_0),esk6_0)|~r2_hidden(esk9_0,k10_relat_1(esk8_0,X1))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.12/0.37  cnf(c_0_42, plain, (r2_hidden(esk4_3(X1,X2,X3),X2)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  cnf(c_0_43, negated_conjecture, (r2_hidden(esk9_0,k10_relat_1(esk8_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_17])])).
% 0.12/0.37  cnf(c_0_44, negated_conjecture, (~r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43]), c_0_23])])).
% 0.12/0.37  cnf(c_0_45, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_40]), c_0_43]), c_0_17])]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 46
% 0.12/0.37  # Proof object clause steps            : 29
% 0.12/0.37  # Proof object formula steps           : 17
% 0.12/0.37  # Proof object conjectures             : 21
% 0.12/0.37  # Proof object clause conjectures      : 18
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 14
% 0.12/0.37  # Proof object initial formulas used   : 8
% 0.12/0.37  # Proof object generating inferences   : 14
% 0.12/0.37  # Proof object simplifying inferences  : 14
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 8
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 22
% 0.12/0.37  # Removed in clause preprocessing      : 0
% 0.12/0.37  # Initial clauses in saturation        : 22
% 0.12/0.37  # Processed clauses                    : 70
% 0.12/0.37  # ...of these trivial                  : 1
% 0.12/0.37  # ...subsumed                          : 2
% 0.12/0.37  # ...remaining for further processing  : 67
% 0.12/0.37  # Other redundant clauses eliminated   : 0
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 2
% 0.12/0.37  # Backward-rewritten                   : 2
% 0.12/0.37  # Generated clauses                    : 56
% 0.12/0.37  # ...of the previous two non-trivial   : 53
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 50
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 1
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 36
% 0.12/0.37  #    Positive orientable unit clauses  : 5
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 4
% 0.12/0.37  #    Non-unit-clauses                  : 27
% 0.12/0.37  # Current number of unprocessed clauses: 22
% 0.12/0.37  # ...number of literals in the above   : 79
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 31
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 246
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 153
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 4
% 0.12/0.37  # Unit Clause-clause subsumption calls : 20
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 2
% 0.12/0.37  # BW rewrite match successes           : 2
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 2883
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.031 s
% 0.12/0.37  # System time              : 0.004 s
% 0.12/0.37  # Total time               : 0.035 s
% 0.12/0.37  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
