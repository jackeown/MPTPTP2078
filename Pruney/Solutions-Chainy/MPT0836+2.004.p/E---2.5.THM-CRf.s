%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:58:13 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   45 (  96 expanded)
%              Number of clauses        :   26 (  41 expanded)
%              Number of leaves         :    9 (  23 expanded)
%              Depth                    :   10
%              Number of atoms          :  133 ( 416 expanded)
%              Number of equality atoms :   22 (  46 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k7_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(t47_relset_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
             => ! [X4] :
                  ( m1_subset_1(X4,X1)
                 => ( r2_hidden(X4,k1_relset_1(X1,X2,X3))
                  <=> ? [X5] :
                        ( m1_subset_1(X5,X2)
                        & r2_hidden(k4_tarski(X4,X5),X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(d16_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(t204_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> r2_hidden(X2,k11_relat_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(c_0_9,plain,(
    ! [X28,X29,X30,X31] :
      ( ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
      | m1_subset_1(k7_relset_1(X28,X29,X30,X31),k1_zfmisc_1(X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relset_1])])).

fof(c_0_10,plain,(
    ! [X35,X36,X37,X38] :
      ( ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
      | k7_relset_1(X35,X36,X37,X38) = k9_relat_1(X37,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
               => ! [X4] :
                    ( m1_subset_1(X4,X1)
                   => ( r2_hidden(X4,k1_relset_1(X1,X2,X3))
                    <=> ? [X5] :
                          ( m1_subset_1(X5,X2)
                          & r2_hidden(k4_tarski(X4,X5),X3) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t47_relset_1])).

cnf(c_0_12,plain,
    ( m1_subset_1(k7_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,negated_conjecture,(
    ! [X43] :
      ( ~ v1_xboole_0(esk4_0)
      & ~ v1_xboole_0(esk5_0)
      & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
      & m1_subset_1(esk7_0,esk4_0)
      & ( ~ r2_hidden(esk7_0,k1_relset_1(esk4_0,esk5_0,esk6_0))
        | ~ m1_subset_1(X43,esk5_0)
        | ~ r2_hidden(k4_tarski(esk7_0,X43),esk6_0) )
      & ( m1_subset_1(esk8_0,esk5_0)
        | r2_hidden(esk7_0,k1_relset_1(esk4_0,esk5_0,esk6_0)) )
      & ( r2_hidden(k4_tarski(esk7_0,esk8_0),esk6_0)
        | r2_hidden(esk7_0,k1_relset_1(esk4_0,esk5_0,esk6_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])])])).

fof(c_0_15,plain,(
    ! [X25,X26,X27] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | v1_relat_1(X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_16,plain,
    ( m1_subset_1(k9_relat_1(X1,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3))) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X9,X10] :
      ( ~ v1_relat_1(X9)
      | k11_relat_1(X9,X10) = k9_relat_1(X9,k1_tarski(X10)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).

cnf(c_0_19,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X6,X7,X8] :
      ( ~ r2_hidden(X6,X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X8))
      | m1_subset_1(X6,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(k9_relat_1(esk6_0,X1),k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_17])).

fof(c_0_24,plain,(
    ! [X22,X23,X24] :
      ( ( ~ r2_hidden(k4_tarski(X22,X23),X24)
        | r2_hidden(X23,k11_relat_1(X24,X22))
        | ~ v1_relat_1(X24) )
      & ( ~ r2_hidden(X23,k11_relat_1(X24,X22))
        | r2_hidden(k4_tarski(X22,X23),X24)
        | ~ v1_relat_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).

fof(c_0_25,plain,(
    ! [X11,X12,X13,X15,X16,X17,X18,X20] :
      ( ( ~ r2_hidden(X13,X12)
        | r2_hidden(k4_tarski(X13,esk1_3(X11,X12,X13)),X11)
        | X12 != k1_relat_1(X11) )
      & ( ~ r2_hidden(k4_tarski(X15,X16),X11)
        | r2_hidden(X15,X12)
        | X12 != k1_relat_1(X11) )
      & ( ~ r2_hidden(esk2_2(X17,X18),X18)
        | ~ r2_hidden(k4_tarski(esk2_2(X17,X18),X20),X17)
        | X18 = k1_relat_1(X17) )
      & ( r2_hidden(esk2_2(X17,X18),X18)
        | r2_hidden(k4_tarski(esk2_2(X17,X18),esk3_2(X17,X18)),X17)
        | X18 = k1_relat_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_26,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(k11_relat_1(esk6_0,X1),k1_zfmisc_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

cnf(c_0_28,plain,
    ( r2_hidden(X2,k11_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( r2_hidden(k4_tarski(X1,esk1_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_0,esk8_0),esk6_0)
    | r2_hidden(esk7_0,k1_relset_1(esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_32,negated_conjecture,
    ( ~ r2_hidden(esk7_0,k1_relset_1(esk4_0,esk5_0,esk6_0))
    | ~ m1_subset_1(X1,esk5_0)
    | ~ r2_hidden(k4_tarski(esk7_0,X1),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(X1,esk5_0)
    | ~ r2_hidden(X1,k11_relat_1(esk6_0,X2)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),k11_relat_1(X1,X3))
    | X2 != k1_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk7_0,k1_relset_1(esk4_0,esk5_0,esk6_0))
    | r2_hidden(esk7_0,X1)
    | X1 != k1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_36,plain,(
    ! [X32,X33,X34] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
      | k1_relset_1(X32,X33,X34) = k1_relat_1(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_37,negated_conjecture,
    ( X1 != k1_relat_1(esk6_0)
    | ~ m1_subset_1(esk1_3(esk6_0,X1,esk7_0),esk5_0)
    | ~ r2_hidden(esk7_0,k1_relset_1(esk4_0,esk5_0,esk6_0))
    | ~ r2_hidden(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk1_3(esk6_0,X1,X2),esk5_0)
    | X1 != k1_relat_1(esk6_0)
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_23])])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk7_0,k1_relset_1(esk4_0,esk5_0,esk6_0))
    | r2_hidden(esk7_0,k1_relat_1(esk6_0)) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_40,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( X1 != k1_relat_1(esk6_0)
    | ~ r2_hidden(esk7_0,k1_relset_1(esk4_0,esk5_0,esk6_0))
    | ~ r2_hidden(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk7_0,k1_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_17])])).

cnf(c_0_43,negated_conjecture,
    ( X1 != k1_relat_1(esk6_0)
    | ~ r2_hidden(esk7_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_40]),c_0_42]),c_0_17])])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_43,c_0_42]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:04:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  # Version: 2.5pre002
% 0.13/0.36  # No SInE strategy applied
% 0.13/0.36  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.13/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.028 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(dt_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k7_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 0.13/0.39  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.13/0.39  fof(t47_relset_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>![X4]:(m1_subset_1(X4,X1)=>(r2_hidden(X4,k1_relset_1(X1,X2,X3))<=>?[X5]:(m1_subset_1(X5,X2)&r2_hidden(k4_tarski(X4,X5),X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relset_1)).
% 0.13/0.39  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.13/0.39  fof(d16_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 0.13/0.39  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.13/0.39  fof(t204_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r2_hidden(X2,k11_relat_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 0.13/0.39  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 0.13/0.39  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.13/0.39  fof(c_0_9, plain, ![X28, X29, X30, X31]:(~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))|m1_subset_1(k7_relset_1(X28,X29,X30,X31),k1_zfmisc_1(X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relset_1])])).
% 0.13/0.39  fof(c_0_10, plain, ![X35, X36, X37, X38]:(~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|k7_relset_1(X35,X36,X37,X38)=k9_relat_1(X37,X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.13/0.39  fof(c_0_11, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>![X4]:(m1_subset_1(X4,X1)=>(r2_hidden(X4,k1_relset_1(X1,X2,X3))<=>?[X5]:(m1_subset_1(X5,X2)&r2_hidden(k4_tarski(X4,X5),X3)))))))), inference(assume_negation,[status(cth)],[t47_relset_1])).
% 0.13/0.39  cnf(c_0_12, plain, (m1_subset_1(k7_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.39  cnf(c_0_13, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.39  fof(c_0_14, negated_conjecture, ![X43]:(~v1_xboole_0(esk4_0)&(~v1_xboole_0(esk5_0)&(m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))&(m1_subset_1(esk7_0,esk4_0)&((~r2_hidden(esk7_0,k1_relset_1(esk4_0,esk5_0,esk6_0))|(~m1_subset_1(X43,esk5_0)|~r2_hidden(k4_tarski(esk7_0,X43),esk6_0)))&((m1_subset_1(esk8_0,esk5_0)|r2_hidden(esk7_0,k1_relset_1(esk4_0,esk5_0,esk6_0)))&(r2_hidden(k4_tarski(esk7_0,esk8_0),esk6_0)|r2_hidden(esk7_0,k1_relset_1(esk4_0,esk5_0,esk6_0))))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])])])).
% 0.13/0.39  fof(c_0_15, plain, ![X25, X26, X27]:(~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))|v1_relat_1(X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.13/0.39  cnf(c_0_16, plain, (m1_subset_1(k9_relat_1(X1,X2),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.13/0.39  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.39  fof(c_0_18, plain, ![X9, X10]:(~v1_relat_1(X9)|k11_relat_1(X9,X10)=k9_relat_1(X9,k1_tarski(X10))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).
% 0.13/0.39  cnf(c_0_19, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  fof(c_0_20, plain, ![X6, X7, X8]:(~r2_hidden(X6,X7)|~m1_subset_1(X7,k1_zfmisc_1(X8))|m1_subset_1(X6,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.13/0.39  cnf(c_0_21, negated_conjecture, (m1_subset_1(k9_relat_1(esk6_0,X1),k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.13/0.39  cnf(c_0_22, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.39  cnf(c_0_23, negated_conjecture, (v1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_19, c_0_17])).
% 0.13/0.39  fof(c_0_24, plain, ![X22, X23, X24]:((~r2_hidden(k4_tarski(X22,X23),X24)|r2_hidden(X23,k11_relat_1(X24,X22))|~v1_relat_1(X24))&(~r2_hidden(X23,k11_relat_1(X24,X22))|r2_hidden(k4_tarski(X22,X23),X24)|~v1_relat_1(X24))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).
% 0.13/0.39  fof(c_0_25, plain, ![X11, X12, X13, X15, X16, X17, X18, X20]:(((~r2_hidden(X13,X12)|r2_hidden(k4_tarski(X13,esk1_3(X11,X12,X13)),X11)|X12!=k1_relat_1(X11))&(~r2_hidden(k4_tarski(X15,X16),X11)|r2_hidden(X15,X12)|X12!=k1_relat_1(X11)))&((~r2_hidden(esk2_2(X17,X18),X18)|~r2_hidden(k4_tarski(esk2_2(X17,X18),X20),X17)|X18=k1_relat_1(X17))&(r2_hidden(esk2_2(X17,X18),X18)|r2_hidden(k4_tarski(esk2_2(X17,X18),esk3_2(X17,X18)),X17)|X18=k1_relat_1(X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.13/0.39  cnf(c_0_26, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.39  cnf(c_0_27, negated_conjecture, (m1_subset_1(k11_relat_1(esk6_0,X1),k1_zfmisc_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])])).
% 0.13/0.39  cnf(c_0_28, plain, (r2_hidden(X2,k11_relat_1(X3,X1))|~r2_hidden(k4_tarski(X1,X2),X3)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.39  cnf(c_0_29, plain, (r2_hidden(k4_tarski(X1,esk1_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.39  cnf(c_0_30, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.39  cnf(c_0_31, negated_conjecture, (r2_hidden(k4_tarski(esk7_0,esk8_0),esk6_0)|r2_hidden(esk7_0,k1_relset_1(esk4_0,esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.39  cnf(c_0_32, negated_conjecture, (~r2_hidden(esk7_0,k1_relset_1(esk4_0,esk5_0,esk6_0))|~m1_subset_1(X1,esk5_0)|~r2_hidden(k4_tarski(esk7_0,X1),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.39  cnf(c_0_33, negated_conjecture, (m1_subset_1(X1,esk5_0)|~r2_hidden(X1,k11_relat_1(esk6_0,X2))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.13/0.39  cnf(c_0_34, plain, (r2_hidden(esk1_3(X1,X2,X3),k11_relat_1(X1,X3))|X2!=k1_relat_1(X1)|~v1_relat_1(X1)|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.39  cnf(c_0_35, negated_conjecture, (r2_hidden(esk7_0,k1_relset_1(esk4_0,esk5_0,esk6_0))|r2_hidden(esk7_0,X1)|X1!=k1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.13/0.39  fof(c_0_36, plain, ![X32, X33, X34]:(~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|k1_relset_1(X32,X33,X34)=k1_relat_1(X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.13/0.39  cnf(c_0_37, negated_conjecture, (X1!=k1_relat_1(esk6_0)|~m1_subset_1(esk1_3(esk6_0,X1,esk7_0),esk5_0)|~r2_hidden(esk7_0,k1_relset_1(esk4_0,esk5_0,esk6_0))|~r2_hidden(esk7_0,X1)), inference(spm,[status(thm)],[c_0_32, c_0_29])).
% 0.13/0.39  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk1_3(esk6_0,X1,X2),esk5_0)|X1!=k1_relat_1(esk6_0)|~r2_hidden(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_23])])).
% 0.13/0.39  cnf(c_0_39, negated_conjecture, (r2_hidden(esk7_0,k1_relset_1(esk4_0,esk5_0,esk6_0))|r2_hidden(esk7_0,k1_relat_1(esk6_0))), inference(er,[status(thm)],[c_0_35])).
% 0.13/0.39  cnf(c_0_40, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.39  cnf(c_0_41, negated_conjecture, (X1!=k1_relat_1(esk6_0)|~r2_hidden(esk7_0,k1_relset_1(esk4_0,esk5_0,esk6_0))|~r2_hidden(esk7_0,X1)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.13/0.39  cnf(c_0_42, negated_conjecture, (r2_hidden(esk7_0,k1_relat_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_17])])).
% 0.13/0.39  cnf(c_0_43, negated_conjecture, (X1!=k1_relat_1(esk6_0)|~r2_hidden(esk7_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_40]), c_0_42]), c_0_17])])).
% 0.13/0.39  cnf(c_0_44, negated_conjecture, ($false), inference(spm,[status(thm)],[c_0_43, c_0_42]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 45
% 0.13/0.39  # Proof object clause steps            : 26
% 0.13/0.39  # Proof object formula steps           : 19
% 0.13/0.39  # Proof object conjectures             : 18
% 0.13/0.39  # Proof object clause conjectures      : 15
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 12
% 0.13/0.39  # Proof object initial formulas used   : 9
% 0.13/0.39  # Proof object generating inferences   : 14
% 0.13/0.39  # Proof object simplifying inferences  : 9
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 9
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 19
% 0.13/0.39  # Removed in clause preprocessing      : 0
% 0.13/0.39  # Initial clauses in saturation        : 19
% 0.13/0.39  # Processed clauses                    : 75
% 0.13/0.39  # ...of these trivial                  : 1
% 0.13/0.39  # ...subsumed                          : 4
% 0.13/0.39  # ...remaining for further processing  : 70
% 0.13/0.39  # Other redundant clauses eliminated   : 0
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 2
% 0.13/0.39  # Backward-rewritten                   : 1
% 0.13/0.39  # Generated clauses                    : 65
% 0.13/0.39  # ...of the previous two non-trivial   : 62
% 0.13/0.39  # Contextual simplify-reflections      : 0
% 0.13/0.39  # Paramodulations                      : 61
% 0.13/0.39  # Factorizations                       : 0
% 0.13/0.39  # Equation resolutions                 : 4
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 48
% 0.13/0.39  #    Positive orientable unit clauses  : 6
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 2
% 0.13/0.39  #    Non-unit-clauses                  : 40
% 0.13/0.39  # Current number of unprocessed clauses: 25
% 0.13/0.39  # ...number of literals in the above   : 99
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 22
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 261
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 181
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 6
% 0.13/0.39  # Unit Clause-clause subsumption calls : 6
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 1
% 0.13/0.39  # BW rewrite match successes           : 1
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 2860
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.029 s
% 0.13/0.39  # System time              : 0.007 s
% 0.13/0.39  # Total time               : 0.036 s
% 0.13/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
