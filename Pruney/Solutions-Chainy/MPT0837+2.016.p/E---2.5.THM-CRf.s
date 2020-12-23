%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:58:17 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 185 expanded)
%              Number of clauses        :   24 (  73 expanded)
%              Number of leaves         :   10 (  48 expanded)
%              Depth                    :   10
%              Number of atoms          :  137 ( 690 expanded)
%              Number of equality atoms :   18 (  32 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_relset_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
             => ! [X4] :
                  ( r2_hidden(X4,k2_relset_1(X2,X1,X3))
                <=> ? [X5] :
                      ( m1_subset_1(X5,X2)
                      & r2_hidden(k4_tarski(X5,X4),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relset_1)).

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

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
               => ! [X4] :
                    ( r2_hidden(X4,k2_relset_1(X2,X1,X3))
                  <=> ? [X5] :
                        ( m1_subset_1(X5,X2)
                        & r2_hidden(k4_tarski(X5,X4),X3) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t48_relset_1])).

fof(c_0_11,plain,(
    ! [X8,X9] :
      ( ~ v1_relat_1(X8)
      | ~ m1_subset_1(X9,k1_zfmisc_1(X8))
      | v1_relat_1(X9) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_12,negated_conjecture,(
    ! [X42] :
      ( ~ v1_xboole_0(esk5_0)
      & ~ v1_xboole_0(esk6_0)
      & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk5_0)))
      & ( ~ r2_hidden(esk8_0,k2_relset_1(esk6_0,esk5_0,esk7_0))
        | ~ m1_subset_1(X42,esk6_0)
        | ~ r2_hidden(k4_tarski(X42,esk8_0),esk7_0) )
      & ( m1_subset_1(esk9_0,esk6_0)
        | r2_hidden(esk8_0,k2_relset_1(esk6_0,esk5_0,esk7_0)) )
      & ( r2_hidden(k4_tarski(esk9_0,esk8_0),esk7_0)
        | r2_hidden(esk8_0,k2_relset_1(esk6_0,esk5_0,esk7_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])])).

fof(c_0_13,plain,(
    ! [X21,X22] : v1_relat_1(k2_zfmisc_1(X21,X22)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_14,plain,(
    ! [X32,X33,X34] :
      ( ( v4_relat_1(X34,X32)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( v5_relat_1(X34,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_15,plain,(
    ! [X23,X24,X25,X27] :
      ( ( r2_hidden(esk4_3(X23,X24,X25),k1_relat_1(X25))
        | ~ r2_hidden(X23,k9_relat_1(X25,X24))
        | ~ v1_relat_1(X25) )
      & ( r2_hidden(k4_tarski(esk4_3(X23,X24,X25),X23),X25)
        | ~ r2_hidden(X23,k9_relat_1(X25,X24))
        | ~ v1_relat_1(X25) )
      & ( r2_hidden(esk4_3(X23,X24,X25),X24)
        | ~ r2_hidden(X23,k9_relat_1(X25,X24))
        | ~ v1_relat_1(X25) )
      & ( ~ r2_hidden(X27,k1_relat_1(X25))
        | ~ r2_hidden(k4_tarski(X27,X23),X25)
        | ~ r2_hidden(X27,X24)
        | r2_hidden(X23,k9_relat_1(X25,X24))
        | ~ v1_relat_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

cnf(c_0_16,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,plain,(
    ! [X30,X31] :
      ( ~ v1_relat_1(X31)
      | ~ v4_relat_1(X31,X30)
      | X31 = k7_relat_1(X31,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_20,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( ~ r2_hidden(esk8_0,k2_relset_1(esk6_0,esk5_0,esk7_0))
    | ~ m1_subset_1(X1,esk6_0)
    | ~ r2_hidden(k4_tarski(X1,esk8_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,plain,
    ( r2_hidden(k4_tarski(esk4_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])])).

fof(c_0_24,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,X7)
      | m1_subset_1(X6,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

fof(c_0_25,plain,(
    ! [X28,X29] :
      ( ~ v1_relat_1(X29)
      | k2_relat_1(k7_relat_1(X29,X28)) = k9_relat_1(X29,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_26,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( v4_relat_1(esk7_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_17])).

cnf(c_0_28,negated_conjecture,
    ( ~ m1_subset_1(esk4_3(esk8_0,X1,esk7_0),esk6_0)
    | ~ r2_hidden(esk8_0,k2_relset_1(esk6_0,esk5_0,esk7_0))
    | ~ r2_hidden(esk8_0,k9_relat_1(esk7_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

cnf(c_0_29,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( k7_relat_1(esk7_0,esk6_0) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_23])])).

fof(c_0_32,plain,(
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

cnf(c_0_33,negated_conjecture,
    ( ~ r2_hidden(esk8_0,k2_relset_1(esk6_0,esk5_0,esk7_0))
    | ~ r2_hidden(esk4_3(esk8_0,X1,esk7_0),esk6_0)
    | ~ r2_hidden(esk8_0,k9_relat_1(esk7_0,X1)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_35,negated_conjecture,
    ( k9_relat_1(esk7_0,esk6_0) = k2_relat_1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_23])])).

fof(c_0_36,plain,(
    ! [X35,X36,X37] :
      ( ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
      | k2_relset_1(X35,X36,X37) = k2_relat_1(X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_37,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(k4_tarski(esk9_0,esk8_0),esk7_0)
    | r2_hidden(esk8_0,k2_relset_1(esk6_0,esk5_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_39,negated_conjecture,
    ( ~ r2_hidden(esk8_0,k2_relset_1(esk6_0,esk5_0,esk7_0))
    | ~ r2_hidden(esk8_0,k2_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_23])])).

cnf(c_0_40,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk8_0,k2_relset_1(esk6_0,esk5_0,esk7_0))
    | r2_hidden(esk8_0,X1)
    | X1 != k2_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( ~ r2_hidden(esk8_0,k2_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_17])])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk8_0,k2_relset_1(esk6_0,esk5_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_41]),c_0_42])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_40]),c_0_17])]),c_0_42]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:20:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.13/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t48_relset_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>![X4]:(r2_hidden(X4,k2_relset_1(X2,X1,X3))<=>?[X5]:(m1_subset_1(X5,X2)&r2_hidden(k4_tarski(X5,X4),X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_relset_1)).
% 0.13/0.38  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.13/0.38  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.13/0.38  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.13/0.38  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 0.13/0.38  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 0.13/0.38  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 0.13/0.38  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 0.13/0.38  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 0.13/0.38  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.13/0.38  fof(c_0_10, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>![X4]:(r2_hidden(X4,k2_relset_1(X2,X1,X3))<=>?[X5]:(m1_subset_1(X5,X2)&r2_hidden(k4_tarski(X5,X4),X3))))))), inference(assume_negation,[status(cth)],[t48_relset_1])).
% 0.13/0.38  fof(c_0_11, plain, ![X8, X9]:(~v1_relat_1(X8)|(~m1_subset_1(X9,k1_zfmisc_1(X8))|v1_relat_1(X9))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.13/0.38  fof(c_0_12, negated_conjecture, ![X42]:(~v1_xboole_0(esk5_0)&(~v1_xboole_0(esk6_0)&(m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk5_0)))&((~r2_hidden(esk8_0,k2_relset_1(esk6_0,esk5_0,esk7_0))|(~m1_subset_1(X42,esk6_0)|~r2_hidden(k4_tarski(X42,esk8_0),esk7_0)))&((m1_subset_1(esk9_0,esk6_0)|r2_hidden(esk8_0,k2_relset_1(esk6_0,esk5_0,esk7_0)))&(r2_hidden(k4_tarski(esk9_0,esk8_0),esk7_0)|r2_hidden(esk8_0,k2_relset_1(esk6_0,esk5_0,esk7_0)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])])).
% 0.13/0.38  fof(c_0_13, plain, ![X21, X22]:v1_relat_1(k2_zfmisc_1(X21,X22)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.13/0.38  fof(c_0_14, plain, ![X32, X33, X34]:((v4_relat_1(X34,X32)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))&(v5_relat_1(X34,X33)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.13/0.38  fof(c_0_15, plain, ![X23, X24, X25, X27]:((((r2_hidden(esk4_3(X23,X24,X25),k1_relat_1(X25))|~r2_hidden(X23,k9_relat_1(X25,X24))|~v1_relat_1(X25))&(r2_hidden(k4_tarski(esk4_3(X23,X24,X25),X23),X25)|~r2_hidden(X23,k9_relat_1(X25,X24))|~v1_relat_1(X25)))&(r2_hidden(esk4_3(X23,X24,X25),X24)|~r2_hidden(X23,k9_relat_1(X25,X24))|~v1_relat_1(X25)))&(~r2_hidden(X27,k1_relat_1(X25))|~r2_hidden(k4_tarski(X27,X23),X25)|~r2_hidden(X27,X24)|r2_hidden(X23,k9_relat_1(X25,X24))|~v1_relat_1(X25))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 0.13/0.38  cnf(c_0_16, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_18, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  fof(c_0_19, plain, ![X30, X31]:(~v1_relat_1(X31)|~v4_relat_1(X31,X30)|X31=k7_relat_1(X31,X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 0.13/0.38  cnf(c_0_20, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_21, negated_conjecture, (~r2_hidden(esk8_0,k2_relset_1(esk6_0,esk5_0,esk7_0))|~m1_subset_1(X1,esk6_0)|~r2_hidden(k4_tarski(X1,esk8_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_22, plain, (r2_hidden(k4_tarski(esk4_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_23, negated_conjecture, (v1_relat_1(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])])).
% 0.13/0.38  fof(c_0_24, plain, ![X6, X7]:(~r2_hidden(X6,X7)|m1_subset_1(X6,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.13/0.38  fof(c_0_25, plain, ![X28, X29]:(~v1_relat_1(X29)|k2_relat_1(k7_relat_1(X29,X28))=k9_relat_1(X29,X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.13/0.38  cnf(c_0_26, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_27, negated_conjecture, (v4_relat_1(esk7_0,esk6_0)), inference(spm,[status(thm)],[c_0_20, c_0_17])).
% 0.13/0.38  cnf(c_0_28, negated_conjecture, (~m1_subset_1(esk4_3(esk8_0,X1,esk7_0),esk6_0)|~r2_hidden(esk8_0,k2_relset_1(esk6_0,esk5_0,esk7_0))|~r2_hidden(esk8_0,k9_relat_1(esk7_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])])).
% 0.13/0.38  cnf(c_0_29, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.38  cnf(c_0_30, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.38  cnf(c_0_31, negated_conjecture, (k7_relat_1(esk7_0,esk6_0)=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_23])])).
% 0.13/0.38  fof(c_0_32, plain, ![X10, X11, X12, X14, X15, X16, X17, X19]:(((~r2_hidden(X12,X11)|r2_hidden(k4_tarski(esk1_3(X10,X11,X12),X12),X10)|X11!=k2_relat_1(X10))&(~r2_hidden(k4_tarski(X15,X14),X10)|r2_hidden(X14,X11)|X11!=k2_relat_1(X10)))&((~r2_hidden(esk2_2(X16,X17),X17)|~r2_hidden(k4_tarski(X19,esk2_2(X16,X17)),X16)|X17=k2_relat_1(X16))&(r2_hidden(esk2_2(X16,X17),X17)|r2_hidden(k4_tarski(esk3_2(X16,X17),esk2_2(X16,X17)),X16)|X17=k2_relat_1(X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.13/0.38  cnf(c_0_33, negated_conjecture, (~r2_hidden(esk8_0,k2_relset_1(esk6_0,esk5_0,esk7_0))|~r2_hidden(esk4_3(esk8_0,X1,esk7_0),esk6_0)|~r2_hidden(esk8_0,k9_relat_1(esk7_0,X1))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.38  cnf(c_0_34, plain, (r2_hidden(esk4_3(X1,X2,X3),X2)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_35, negated_conjecture, (k9_relat_1(esk7_0,esk6_0)=k2_relat_1(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_23])])).
% 0.13/0.38  fof(c_0_36, plain, ![X35, X36, X37]:(~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|k2_relset_1(X35,X36,X37)=k2_relat_1(X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.13/0.38  cnf(c_0_37, plain, (r2_hidden(X2,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, (r2_hidden(k4_tarski(esk9_0,esk8_0),esk7_0)|r2_hidden(esk8_0,k2_relset_1(esk6_0,esk5_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_39, negated_conjecture, (~r2_hidden(esk8_0,k2_relset_1(esk6_0,esk5_0,esk7_0))|~r2_hidden(esk8_0,k2_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_23])])).
% 0.13/0.38  cnf(c_0_40, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.38  cnf(c_0_41, negated_conjecture, (r2_hidden(esk8_0,k2_relset_1(esk6_0,esk5_0,esk7_0))|r2_hidden(esk8_0,X1)|X1!=k2_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, (~r2_hidden(esk8_0,k2_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_17])])).
% 0.13/0.38  cnf(c_0_43, negated_conjecture, (r2_hidden(esk8_0,k2_relset_1(esk6_0,esk5_0,esk7_0))), inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_41]), c_0_42])).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_40]), c_0_17])]), c_0_42]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 45
% 0.13/0.38  # Proof object clause steps            : 24
% 0.13/0.38  # Proof object formula steps           : 21
% 0.13/0.38  # Proof object conjectures             : 17
% 0.13/0.38  # Proof object clause conjectures      : 14
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 13
% 0.13/0.38  # Proof object initial formulas used   : 10
% 0.13/0.38  # Proof object generating inferences   : 11
% 0.13/0.38  # Proof object simplifying inferences  : 17
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 10
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 22
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 22
% 0.13/0.38  # Processed clauses                    : 58
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 0
% 0.13/0.38  # ...remaining for further processing  : 58
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 9
% 0.13/0.38  # Generated clauses                    : 32
% 0.13/0.38  # ...of the previous two non-trivial   : 35
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 31
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 1
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 27
% 0.13/0.38  #    Positive orientable unit clauses  : 8
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 3
% 0.13/0.38  #    Non-unit-clauses                  : 16
% 0.13/0.38  # Current number of unprocessed clauses: 15
% 0.13/0.38  # ...number of literals in the above   : 62
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 31
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 153
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 94
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.38  # Unit Clause-clause subsumption calls : 18
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 1
% 0.13/0.38  # BW rewrite match successes           : 1
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 2383
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.032 s
% 0.13/0.38  # System time              : 0.002 s
% 0.13/0.38  # Total time               : 0.034 s
% 0.13/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
