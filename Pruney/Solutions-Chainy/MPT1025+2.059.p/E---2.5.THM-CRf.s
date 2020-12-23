%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:43 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 106 expanded)
%              Number of clauses        :   27 (  39 expanded)
%              Number of leaves         :    6 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :  157 ( 556 expanded)
%              Number of equality atoms :    7 (  55 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   15 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t115_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X5] :
          ~ ( r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))
            & ! [X6] :
                ~ ( r2_hidden(X6,X1)
                  & r2_hidden(X6,X3)
                  & X5 = k1_funct_1(X4,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).

fof(t116_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X5] :
          ~ ( r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))
            & ! [X6] :
                ( m1_subset_1(X6,X1)
               => ~ ( r2_hidden(X6,X3)
                    & X5 = k1_funct_1(X4,X6) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(c_0_6,plain,(
    ! [X17,X18,X19] :
      ( ~ r2_hidden(X17,X18)
      | ~ m1_subset_1(X18,k1_zfmisc_1(X19))
      | ~ v1_xboole_0(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_7,plain,(
    ! [X15,X16] :
      ( ( ~ m1_subset_1(X15,k1_zfmisc_1(X16))
        | r1_tarski(X15,X16) )
      & ( ~ r1_tarski(X15,X16)
        | m1_subset_1(X15,k1_zfmisc_1(X16)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_8,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_10,plain,(
    ! [X20,X21,X22,X23,X24] :
      ( ( r2_hidden(esk2_5(X20,X21,X22,X23,X24),X20)
        | ~ r2_hidden(X24,k7_relset_1(X20,X21,X23,X22))
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,X20,X21)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( r2_hidden(esk2_5(X20,X21,X22,X23,X24),X22)
        | ~ r2_hidden(X24,k7_relset_1(X20,X21,X23,X22))
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,X20,X21)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( X24 = k1_funct_1(X23,esk2_5(X20,X21,X22,X23,X24))
        | ~ r2_hidden(X24,k7_relset_1(X20,X21,X23,X22))
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,X20,X21)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t115_funct_2])])])])])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X5] :
            ~ ( r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))
              & ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ~ ( r2_hidden(X6,X3)
                      & X5 = k1_funct_1(X4,X6) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t116_funct_2])).

cnf(c_0_12,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X3)
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,plain,
    ( r2_hidden(esk2_5(X1,X2,X3,X4,X5),X1)
    | ~ r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,negated_conjecture,(
    ! [X31] :
      ( v1_funct_1(esk6_0)
      & v1_funct_2(esk6_0,esk3_0,esk4_0)
      & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
      & r2_hidden(esk7_0,k7_relset_1(esk3_0,esk4_0,esk6_0,esk5_0))
      & ( ~ m1_subset_1(X31,esk3_0)
        | ~ r2_hidden(X31,esk5_0)
        | esk7_0 != k1_funct_1(esk6_0,X31) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])).

cnf(c_0_15,plain,
    ( ~ v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_xboole_0(X4)
    | ~ r2_hidden(X5,k7_relset_1(X2,X3,X1,X6))
    | ~ r1_tarski(X2,X4) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( v1_funct_2(esk6_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_20,plain,(
    ! [X13,X14] :
      ( ( ~ m1_subset_1(X14,X13)
        | r2_hidden(X14,X13)
        | v1_xboole_0(X13) )
      & ( ~ r2_hidden(X14,X13)
        | m1_subset_1(X14,X13)
        | v1_xboole_0(X13) )
      & ( ~ m1_subset_1(X14,X13)
        | v1_xboole_0(X14)
        | ~ v1_xboole_0(X13) )
      & ( ~ v1_xboole_0(X14)
        | m1_subset_1(X14,X13)
        | ~ v1_xboole_0(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_21,negated_conjecture,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k7_relset_1(esk3_0,esk4_0,esk6_0,X3))
    | ~ r1_tarski(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk7_0,k7_relset_1(esk3_0,esk4_0,esk6_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( ~ v1_xboole_0(X1)
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( ~ m1_subset_1(X1,esk3_0)
    | ~ r2_hidden(X1,esk5_0)
    | esk7_0 != k1_funct_1(esk6_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_29,plain,
    ( X1 = k1_funct_1(X2,esk2_5(X3,X4,X5,X2,X1))
    | ~ r2_hidden(X1,k7_relset_1(X3,X4,X2,X5))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_30,plain,
    ( m1_subset_1(esk2_5(X1,X2,X3,X4,X5),X1)
    | v1_xboole_0(X1)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X5,k7_relset_1(X1,X2,X4,X3)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_13])).

cnf(c_0_31,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( ~ v1_funct_2(esk6_0,X1,X2)
    | ~ m1_subset_1(esk2_5(X1,X2,X3,esk6_0,esk7_0),esk3_0)
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(esk2_5(X1,X2,X3,esk6_0,esk7_0),esk5_0)
    | ~ r2_hidden(esk7_0,k7_relset_1(X1,X2,esk6_0,X3)) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_18])])])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk2_5(esk3_0,esk4_0,X1,esk6_0,X2),esk3_0)
    | ~ r2_hidden(X2,k7_relset_1(esk3_0,esk4_0,esk6_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_16]),c_0_17]),c_0_18])]),c_0_31])).

cnf(c_0_34,plain,
    ( r2_hidden(esk2_5(X1,X2,X3,X4,X5),X3)
    | ~ r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_36,negated_conjecture,
    ( ~ r2_hidden(esk2_5(esk3_0,esk4_0,X1,esk6_0,esk7_0),esk5_0)
    | ~ r2_hidden(esk7_0,k7_relset_1(esk3_0,esk4_0,esk6_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_17]),c_0_16])])).

cnf(c_0_37,plain,
    ( r2_hidden(esk2_5(X1,X2,X3,X4,X5),X3)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ v1_funct_1(X4)
    | ~ r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))
    | ~ r1_tarski(X4,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_9])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(esk6_0,k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_16])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_22]),c_0_17]),c_0_18]),c_0_38])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:03:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.45  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S03DN
% 0.19/0.45  # and selection function PSelectComplexExceptRRHorn.
% 0.19/0.45  #
% 0.19/0.45  # Preprocessing time       : 0.028 s
% 0.19/0.45  # Presaturation interreduction done
% 0.19/0.45  
% 0.19/0.45  # Proof found!
% 0.19/0.45  # SZS status Theorem
% 0.19/0.45  # SZS output start CNFRefutation
% 0.19/0.45  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.19/0.45  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.45  fof(t115_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:~(((r2_hidden(X6,X1)&r2_hidden(X6,X3))&X5=k1_funct_1(X4,X6)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_funct_2)).
% 0.19/0.45  fof(t116_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:(m1_subset_1(X6,X1)=>~((r2_hidden(X6,X3)&X5=k1_funct_1(X4,X6))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_funct_2)).
% 0.19/0.45  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.45  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.19/0.45  fof(c_0_6, plain, ![X17, X18, X19]:(~r2_hidden(X17,X18)|~m1_subset_1(X18,k1_zfmisc_1(X19))|~v1_xboole_0(X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.19/0.45  fof(c_0_7, plain, ![X15, X16]:((~m1_subset_1(X15,k1_zfmisc_1(X16))|r1_tarski(X15,X16))&(~r1_tarski(X15,X16)|m1_subset_1(X15,k1_zfmisc_1(X16)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.45  cnf(c_0_8, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.45  cnf(c_0_9, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.45  fof(c_0_10, plain, ![X20, X21, X22, X23, X24]:(((r2_hidden(esk2_5(X20,X21,X22,X23,X24),X20)|~r2_hidden(X24,k7_relset_1(X20,X21,X23,X22))|(~v1_funct_1(X23)|~v1_funct_2(X23,X20,X21)|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))))&(r2_hidden(esk2_5(X20,X21,X22,X23,X24),X22)|~r2_hidden(X24,k7_relset_1(X20,X21,X23,X22))|(~v1_funct_1(X23)|~v1_funct_2(X23,X20,X21)|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X20,X21))))))&(X24=k1_funct_1(X23,esk2_5(X20,X21,X22,X23,X24))|~r2_hidden(X24,k7_relset_1(X20,X21,X23,X22))|(~v1_funct_1(X23)|~v1_funct_2(X23,X20,X21)|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t115_funct_2])])])])])).
% 0.19/0.45  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:(m1_subset_1(X6,X1)=>~((r2_hidden(X6,X3)&X5=k1_funct_1(X4,X6)))))))), inference(assume_negation,[status(cth)],[t116_funct_2])).
% 0.19/0.45  cnf(c_0_12, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X3)|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.19/0.45  cnf(c_0_13, plain, (r2_hidden(esk2_5(X1,X2,X3,X4,X5),X1)|~r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.45  fof(c_0_14, negated_conjecture, ![X31]:(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk3_0,esk4_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))))&(r2_hidden(esk7_0,k7_relset_1(esk3_0,esk4_0,esk6_0,esk5_0))&(~m1_subset_1(X31,esk3_0)|(~r2_hidden(X31,esk5_0)|esk7_0!=k1_funct_1(esk6_0,X31))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])).
% 0.19/0.45  cnf(c_0_15, plain, (~v1_funct_2(X1,X2,X3)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_xboole_0(X4)|~r2_hidden(X5,k7_relset_1(X2,X3,X1,X6))|~r1_tarski(X2,X4)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.19/0.45  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.45  cnf(c_0_17, negated_conjecture, (v1_funct_2(esk6_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.45  cnf(c_0_18, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.45  fof(c_0_19, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.45  fof(c_0_20, plain, ![X13, X14]:(((~m1_subset_1(X14,X13)|r2_hidden(X14,X13)|v1_xboole_0(X13))&(~r2_hidden(X14,X13)|m1_subset_1(X14,X13)|v1_xboole_0(X13)))&((~m1_subset_1(X14,X13)|v1_xboole_0(X14)|~v1_xboole_0(X13))&(~v1_xboole_0(X14)|m1_subset_1(X14,X13)|~v1_xboole_0(X13)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.19/0.45  cnf(c_0_21, negated_conjecture, (~v1_xboole_0(X1)|~r2_hidden(X2,k7_relset_1(esk3_0,esk4_0,esk6_0,X3))|~r1_tarski(esk3_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18])])).
% 0.19/0.45  cnf(c_0_22, negated_conjecture, (r2_hidden(esk7_0,k7_relset_1(esk3_0,esk4_0,esk6_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.45  cnf(c_0_23, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.45  cnf(c_0_24, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.45  cnf(c_0_25, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.45  cnf(c_0_26, negated_conjecture, (~v1_xboole_0(X1)|~r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.45  cnf(c_0_27, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.45  cnf(c_0_28, negated_conjecture, (~m1_subset_1(X1,esk3_0)|~r2_hidden(X1,esk5_0)|esk7_0!=k1_funct_1(esk6_0,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.45  cnf(c_0_29, plain, (X1=k1_funct_1(X2,esk2_5(X3,X4,X5,X2,X1))|~r2_hidden(X1,k7_relset_1(X3,X4,X2,X5))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X4)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.45  cnf(c_0_30, plain, (m1_subset_1(esk2_5(X1,X2,X3,X4,X5),X1)|v1_xboole_0(X1)|~v1_funct_2(X4,X1,X2)|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))), inference(spm,[status(thm)],[c_0_25, c_0_13])).
% 0.19/0.45  cnf(c_0_31, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.45  cnf(c_0_32, negated_conjecture, (~v1_funct_2(esk6_0,X1,X2)|~m1_subset_1(esk2_5(X1,X2,X3,esk6_0,esk7_0),esk3_0)|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r2_hidden(esk2_5(X1,X2,X3,esk6_0,esk7_0),esk5_0)|~r2_hidden(esk7_0,k7_relset_1(X1,X2,esk6_0,X3))), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_18])])])).
% 0.19/0.45  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk2_5(esk3_0,esk4_0,X1,esk6_0,X2),esk3_0)|~r2_hidden(X2,k7_relset_1(esk3_0,esk4_0,esk6_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_16]), c_0_17]), c_0_18])]), c_0_31])).
% 0.19/0.45  cnf(c_0_34, plain, (r2_hidden(esk2_5(X1,X2,X3,X4,X5),X3)|~r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.45  cnf(c_0_35, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.45  cnf(c_0_36, negated_conjecture, (~r2_hidden(esk2_5(esk3_0,esk4_0,X1,esk6_0,esk7_0),esk5_0)|~r2_hidden(esk7_0,k7_relset_1(esk3_0,esk4_0,esk6_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_17]), c_0_16])])).
% 0.19/0.45  cnf(c_0_37, plain, (r2_hidden(esk2_5(X1,X2,X3,X4,X5),X3)|~v1_funct_2(X4,X1,X2)|~v1_funct_1(X4)|~r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))|~r1_tarski(X4,k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_34, c_0_9])).
% 0.19/0.45  cnf(c_0_38, negated_conjecture, (r1_tarski(esk6_0,k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_35, c_0_16])).
% 0.19/0.45  cnf(c_0_39, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_22]), c_0_17]), c_0_18]), c_0_38])]), ['proof']).
% 0.19/0.45  # SZS output end CNFRefutation
% 0.19/0.45  # Proof object total steps             : 40
% 0.19/0.45  # Proof object clause steps            : 27
% 0.19/0.45  # Proof object formula steps           : 13
% 0.19/0.45  # Proof object conjectures             : 16
% 0.19/0.45  # Proof object clause conjectures      : 13
% 0.19/0.45  # Proof object formula conjectures     : 3
% 0.19/0.45  # Proof object initial clauses used    : 14
% 0.19/0.45  # Proof object initial formulas used   : 6
% 0.19/0.45  # Proof object generating inferences   : 13
% 0.19/0.45  # Proof object simplifying inferences  : 18
% 0.19/0.45  # Training examples: 0 positive, 0 negative
% 0.19/0.45  # Parsed axioms                        : 6
% 0.19/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.45  # Initial clauses                      : 18
% 0.19/0.45  # Removed in clause preprocessing      : 0
% 0.19/0.45  # Initial clauses in saturation        : 18
% 0.19/0.45  # Processed clauses                    : 772
% 0.19/0.45  # ...of these trivial                  : 0
% 0.19/0.45  # ...subsumed                          : 465
% 0.19/0.45  # ...remaining for further processing  : 307
% 0.19/0.45  # Other redundant clauses eliminated   : 1
% 0.19/0.45  # Clauses deleted for lack of memory   : 0
% 0.19/0.45  # Backward-subsumed                    : 58
% 0.19/0.45  # Backward-rewritten                   : 2
% 0.19/0.45  # Generated clauses                    : 2251
% 0.19/0.45  # ...of the previous two non-trivial   : 2200
% 0.19/0.45  # Contextual simplify-reflections      : 17
% 0.19/0.45  # Paramodulations                      : 2247
% 0.19/0.45  # Factorizations                       : 2
% 0.19/0.45  # Equation resolutions                 : 1
% 0.19/0.45  # Propositional unsat checks           : 0
% 0.19/0.45  #    Propositional check models        : 0
% 0.19/0.45  #    Propositional check unsatisfiable : 0
% 0.19/0.45  #    Propositional clauses             : 0
% 0.19/0.45  #    Propositional clauses after purity: 0
% 0.19/0.45  #    Propositional unsat core size     : 0
% 0.19/0.45  #    Propositional preprocessing time  : 0.000
% 0.19/0.45  #    Propositional encoding time       : 0.000
% 0.19/0.45  #    Propositional solver time         : 0.000
% 0.19/0.45  #    Success case prop preproc time    : 0.000
% 0.19/0.45  #    Success case prop encoding time   : 0.000
% 0.19/0.45  #    Success case prop solver time     : 0.000
% 0.19/0.45  # Current number of processed clauses  : 228
% 0.19/0.45  #    Positive orientable unit clauses  : 8
% 0.19/0.45  #    Positive unorientable unit clauses: 0
% 0.19/0.45  #    Negative unit clauses             : 3
% 0.19/0.45  #    Non-unit-clauses                  : 217
% 0.19/0.45  # Current number of unprocessed clauses: 1416
% 0.19/0.45  # ...number of literals in the above   : 9055
% 0.19/0.45  # Current number of archived formulas  : 0
% 0.19/0.45  # Current number of archived clauses   : 79
% 0.19/0.45  # Clause-clause subsumption calls (NU) : 17249
% 0.19/0.45  # Rec. Clause-clause subsumption calls : 6229
% 0.19/0.45  # Non-unit clause-clause subsumptions  : 495
% 0.19/0.45  # Unit Clause-clause subsumption calls : 115
% 0.19/0.45  # Rewrite failures with RHS unbound    : 0
% 0.19/0.45  # BW rewrite match attempts            : 33
% 0.19/0.45  # BW rewrite match successes           : 2
% 0.19/0.45  # Condensation attempts                : 0
% 0.19/0.45  # Condensation successes               : 0
% 0.19/0.45  # Termbank termtop insertions          : 51407
% 0.19/0.45  
% 0.19/0.45  # -------------------------------------------------
% 0.19/0.45  # User time                : 0.107 s
% 0.19/0.45  # System time              : 0.004 s
% 0.19/0.45  # Total time               : 0.110 s
% 0.19/0.45  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
