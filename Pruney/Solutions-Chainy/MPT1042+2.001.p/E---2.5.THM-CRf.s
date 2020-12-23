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
% DateTime   : Thu Dec  3 11:07:07 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   33 ( 194 expanded)
%              Number of clauses        :   26 (  79 expanded)
%              Number of leaves         :    3 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :  172 (1506 expanded)
%              Number of equality atoms :   26 ( 210 expanded)
%              Maximal formula depth    :   26 (   5 average)
%              Maximal clause size      :   68 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d7_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( X4 = k5_partfun1(X1,X2,X3)
        <=> ! [X5] :
              ( r2_hidden(X5,X4)
            <=> ? [X6] :
                  ( v1_funct_1(X6)
                  & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & X6 = X5
                  & v1_partfun1(X6,X1)
                  & r1_partfun1(X3,X6) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_partfun1)).

fof(t158_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( r2_hidden(X4,k5_partfun1(X1,X2,X3))
         => ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_2)).

fof(cc1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v1_partfun1(X3,X1) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

fof(c_0_3,plain,(
    ! [X10,X11,X12,X13,X14,X16,X17,X18,X20] :
      ( ( v1_funct_1(esk1_5(X10,X11,X12,X13,X14))
        | ~ r2_hidden(X14,X13)
        | X13 != k5_partfun1(X10,X11,X12)
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) )
      & ( m1_subset_1(esk1_5(X10,X11,X12,X13,X14),k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
        | ~ r2_hidden(X14,X13)
        | X13 != k5_partfun1(X10,X11,X12)
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) )
      & ( esk1_5(X10,X11,X12,X13,X14) = X14
        | ~ r2_hidden(X14,X13)
        | X13 != k5_partfun1(X10,X11,X12)
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) )
      & ( v1_partfun1(esk1_5(X10,X11,X12,X13,X14),X10)
        | ~ r2_hidden(X14,X13)
        | X13 != k5_partfun1(X10,X11,X12)
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) )
      & ( r1_partfun1(X12,esk1_5(X10,X11,X12,X13,X14))
        | ~ r2_hidden(X14,X13)
        | X13 != k5_partfun1(X10,X11,X12)
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) )
      & ( ~ v1_funct_1(X17)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
        | X17 != X16
        | ~ v1_partfun1(X17,X10)
        | ~ r1_partfun1(X12,X17)
        | r2_hidden(X16,X13)
        | X13 != k5_partfun1(X10,X11,X12)
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) )
      & ( ~ r2_hidden(esk2_4(X10,X11,X12,X18),X18)
        | ~ v1_funct_1(X20)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
        | X20 != esk2_4(X10,X11,X12,X18)
        | ~ v1_partfun1(X20,X10)
        | ~ r1_partfun1(X12,X20)
        | X18 = k5_partfun1(X10,X11,X12)
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) )
      & ( v1_funct_1(esk3_4(X10,X11,X12,X18))
        | r2_hidden(esk2_4(X10,X11,X12,X18),X18)
        | X18 = k5_partfun1(X10,X11,X12)
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) )
      & ( m1_subset_1(esk3_4(X10,X11,X12,X18),k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
        | r2_hidden(esk2_4(X10,X11,X12,X18),X18)
        | X18 = k5_partfun1(X10,X11,X12)
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) )
      & ( esk3_4(X10,X11,X12,X18) = esk2_4(X10,X11,X12,X18)
        | r2_hidden(esk2_4(X10,X11,X12,X18),X18)
        | X18 = k5_partfun1(X10,X11,X12)
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) )
      & ( v1_partfun1(esk3_4(X10,X11,X12,X18),X10)
        | r2_hidden(esk2_4(X10,X11,X12,X18),X18)
        | X18 = k5_partfun1(X10,X11,X12)
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) )
      & ( r1_partfun1(X12,esk3_4(X10,X11,X12,X18))
        | r2_hidden(esk2_4(X10,X11,X12,X18),X18)
        | X18 = k5_partfun1(X10,X11,X12)
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_partfun1])])])])])])).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X4] :
            ( r2_hidden(X4,k5_partfun1(X1,X2,X3))
           => ( v1_funct_1(X4)
              & v1_funct_2(X4,X1,X2)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t158_funct_2])).

cnf(c_0_5,plain,
    ( v1_funct_1(esk1_5(X1,X2,X3,X4,X5))
    | ~ r2_hidden(X5,X4)
    | X4 != k5_partfun1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

fof(c_0_6,negated_conjecture,
    ( v1_funct_1(esk6_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
    & r2_hidden(esk7_0,k5_partfun1(esk4_0,esk5_0,esk6_0))
    & ( ~ v1_funct_1(esk7_0)
      | ~ v1_funct_2(esk7_0,esk4_0,esk5_0)
      | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

cnf(c_0_7,plain,
    ( esk1_5(X1,X2,X3,X4,X5) = X5
    | ~ r2_hidden(X5,X4)
    | X4 != k5_partfun1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_8,plain,
    ( v1_funct_1(esk1_5(X1,X2,X3,k5_partfun1(X1,X2,X3),X4))
    | ~ r2_hidden(X4,k5_partfun1(X1,X2,X3))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( esk1_5(X1,X2,X3,k5_partfun1(X1,X2,X3),X4) = X4
    | ~ r2_hidden(X4,k5_partfun1(X1,X2,X3))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( m1_subset_1(esk1_5(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X5,X4)
    | X4 != k5_partfun1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_13,negated_conjecture,
    ( v1_funct_1(esk1_5(esk4_0,esk5_0,esk6_0,k5_partfun1(esk4_0,esk5_0,esk6_0),X1))
    | ~ r2_hidden(X1,k5_partfun1(esk4_0,esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10])])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk7_0,k5_partfun1(esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_15,negated_conjecture,
    ( esk1_5(esk4_0,esk5_0,esk6_0,k5_partfun1(esk4_0,esk5_0,esk6_0),X1) = X1
    | ~ r2_hidden(X1,k5_partfun1(esk4_0,esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_9]),c_0_10])])).

cnf(c_0_16,plain,
    ( m1_subset_1(esk1_5(X1,X2,X3,k5_partfun1(X1,X2,X3),X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X4,k5_partfun1(X1,X2,X3))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( v1_funct_1(esk1_5(esk4_0,esk5_0,esk6_0,k5_partfun1(esk4_0,esk5_0,esk6_0),esk7_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( esk1_5(esk4_0,esk5_0,esk6_0,k5_partfun1(esk4_0,esk5_0,esk6_0),esk7_0) = esk7_0 ),
    inference(spm,[status(thm)],[c_0_15,c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk1_5(esk4_0,esk5_0,esk6_0,k5_partfun1(esk4_0,esk5_0,esk6_0),X1),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
    | ~ r2_hidden(X1,k5_partfun1(esk4_0,esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_9]),c_0_10])])).

cnf(c_0_20,negated_conjecture,
    ( ~ v1_funct_1(esk7_0)
    | ~ v1_funct_2(esk7_0,esk4_0,esk5_0)
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk1_5(esk4_0,esk5_0,esk6_0,k5_partfun1(esk4_0,esk5_0,esk6_0),esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_14])).

cnf(c_0_23,plain,
    ( v1_partfun1(esk1_5(X1,X2,X3,X4,X5),X1)
    | ~ r2_hidden(X5,X4)
    | X4 != k5_partfun1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

fof(c_0_24,plain,(
    ! [X7,X8,X9] :
      ( ( v1_funct_1(X9)
        | ~ v1_funct_1(X9)
        | ~ v1_partfun1(X9,X7)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) )
      & ( v1_funct_2(X9,X7,X8)
        | ~ v1_funct_1(X9)
        | ~ v1_partfun1(X9,X7)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).

cnf(c_0_25,negated_conjecture,
    ( ~ v1_funct_2(esk7_0,esk4_0,esk5_0)
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21])])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(rw,[status(thm)],[c_0_22,c_0_18])).

cnf(c_0_27,plain,
    ( v1_partfun1(esk1_5(X1,X2,X3,k5_partfun1(X1,X2,X3),X4),X1)
    | ~ r2_hidden(X4,k5_partfun1(X1,X2,X3))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( ~ v1_funct_2(esk7_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26])])).

cnf(c_0_30,negated_conjecture,
    ( v1_partfun1(esk1_5(esk4_0,esk5_0,esk6_0,k5_partfun1(esk4_0,esk5_0,esk6_0),X1),esk4_0)
    | ~ r2_hidden(X1,k5_partfun1(esk4_0,esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_9]),c_0_10])])).

cnf(c_0_31,negated_conjecture,
    ( ~ v1_partfun1(esk7_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_26]),c_0_21])]),c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_14]),c_0_18]),c_0_31]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:42:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S08BA
% 0.13/0.38  # and selection function SelectCQPrecWNTNp.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(d7_partfun1, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(X4=k5_partfun1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>?[X6]:((((v1_funct_1(X6)&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&X6=X5)&v1_partfun1(X6,X1))&r1_partfun1(X3,X6))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_partfun1)).
% 0.13/0.38  fof(t158_funct_2, conjecture, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(r2_hidden(X4,k5_partfun1(X1,X2,X3))=>((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_2)).
% 0.13/0.38  fof(cc1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_partfun1(X3,X1))=>(v1_funct_1(X3)&v1_funct_2(X3,X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 0.13/0.38  fof(c_0_3, plain, ![X10, X11, X12, X13, X14, X16, X17, X18, X20]:(((((((v1_funct_1(esk1_5(X10,X11,X12,X13,X14))|~r2_hidden(X14,X13)|X13!=k5_partfun1(X10,X11,X12)|(~v1_funct_1(X12)|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))))&(m1_subset_1(esk1_5(X10,X11,X12,X13,X14),k1_zfmisc_1(k2_zfmisc_1(X10,X11)))|~r2_hidden(X14,X13)|X13!=k5_partfun1(X10,X11,X12)|(~v1_funct_1(X12)|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))))))&(esk1_5(X10,X11,X12,X13,X14)=X14|~r2_hidden(X14,X13)|X13!=k5_partfun1(X10,X11,X12)|(~v1_funct_1(X12)|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))))))&(v1_partfun1(esk1_5(X10,X11,X12,X13,X14),X10)|~r2_hidden(X14,X13)|X13!=k5_partfun1(X10,X11,X12)|(~v1_funct_1(X12)|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))))))&(r1_partfun1(X12,esk1_5(X10,X11,X12,X13,X14))|~r2_hidden(X14,X13)|X13!=k5_partfun1(X10,X11,X12)|(~v1_funct_1(X12)|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))))))&(~v1_funct_1(X17)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))|X17!=X16|~v1_partfun1(X17,X10)|~r1_partfun1(X12,X17)|r2_hidden(X16,X13)|X13!=k5_partfun1(X10,X11,X12)|(~v1_funct_1(X12)|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))))))&((~r2_hidden(esk2_4(X10,X11,X12,X18),X18)|(~v1_funct_1(X20)|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))|X20!=esk2_4(X10,X11,X12,X18)|~v1_partfun1(X20,X10)|~r1_partfun1(X12,X20))|X18=k5_partfun1(X10,X11,X12)|(~v1_funct_1(X12)|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))))&(((((v1_funct_1(esk3_4(X10,X11,X12,X18))|r2_hidden(esk2_4(X10,X11,X12,X18),X18)|X18=k5_partfun1(X10,X11,X12)|(~v1_funct_1(X12)|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))))&(m1_subset_1(esk3_4(X10,X11,X12,X18),k1_zfmisc_1(k2_zfmisc_1(X10,X11)))|r2_hidden(esk2_4(X10,X11,X12,X18),X18)|X18=k5_partfun1(X10,X11,X12)|(~v1_funct_1(X12)|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))))))&(esk3_4(X10,X11,X12,X18)=esk2_4(X10,X11,X12,X18)|r2_hidden(esk2_4(X10,X11,X12,X18),X18)|X18=k5_partfun1(X10,X11,X12)|(~v1_funct_1(X12)|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))))))&(v1_partfun1(esk3_4(X10,X11,X12,X18),X10)|r2_hidden(esk2_4(X10,X11,X12,X18),X18)|X18=k5_partfun1(X10,X11,X12)|(~v1_funct_1(X12)|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))))))&(r1_partfun1(X12,esk3_4(X10,X11,X12,X18))|r2_hidden(esk2_4(X10,X11,X12,X18),X18)|X18=k5_partfun1(X10,X11,X12)|(~v1_funct_1(X12)|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_partfun1])])])])])])).
% 0.13/0.38  fof(c_0_4, negated_conjecture, ~(![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(r2_hidden(X4,k5_partfun1(X1,X2,X3))=>((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))))), inference(assume_negation,[status(cth)],[t158_funct_2])).
% 0.13/0.38  cnf(c_0_5, plain, (v1_funct_1(esk1_5(X1,X2,X3,X4,X5))|~r2_hidden(X5,X4)|X4!=k5_partfun1(X1,X2,X3)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.13/0.38  fof(c_0_6, negated_conjecture, ((v1_funct_1(esk6_0)&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))))&(r2_hidden(esk7_0,k5_partfun1(esk4_0,esk5_0,esk6_0))&(~v1_funct_1(esk7_0)|~v1_funct_2(esk7_0,esk4_0,esk5_0)|~m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.13/0.38  cnf(c_0_7, plain, (esk1_5(X1,X2,X3,X4,X5)=X5|~r2_hidden(X5,X4)|X4!=k5_partfun1(X1,X2,X3)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.13/0.38  cnf(c_0_8, plain, (v1_funct_1(esk1_5(X1,X2,X3,k5_partfun1(X1,X2,X3),X4))|~r2_hidden(X4,k5_partfun1(X1,X2,X3))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_5])).
% 0.13/0.38  cnf(c_0_9, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_10, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_11, plain, (esk1_5(X1,X2,X3,k5_partfun1(X1,X2,X3),X4)=X4|~r2_hidden(X4,k5_partfun1(X1,X2,X3))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_12, plain, (m1_subset_1(esk1_5(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r2_hidden(X5,X4)|X4!=k5_partfun1(X1,X2,X3)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.13/0.38  cnf(c_0_13, negated_conjecture, (v1_funct_1(esk1_5(esk4_0,esk5_0,esk6_0,k5_partfun1(esk4_0,esk5_0,esk6_0),X1))|~r2_hidden(X1,k5_partfun1(esk4_0,esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8, c_0_9]), c_0_10])])).
% 0.13/0.38  cnf(c_0_14, negated_conjecture, (r2_hidden(esk7_0,k5_partfun1(esk4_0,esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_15, negated_conjecture, (esk1_5(esk4_0,esk5_0,esk6_0,k5_partfun1(esk4_0,esk5_0,esk6_0),X1)=X1|~r2_hidden(X1,k5_partfun1(esk4_0,esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_9]), c_0_10])])).
% 0.13/0.38  cnf(c_0_16, plain, (m1_subset_1(esk1_5(X1,X2,X3,k5_partfun1(X1,X2,X3),X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r2_hidden(X4,k5_partfun1(X1,X2,X3))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_17, negated_conjecture, (v1_funct_1(esk1_5(esk4_0,esk5_0,esk6_0,k5_partfun1(esk4_0,esk5_0,esk6_0),esk7_0))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.13/0.38  cnf(c_0_18, negated_conjecture, (esk1_5(esk4_0,esk5_0,esk6_0,k5_partfun1(esk4_0,esk5_0,esk6_0),esk7_0)=esk7_0), inference(spm,[status(thm)],[c_0_15, c_0_14])).
% 0.13/0.38  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk1_5(esk4_0,esk5_0,esk6_0,k5_partfun1(esk4_0,esk5_0,esk6_0),X1),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))|~r2_hidden(X1,k5_partfun1(esk4_0,esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_9]), c_0_10])])).
% 0.13/0.38  cnf(c_0_20, negated_conjecture, (~v1_funct_1(esk7_0)|~v1_funct_2(esk7_0,esk4_0,esk5_0)|~m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_21, negated_conjecture, (v1_funct_1(esk7_0)), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.13/0.38  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk1_5(esk4_0,esk5_0,esk6_0,k5_partfun1(esk4_0,esk5_0,esk6_0),esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(spm,[status(thm)],[c_0_19, c_0_14])).
% 0.13/0.38  cnf(c_0_23, plain, (v1_partfun1(esk1_5(X1,X2,X3,X4,X5),X1)|~r2_hidden(X5,X4)|X4!=k5_partfun1(X1,X2,X3)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.13/0.38  fof(c_0_24, plain, ![X7, X8, X9]:((v1_funct_1(X9)|(~v1_funct_1(X9)|~v1_partfun1(X9,X7))|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))))&(v1_funct_2(X9,X7,X8)|(~v1_funct_1(X9)|~v1_partfun1(X9,X7))|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, (~v1_funct_2(esk7_0,esk4_0,esk5_0)|~m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21])])).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(rw,[status(thm)],[c_0_22, c_0_18])).
% 0.13/0.38  cnf(c_0_27, plain, (v1_partfun1(esk1_5(X1,X2,X3,k5_partfun1(X1,X2,X3),X4),X1)|~r2_hidden(X4,k5_partfun1(X1,X2,X3))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_28, plain, (v1_funct_2(X1,X2,X3)|~v1_funct_1(X1)|~v1_partfun1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.38  cnf(c_0_29, negated_conjecture, (~v1_funct_2(esk7_0,esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_26])])).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, (v1_partfun1(esk1_5(esk4_0,esk5_0,esk6_0,k5_partfun1(esk4_0,esk5_0,esk6_0),X1),esk4_0)|~r2_hidden(X1,k5_partfun1(esk4_0,esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_9]), c_0_10])])).
% 0.13/0.38  cnf(c_0_31, negated_conjecture, (~v1_partfun1(esk7_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_26]), c_0_21])]), c_0_29])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_14]), c_0_18]), c_0_31]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 33
% 0.13/0.38  # Proof object clause steps            : 26
% 0.13/0.38  # Proof object formula steps           : 7
% 0.13/0.38  # Proof object conjectures             : 20
% 0.13/0.38  # Proof object clause conjectures      : 17
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 9
% 0.13/0.38  # Proof object initial formulas used   : 3
% 0.13/0.38  # Proof object generating inferences   : 9
% 0.13/0.38  # Proof object simplifying inferences  : 23
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 3
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 18
% 0.13/0.38  # Removed in clause preprocessing      : 1
% 0.13/0.38  # Initial clauses in saturation        : 17
% 0.13/0.38  # Processed clauses                    : 66
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 2
% 0.13/0.38  # ...remaining for further processing  : 64
% 0.13/0.38  # Other redundant clauses eliminated   : 8
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 4
% 0.13/0.38  # Generated clauses                    : 94
% 0.13/0.38  # ...of the previous two non-trivial   : 94
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 87
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 8
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
% 0.13/0.38  # Current number of processed clauses  : 36
% 0.13/0.38  #    Positive orientable unit clauses  : 7
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 2
% 0.13/0.38  #    Non-unit-clauses                  : 27
% 0.13/0.38  # Current number of unprocessed clauses: 59
% 0.13/0.38  # ...number of literals in the above   : 279
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 21
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 193
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 38
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 1
% 0.13/0.38  # Unit Clause-clause subsumption calls : 53
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 6
% 0.13/0.38  # BW rewrite match successes           : 3
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 4522
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.032 s
% 0.13/0.38  # System time              : 0.003 s
% 0.13/0.38  # Total time               : 0.035 s
% 0.13/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
