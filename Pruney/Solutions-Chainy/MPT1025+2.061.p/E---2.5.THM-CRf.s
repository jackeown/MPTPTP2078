%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:43 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   22 (  62 expanded)
%              Number of clauses        :   15 (  21 expanded)
%              Number of leaves         :    3 (  15 expanded)
%              Depth                    :    7
%              Number of atoms          :   86 ( 346 expanded)
%              Number of equality atoms :    7 (  41 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   15 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_funct_2)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(c_0_3,negated_conjecture,(
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

fof(c_0_4,negated_conjecture,(
    ! [X20] :
      ( v1_funct_1(esk5_0)
      & v1_funct_2(esk5_0,esk2_0,esk3_0)
      & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
      & r2_hidden(esk6_0,k7_relset_1(esk2_0,esk3_0,esk5_0,esk4_0))
      & ( ~ m1_subset_1(X20,esk2_0)
        | ~ r2_hidden(X20,esk4_0)
        | esk6_0 != k1_funct_1(esk5_0,X20) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])).

fof(c_0_5,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( r2_hidden(esk1_5(X9,X10,X11,X12,X13),X9)
        | ~ r2_hidden(X13,k7_relset_1(X9,X10,X12,X11))
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,X9,X10)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) )
      & ( r2_hidden(esk1_5(X9,X10,X11,X12,X13),X11)
        | ~ r2_hidden(X13,k7_relset_1(X9,X10,X12,X11))
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,X9,X10)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) )
      & ( X13 = k1_funct_1(X12,esk1_5(X9,X10,X11,X12,X13))
        | ~ r2_hidden(X13,k7_relset_1(X9,X10,X12,X11))
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,X9,X10)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t115_funct_2])])])])])).

cnf(c_0_6,negated_conjecture,
    ( ~ m1_subset_1(X1,esk2_0)
    | ~ r2_hidden(X1,esk4_0)
    | esk6_0 != k1_funct_1(esk5_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( X1 = k1_funct_1(X2,esk1_5(X3,X4,X5,X2,X1))
    | ~ r2_hidden(X1,k7_relset_1(X3,X4,X2,X5))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,negated_conjecture,
    ( ~ v1_funct_2(esk5_0,X1,X2)
    | ~ m1_subset_1(esk1_5(X1,X2,X3,esk5_0,esk6_0),esk2_0)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(esk1_5(X1,X2,X3,esk5_0,esk6_0),esk4_0)
    | ~ r2_hidden(esk6_0,k7_relset_1(X1,X2,esk5_0,X3)) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_7]),c_0_8])])])).

cnf(c_0_10,negated_conjecture,
    ( v1_funct_2(esk5_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_12,plain,(
    ! [X7,X8] :
      ( ~ r2_hidden(X7,X8)
      | m1_subset_1(X7,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_13,plain,
    ( r2_hidden(esk1_5(X1,X2,X3,X4,X5),X1)
    | ~ r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,negated_conjecture,
    ( ~ m1_subset_1(esk1_5(esk2_0,esk3_0,X1,esk5_0,esk6_0),esk2_0)
    | ~ r2_hidden(esk1_5(esk2_0,esk3_0,X1,esk5_0,esk6_0),esk4_0)
    | ~ r2_hidden(esk6_0,k7_relset_1(esk2_0,esk3_0,esk5_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11])])).

cnf(c_0_15,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk1_5(esk2_0,esk3_0,X1,esk5_0,X2),esk2_0)
    | ~ r2_hidden(X2,k7_relset_1(esk2_0,esk3_0,esk5_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_10]),c_0_8]),c_0_11])])).

cnf(c_0_17,plain,
    ( r2_hidden(esk1_5(X1,X2,X3,X4,X5),X3)
    | ~ r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_18,negated_conjecture,
    ( ~ r2_hidden(esk1_5(esk2_0,esk3_0,X1,esk5_0,esk6_0),esk4_0)
    | ~ r2_hidden(esk6_0,k7_relset_1(esk2_0,esk3_0,esk5_0,X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk1_5(esk2_0,esk3_0,X1,esk5_0,X2),X1)
    | ~ r2_hidden(X2,k7_relset_1(esk2_0,esk3_0,esk5_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_10]),c_0_8]),c_0_11])])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk6_0,k7_relset_1(esk2_0,esk3_0,esk5_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_21,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:52:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S050A
% 0.19/0.36  # and selection function PSelectNewComplexExceptUniqMaxHorn.
% 0.19/0.36  #
% 0.19/0.36  # Preprocessing time       : 0.026 s
% 0.19/0.36  # Presaturation interreduction done
% 0.19/0.36  
% 0.19/0.36  # Proof found!
% 0.19/0.36  # SZS status Theorem
% 0.19/0.36  # SZS output start CNFRefutation
% 0.19/0.36  fof(t116_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:(m1_subset_1(X6,X1)=>~((r2_hidden(X6,X3)&X5=k1_funct_1(X4,X6))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_funct_2)).
% 0.19/0.36  fof(t115_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:~(((r2_hidden(X6,X1)&r2_hidden(X6,X3))&X5=k1_funct_1(X4,X6)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t115_funct_2)).
% 0.19/0.36  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 0.19/0.36  fof(c_0_3, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:(m1_subset_1(X6,X1)=>~((r2_hidden(X6,X3)&X5=k1_funct_1(X4,X6)))))))), inference(assume_negation,[status(cth)],[t116_funct_2])).
% 0.19/0.36  fof(c_0_4, negated_conjecture, ![X20]:(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk2_0,esk3_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))))&(r2_hidden(esk6_0,k7_relset_1(esk2_0,esk3_0,esk5_0,esk4_0))&(~m1_subset_1(X20,esk2_0)|(~r2_hidden(X20,esk4_0)|esk6_0!=k1_funct_1(esk5_0,X20))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])).
% 0.19/0.36  fof(c_0_5, plain, ![X9, X10, X11, X12, X13]:(((r2_hidden(esk1_5(X9,X10,X11,X12,X13),X9)|~r2_hidden(X13,k7_relset_1(X9,X10,X12,X11))|(~v1_funct_1(X12)|~v1_funct_2(X12,X9,X10)|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))))&(r2_hidden(esk1_5(X9,X10,X11,X12,X13),X11)|~r2_hidden(X13,k7_relset_1(X9,X10,X12,X11))|(~v1_funct_1(X12)|~v1_funct_2(X12,X9,X10)|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X9,X10))))))&(X13=k1_funct_1(X12,esk1_5(X9,X10,X11,X12,X13))|~r2_hidden(X13,k7_relset_1(X9,X10,X12,X11))|(~v1_funct_1(X12)|~v1_funct_2(X12,X9,X10)|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t115_funct_2])])])])])).
% 0.19/0.36  cnf(c_0_6, negated_conjecture, (~m1_subset_1(X1,esk2_0)|~r2_hidden(X1,esk4_0)|esk6_0!=k1_funct_1(esk5_0,X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.19/0.36  cnf(c_0_7, plain, (X1=k1_funct_1(X2,esk1_5(X3,X4,X5,X2,X1))|~r2_hidden(X1,k7_relset_1(X3,X4,X2,X5))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X4)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.36  cnf(c_0_8, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.19/0.36  cnf(c_0_9, negated_conjecture, (~v1_funct_2(esk5_0,X1,X2)|~m1_subset_1(esk1_5(X1,X2,X3,esk5_0,esk6_0),esk2_0)|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r2_hidden(esk1_5(X1,X2,X3,esk5_0,esk6_0),esk4_0)|~r2_hidden(esk6_0,k7_relset_1(X1,X2,esk5_0,X3))), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6, c_0_7]), c_0_8])])])).
% 0.19/0.36  cnf(c_0_10, negated_conjecture, (v1_funct_2(esk5_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.19/0.36  cnf(c_0_11, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.19/0.36  fof(c_0_12, plain, ![X7, X8]:(~r2_hidden(X7,X8)|m1_subset_1(X7,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.19/0.36  cnf(c_0_13, plain, (r2_hidden(esk1_5(X1,X2,X3,X4,X5),X1)|~r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.36  cnf(c_0_14, negated_conjecture, (~m1_subset_1(esk1_5(esk2_0,esk3_0,X1,esk5_0,esk6_0),esk2_0)|~r2_hidden(esk1_5(esk2_0,esk3_0,X1,esk5_0,esk6_0),esk4_0)|~r2_hidden(esk6_0,k7_relset_1(esk2_0,esk3_0,esk5_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_11])])).
% 0.19/0.36  cnf(c_0_15, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.36  cnf(c_0_16, negated_conjecture, (r2_hidden(esk1_5(esk2_0,esk3_0,X1,esk5_0,X2),esk2_0)|~r2_hidden(X2,k7_relset_1(esk2_0,esk3_0,esk5_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_10]), c_0_8]), c_0_11])])).
% 0.19/0.36  cnf(c_0_17, plain, (r2_hidden(esk1_5(X1,X2,X3,X4,X5),X3)|~r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.36  cnf(c_0_18, negated_conjecture, (~r2_hidden(esk1_5(esk2_0,esk3_0,X1,esk5_0,esk6_0),esk4_0)|~r2_hidden(esk6_0,k7_relset_1(esk2_0,esk3_0,esk5_0,X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16])).
% 0.19/0.36  cnf(c_0_19, negated_conjecture, (r2_hidden(esk1_5(esk2_0,esk3_0,X1,esk5_0,X2),X1)|~r2_hidden(X2,k7_relset_1(esk2_0,esk3_0,esk5_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_10]), c_0_8]), c_0_11])])).
% 0.19/0.36  cnf(c_0_20, negated_conjecture, (r2_hidden(esk6_0,k7_relset_1(esk2_0,esk3_0,esk5_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.19/0.36  cnf(c_0_21, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])]), ['proof']).
% 0.19/0.36  # SZS output end CNFRefutation
% 0.19/0.36  # Proof object total steps             : 22
% 0.19/0.36  # Proof object clause steps            : 15
% 0.19/0.36  # Proof object formula steps           : 7
% 0.19/0.36  # Proof object conjectures             : 14
% 0.19/0.36  # Proof object clause conjectures      : 11
% 0.19/0.36  # Proof object formula conjectures     : 3
% 0.19/0.36  # Proof object initial clauses used    : 9
% 0.19/0.36  # Proof object initial formulas used   : 3
% 0.19/0.36  # Proof object generating inferences   : 6
% 0.19/0.36  # Proof object simplifying inferences  : 14
% 0.19/0.36  # Training examples: 0 positive, 0 negative
% 0.19/0.36  # Parsed axioms                        : 3
% 0.19/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.36  # Initial clauses                      : 9
% 0.19/0.36  # Removed in clause preprocessing      : 0
% 0.19/0.36  # Initial clauses in saturation        : 9
% 0.19/0.36  # Processed clauses                    : 23
% 0.19/0.36  # ...of these trivial                  : 0
% 0.19/0.36  # ...subsumed                          : 0
% 0.19/0.36  # ...remaining for further processing  : 23
% 0.19/0.36  # Other redundant clauses eliminated   : 1
% 0.19/0.36  # Clauses deleted for lack of memory   : 0
% 0.19/0.36  # Backward-subsumed                    : 1
% 0.19/0.36  # Backward-rewritten                   : 0
% 0.19/0.36  # Generated clauses                    : 7
% 0.19/0.36  # ...of the previous two non-trivial   : 5
% 0.19/0.36  # Contextual simplify-reflections      : 1
% 0.19/0.36  # Paramodulations                      : 6
% 0.19/0.36  # Factorizations                       : 0
% 0.19/0.36  # Equation resolutions                 : 1
% 0.19/0.36  # Propositional unsat checks           : 0
% 0.19/0.36  #    Propositional check models        : 0
% 0.19/0.36  #    Propositional check unsatisfiable : 0
% 0.19/0.36  #    Propositional clauses             : 0
% 0.19/0.36  #    Propositional clauses after purity: 0
% 0.19/0.36  #    Propositional unsat core size     : 0
% 0.19/0.36  #    Propositional preprocessing time  : 0.000
% 0.19/0.36  #    Propositional encoding time       : 0.000
% 0.19/0.36  #    Propositional solver time         : 0.000
% 0.19/0.36  #    Success case prop preproc time    : 0.000
% 0.19/0.36  #    Success case prop encoding time   : 0.000
% 0.19/0.36  #    Success case prop solver time     : 0.000
% 0.19/0.36  # Current number of processed clauses  : 13
% 0.19/0.36  #    Positive orientable unit clauses  : 4
% 0.19/0.36  #    Positive unorientable unit clauses: 0
% 0.19/0.36  #    Negative unit clauses             : 0
% 0.19/0.36  #    Non-unit-clauses                  : 9
% 0.19/0.36  # Current number of unprocessed clauses: 0
% 0.19/0.36  # ...number of literals in the above   : 0
% 0.19/0.36  # Current number of archived formulas  : 0
% 0.19/0.36  # Current number of archived clauses   : 10
% 0.19/0.36  # Clause-clause subsumption calls (NU) : 70
% 0.19/0.36  # Rec. Clause-clause subsumption calls : 13
% 0.19/0.36  # Non-unit clause-clause subsumptions  : 2
% 0.19/0.36  # Unit Clause-clause subsumption calls : 0
% 0.19/0.36  # Rewrite failures with RHS unbound    : 0
% 0.19/0.36  # BW rewrite match attempts            : 0
% 0.19/0.36  # BW rewrite match successes           : 0
% 0.19/0.36  # Condensation attempts                : 0
% 0.19/0.36  # Condensation successes               : 0
% 0.19/0.36  # Termbank termtop insertions          : 1114
% 0.19/0.36  
% 0.19/0.36  # -------------------------------------------------
% 0.19/0.36  # User time                : 0.025 s
% 0.19/0.36  # System time              : 0.004 s
% 0.19/0.36  # Total time               : 0.029 s
% 0.19/0.36  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
