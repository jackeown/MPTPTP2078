%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:07 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   24 (  54 expanded)
%              Number of clauses        :   15 (  18 expanded)
%              Number of leaves         :    4 (  13 expanded)
%              Depth                    :    6
%              Number of atoms          :  160 ( 352 expanded)
%              Number of equality atoms :   20 (  20 expanded)
%              Maximal formula depth    :   26 (   6 average)
%              Maximal clause size      :   68 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t156_funct_2,conjecture,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => ! [X3] :
          ( ( v1_funct_1(X3)
            & v1_funct_2(X3,X1,X1)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
         => ( r1_partfun1(X2,X3)
           => r2_hidden(X3,k5_partfun1(X1,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_funct_2)).

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

fof(cc1_partfun1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => v1_partfun1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

fof(cc5_funct_2,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => ( ( v1_funct_1(X3)
              & v1_funct_2(X3,X1,X2) )
           => ( v1_funct_1(X3)
              & v1_partfun1(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_funct_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
       => ! [X3] :
            ( ( v1_funct_1(X3)
              & v1_funct_2(X3,X1,X1)
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
           => ( r1_partfun1(X2,X3)
             => r2_hidden(X3,k5_partfun1(X1,X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t156_funct_2])).

fof(c_0_5,plain,(
    ! [X13,X14,X15,X16,X17,X19,X20,X21,X23] :
      ( ( v1_funct_1(esk1_5(X13,X14,X15,X16,X17))
        | ~ r2_hidden(X17,X16)
        | X16 != k5_partfun1(X13,X14,X15)
        | ~ v1_funct_1(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( m1_subset_1(esk1_5(X13,X14,X15,X16,X17),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
        | ~ r2_hidden(X17,X16)
        | X16 != k5_partfun1(X13,X14,X15)
        | ~ v1_funct_1(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( esk1_5(X13,X14,X15,X16,X17) = X17
        | ~ r2_hidden(X17,X16)
        | X16 != k5_partfun1(X13,X14,X15)
        | ~ v1_funct_1(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( v1_partfun1(esk1_5(X13,X14,X15,X16,X17),X13)
        | ~ r2_hidden(X17,X16)
        | X16 != k5_partfun1(X13,X14,X15)
        | ~ v1_funct_1(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( r1_partfun1(X15,esk1_5(X13,X14,X15,X16,X17))
        | ~ r2_hidden(X17,X16)
        | X16 != k5_partfun1(X13,X14,X15)
        | ~ v1_funct_1(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( ~ v1_funct_1(X20)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
        | X20 != X19
        | ~ v1_partfun1(X20,X13)
        | ~ r1_partfun1(X15,X20)
        | r2_hidden(X19,X16)
        | X16 != k5_partfun1(X13,X14,X15)
        | ~ v1_funct_1(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( ~ r2_hidden(esk2_4(X13,X14,X15,X21),X21)
        | ~ v1_funct_1(X23)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
        | X23 != esk2_4(X13,X14,X15,X21)
        | ~ v1_partfun1(X23,X13)
        | ~ r1_partfun1(X15,X23)
        | X21 = k5_partfun1(X13,X14,X15)
        | ~ v1_funct_1(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( v1_funct_1(esk3_4(X13,X14,X15,X21))
        | r2_hidden(esk2_4(X13,X14,X15,X21),X21)
        | X21 = k5_partfun1(X13,X14,X15)
        | ~ v1_funct_1(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( m1_subset_1(esk3_4(X13,X14,X15,X21),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
        | r2_hidden(esk2_4(X13,X14,X15,X21),X21)
        | X21 = k5_partfun1(X13,X14,X15)
        | ~ v1_funct_1(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( esk3_4(X13,X14,X15,X21) = esk2_4(X13,X14,X15,X21)
        | r2_hidden(esk2_4(X13,X14,X15,X21),X21)
        | X21 = k5_partfun1(X13,X14,X15)
        | ~ v1_funct_1(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( v1_partfun1(esk3_4(X13,X14,X15,X21),X13)
        | r2_hidden(esk2_4(X13,X14,X15,X21),X21)
        | X21 = k5_partfun1(X13,X14,X15)
        | ~ v1_funct_1(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( r1_partfun1(X15,esk3_4(X13,X14,X15,X21))
        | r2_hidden(esk2_4(X13,X14,X15,X21),X21)
        | X21 = k5_partfun1(X13,X14,X15)
        | ~ v1_funct_1(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_partfun1])])])])])])).

fof(c_0_6,plain,(
    ! [X7,X8,X9] :
      ( ~ v1_xboole_0(X7)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | v1_partfun1(X9,X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_partfun1])])])).

fof(c_0_7,negated_conjecture,
    ( v1_funct_1(esk5_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0)))
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,esk4_0,esk4_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0)))
    & r1_partfun1(esk5_0,esk6_0)
    & ~ r2_hidden(esk6_0,k5_partfun1(esk4_0,esk4_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

cnf(c_0_8,plain,
    ( r2_hidden(X4,X6)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | X1 != X4
    | ~ v1_partfun1(X1,X2)
    | ~ r1_partfun1(X5,X1)
    | X6 != k5_partfun1(X2,X3,X5)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_9,plain,(
    ! [X10,X11,X12] :
      ( ( v1_funct_1(X12)
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,X10,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
        | v1_xboole_0(X11) )
      & ( v1_partfun1(X12,X10)
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,X10,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
        | v1_xboole_0(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

cnf(c_0_10,plain,
    ( v1_partfun1(X2,X1)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ r1_partfun1(X4,X1)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_8])])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( v1_funct_2(esk6_0,esk4_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,negated_conjecture,
    ( v1_partfun1(esk6_0,esk4_0)
    | ~ v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(X1,k5_partfun1(esk4_0,esk4_0,esk5_0))
    | ~ r1_partfun1(esk5_0,X1)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])])).

cnf(c_0_20,negated_conjecture,
    ( r1_partfun1(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_21,negated_conjecture,
    ( v1_partfun1(esk6_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_11]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k5_partfun1(esk4_0,esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_23,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_11]),c_0_20]),c_0_17]),c_0_21])]),c_0_22]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:36:55 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S00AA
% 0.19/0.37  # and selection function SelectLargestOrientable.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.028 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t156_funct_2, conjecture, ![X1, X2]:((v1_funct_1(X2)&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(r1_partfun1(X2,X3)=>r2_hidden(X3,k5_partfun1(X1,X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_funct_2)).
% 0.19/0.37  fof(d7_partfun1, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(X4=k5_partfun1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>?[X6]:((((v1_funct_1(X6)&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&X6=X5)&v1_partfun1(X6,X1))&r1_partfun1(X3,X6))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_partfun1)).
% 0.19/0.37  fof(cc1_partfun1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_partfun1(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_partfun1)).
% 0.19/0.37  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 0.19/0.37  fof(c_0_4, negated_conjecture, ~(![X1, X2]:((v1_funct_1(X2)&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(r1_partfun1(X2,X3)=>r2_hidden(X3,k5_partfun1(X1,X1,X2)))))), inference(assume_negation,[status(cth)],[t156_funct_2])).
% 0.19/0.37  fof(c_0_5, plain, ![X13, X14, X15, X16, X17, X19, X20, X21, X23]:(((((((v1_funct_1(esk1_5(X13,X14,X15,X16,X17))|~r2_hidden(X17,X16)|X16!=k5_partfun1(X13,X14,X15)|(~v1_funct_1(X15)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))))&(m1_subset_1(esk1_5(X13,X14,X15,X16,X17),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))|~r2_hidden(X17,X16)|X16!=k5_partfun1(X13,X14,X15)|(~v1_funct_1(X15)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))))))&(esk1_5(X13,X14,X15,X16,X17)=X17|~r2_hidden(X17,X16)|X16!=k5_partfun1(X13,X14,X15)|(~v1_funct_1(X15)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))))))&(v1_partfun1(esk1_5(X13,X14,X15,X16,X17),X13)|~r2_hidden(X17,X16)|X16!=k5_partfun1(X13,X14,X15)|(~v1_funct_1(X15)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))))))&(r1_partfun1(X15,esk1_5(X13,X14,X15,X16,X17))|~r2_hidden(X17,X16)|X16!=k5_partfun1(X13,X14,X15)|(~v1_funct_1(X15)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))))))&(~v1_funct_1(X20)|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))|X20!=X19|~v1_partfun1(X20,X13)|~r1_partfun1(X15,X20)|r2_hidden(X19,X16)|X16!=k5_partfun1(X13,X14,X15)|(~v1_funct_1(X15)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))))))&((~r2_hidden(esk2_4(X13,X14,X15,X21),X21)|(~v1_funct_1(X23)|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))|X23!=esk2_4(X13,X14,X15,X21)|~v1_partfun1(X23,X13)|~r1_partfun1(X15,X23))|X21=k5_partfun1(X13,X14,X15)|(~v1_funct_1(X15)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))))&(((((v1_funct_1(esk3_4(X13,X14,X15,X21))|r2_hidden(esk2_4(X13,X14,X15,X21),X21)|X21=k5_partfun1(X13,X14,X15)|(~v1_funct_1(X15)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))))&(m1_subset_1(esk3_4(X13,X14,X15,X21),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))|r2_hidden(esk2_4(X13,X14,X15,X21),X21)|X21=k5_partfun1(X13,X14,X15)|(~v1_funct_1(X15)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))))))&(esk3_4(X13,X14,X15,X21)=esk2_4(X13,X14,X15,X21)|r2_hidden(esk2_4(X13,X14,X15,X21),X21)|X21=k5_partfun1(X13,X14,X15)|(~v1_funct_1(X15)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))))))&(v1_partfun1(esk3_4(X13,X14,X15,X21),X13)|r2_hidden(esk2_4(X13,X14,X15,X21),X21)|X21=k5_partfun1(X13,X14,X15)|(~v1_funct_1(X15)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))))))&(r1_partfun1(X15,esk3_4(X13,X14,X15,X21))|r2_hidden(esk2_4(X13,X14,X15,X21),X21)|X21=k5_partfun1(X13,X14,X15)|(~v1_funct_1(X15)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_partfun1])])])])])])).
% 0.19/0.37  fof(c_0_6, plain, ![X7, X8, X9]:(~v1_xboole_0(X7)|(~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))|v1_partfun1(X9,X7))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_partfun1])])])).
% 0.19/0.37  fof(c_0_7, negated_conjecture, ((v1_funct_1(esk5_0)&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0))))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk4_0,esk4_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0))))&(r1_partfun1(esk5_0,esk6_0)&~r2_hidden(esk6_0,k5_partfun1(esk4_0,esk4_0,esk5_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.19/0.37  cnf(c_0_8, plain, (r2_hidden(X4,X6)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|X1!=X4|~v1_partfun1(X1,X2)|~r1_partfun1(X5,X1)|X6!=k5_partfun1(X2,X3,X5)|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.37  fof(c_0_9, plain, ![X10, X11, X12]:((v1_funct_1(X12)|(~v1_funct_1(X12)|~v1_funct_2(X12,X10,X11))|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))|v1_xboole_0(X11))&(v1_partfun1(X12,X10)|(~v1_funct_1(X12)|~v1_funct_2(X12,X10,X11))|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))|v1_xboole_0(X11))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 0.19/0.37  cnf(c_0_10, plain, (v1_partfun1(X2,X1)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_11, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.37  cnf(c_0_12, plain, (r2_hidden(X1,k5_partfun1(X2,X3,X4))|~r1_partfun1(X4,X1)|~v1_funct_1(X4)|~v1_funct_1(X1)|~v1_partfun1(X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_8])])).
% 0.19/0.37  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.37  cnf(c_0_14, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.37  cnf(c_0_15, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_16, negated_conjecture, (v1_funct_2(esk6_0,esk4_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.37  cnf(c_0_17, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.37  cnf(c_0_18, negated_conjecture, (v1_partfun1(esk6_0,esk4_0)|~v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.19/0.37  cnf(c_0_19, negated_conjecture, (r2_hidden(X1,k5_partfun1(esk4_0,esk4_0,esk5_0))|~r1_partfun1(esk5_0,X1)|~v1_funct_1(X1)|~v1_partfun1(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14])])).
% 0.19/0.37  cnf(c_0_20, negated_conjecture, (r1_partfun1(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.37  cnf(c_0_21, negated_conjecture, (v1_partfun1(esk6_0,esk4_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_11]), c_0_16]), c_0_17])]), c_0_18])).
% 0.19/0.37  cnf(c_0_22, negated_conjecture, (~r2_hidden(esk6_0,k5_partfun1(esk4_0,esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.37  cnf(c_0_23, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_11]), c_0_20]), c_0_17]), c_0_21])]), c_0_22]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 24
% 0.19/0.37  # Proof object clause steps            : 15
% 0.19/0.37  # Proof object formula steps           : 9
% 0.19/0.37  # Proof object conjectures             : 14
% 0.19/0.37  # Proof object clause conjectures      : 11
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 10
% 0.19/0.37  # Proof object initial formulas used   : 4
% 0.19/0.37  # Proof object generating inferences   : 4
% 0.19/0.37  # Proof object simplifying inferences  : 13
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 4
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 22
% 0.19/0.37  # Removed in clause preprocessing      : 1
% 0.19/0.37  # Initial clauses in saturation        : 21
% 0.19/0.37  # Processed clauses                    : 66
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 0
% 0.19/0.37  # ...remaining for further processing  : 66
% 0.19/0.37  # Other redundant clauses eliminated   : 8
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 1
% 0.19/0.37  # Generated clauses                    : 37
% 0.19/0.37  # ...of the previous two non-trivial   : 35
% 0.19/0.37  # Contextual simplify-reflections      : 2
% 0.19/0.37  # Paramodulations                      : 30
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 8
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 37
% 0.19/0.37  #    Positive orientable unit clauses  : 7
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 1
% 0.19/0.37  #    Non-unit-clauses                  : 29
% 0.19/0.37  # Current number of unprocessed clauses: 11
% 0.19/0.37  # ...number of literals in the above   : 32
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 22
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 325
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 87
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 2
% 0.19/0.37  # Unit Clause-clause subsumption calls : 1
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 1
% 0.19/0.37  # BW rewrite match successes           : 1
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 3174
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.028 s
% 0.19/0.37  # System time              : 0.006 s
% 0.19/0.37  # Total time               : 0.035 s
% 0.19/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
