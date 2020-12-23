%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:07 EST 2020

% Result     : Theorem 0.17s
% Output     : CNFRefutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   33 ( 306 expanded)
%              Number of clauses        :   26 ( 111 expanded)
%              Number of leaves         :    3 (  69 expanded)
%              Depth                    :    8
%              Number of atoms          :  198 (2428 expanded)
%              Number of equality atoms :   39 ( 515 expanded)
%              Maximal formula depth    :   26 (   5 average)
%              Maximal clause size      :   68 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t132_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( ( X2 = k1_xboole_0
            & X1 != k1_xboole_0 )
          | v1_partfun1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

fof(t155_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( r1_partfun1(X3,X4)
           => ( ( X2 = k1_xboole_0
                & X1 != k1_xboole_0 )
              | r2_hidden(X4,k5_partfun1(X1,X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_partfun1)).

fof(c_0_3,plain,(
    ! [X19,X20,X21] :
      ( ( X20 = k1_xboole_0
        | v1_partfun1(X21,X19)
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,X19,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
        | ~ v1_funct_1(X21)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( X19 != k1_xboole_0
        | v1_partfun1(X21,X19)
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,X19,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
        | ~ v1_funct_1(X21)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t132_funct_2])])])).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_funct_2(X4,X1,X2)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
           => ( r1_partfun1(X3,X4)
             => ( ( X2 = k1_xboole_0
                  & X1 != k1_xboole_0 )
                | r2_hidden(X4,k5_partfun1(X1,X2,X3)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t155_funct_2])).

fof(c_0_5,plain,(
    ! [X7,X8,X9,X10,X11,X13,X14,X15,X17] :
      ( ( v1_funct_1(esk1_5(X7,X8,X9,X10,X11))
        | ~ r2_hidden(X11,X10)
        | X10 != k5_partfun1(X7,X8,X9)
        | ~ v1_funct_1(X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) )
      & ( m1_subset_1(esk1_5(X7,X8,X9,X10,X11),k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | ~ r2_hidden(X11,X10)
        | X10 != k5_partfun1(X7,X8,X9)
        | ~ v1_funct_1(X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) )
      & ( esk1_5(X7,X8,X9,X10,X11) = X11
        | ~ r2_hidden(X11,X10)
        | X10 != k5_partfun1(X7,X8,X9)
        | ~ v1_funct_1(X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) )
      & ( v1_partfun1(esk1_5(X7,X8,X9,X10,X11),X7)
        | ~ r2_hidden(X11,X10)
        | X10 != k5_partfun1(X7,X8,X9)
        | ~ v1_funct_1(X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) )
      & ( r1_partfun1(X9,esk1_5(X7,X8,X9,X10,X11))
        | ~ r2_hidden(X11,X10)
        | X10 != k5_partfun1(X7,X8,X9)
        | ~ v1_funct_1(X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) )
      & ( ~ v1_funct_1(X14)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | X14 != X13
        | ~ v1_partfun1(X14,X7)
        | ~ r1_partfun1(X9,X14)
        | r2_hidden(X13,X10)
        | X10 != k5_partfun1(X7,X8,X9)
        | ~ v1_funct_1(X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) )
      & ( ~ r2_hidden(esk2_4(X7,X8,X9,X15),X15)
        | ~ v1_funct_1(X17)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | X17 != esk2_4(X7,X8,X9,X15)
        | ~ v1_partfun1(X17,X7)
        | ~ r1_partfun1(X9,X17)
        | X15 = k5_partfun1(X7,X8,X9)
        | ~ v1_funct_1(X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) )
      & ( v1_funct_1(esk3_4(X7,X8,X9,X15))
        | r2_hidden(esk2_4(X7,X8,X9,X15),X15)
        | X15 = k5_partfun1(X7,X8,X9)
        | ~ v1_funct_1(X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) )
      & ( m1_subset_1(esk3_4(X7,X8,X9,X15),k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | r2_hidden(esk2_4(X7,X8,X9,X15),X15)
        | X15 = k5_partfun1(X7,X8,X9)
        | ~ v1_funct_1(X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) )
      & ( esk3_4(X7,X8,X9,X15) = esk2_4(X7,X8,X9,X15)
        | r2_hidden(esk2_4(X7,X8,X9,X15),X15)
        | X15 = k5_partfun1(X7,X8,X9)
        | ~ v1_funct_1(X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) )
      & ( v1_partfun1(esk3_4(X7,X8,X9,X15),X7)
        | r2_hidden(esk2_4(X7,X8,X9,X15),X15)
        | X15 = k5_partfun1(X7,X8,X9)
        | ~ v1_funct_1(X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) )
      & ( r1_partfun1(X9,esk3_4(X7,X8,X9,X15))
        | r2_hidden(esk2_4(X7,X8,X9,X15),X15)
        | X15 = k5_partfun1(X7,X8,X9)
        | ~ v1_funct_1(X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_partfun1])])])])])])).

cnf(c_0_6,plain,
    ( X1 = k1_xboole_0
    | v1_partfun1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

fof(c_0_7,negated_conjecture,
    ( v1_funct_1(esk6_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
    & v1_funct_1(esk7_0)
    & v1_funct_2(esk7_0,esk4_0,esk5_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
    & r1_partfun1(esk6_0,esk7_0)
    & ( esk5_0 != k1_xboole_0
      | esk4_0 = k1_xboole_0 )
    & ~ r2_hidden(esk7_0,k5_partfun1(esk4_0,esk5_0,esk6_0)) ),
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

cnf(c_0_9,plain,
    ( X1 = k1_xboole_0
    | v1_partfun1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(cn,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( v1_funct_2(esk7_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ r1_partfun1(X4,X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_8])])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | v1_partfun1(esk7_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_12])])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(X1,k5_partfun1(esk4_0,esk5_0,esk6_0))
    | ~ r1_partfun1(esk6_0,X1)
    | ~ v1_partfun1(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])])).

cnf(c_0_19,negated_conjecture,
    ( r1_partfun1(esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_20,negated_conjecture,
    ( ~ r2_hidden(esk7_0,k5_partfun1(esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_21,plain,
    ( v1_partfun1(X2,X1)
    | X1 != k1_xboole_0
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_22,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | v1_partfun1(esk7_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( ~ v1_partfun1(esk7_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_10]),c_0_19]),c_0_12])]),c_0_20])).

cnf(c_0_24,plain,
    ( v1_partfun1(X2,X1)
    | X1 != k1_xboole_0
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(cn,[status(thm)],[c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( v1_partfun1(esk7_0,esk4_0)
    | m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_10,c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_2(esk7_0,esk4_0,k1_xboole_0)
    | v1_partfun1(esk7_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_17])).

cnf(c_0_28,plain,
    ( v1_partfun1(X1,k1_xboole_0)
    | ~ v1_funct_2(X1,k1_xboole_0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
    | ~ v1_funct_1(X1) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[c_0_25,c_0_23]),c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_2(esk7_0,k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[c_0_27,c_0_23]),c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( ~ v1_partfun1(esk7_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_23,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_12])]),c_0_31]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n011.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 20:30:12 EST 2020
% 0.17/0.32  % CPUTime    : 
% 0.17/0.32  # Version: 2.5pre002
% 0.17/0.32  # No SInE strategy applied
% 0.17/0.32  # Trying AutoSched0 for 299 seconds
% 0.17/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S00AA
% 0.17/0.36  # and selection function SelectLargestOrientable.
% 0.17/0.36  #
% 0.17/0.36  # Preprocessing time       : 0.029 s
% 0.17/0.36  # Presaturation interreduction done
% 0.17/0.36  
% 0.17/0.36  # Proof found!
% 0.17/0.36  # SZS status Theorem
% 0.17/0.36  # SZS output start CNFRefutation
% 0.17/0.36  fof(t132_funct_2, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0&X1!=k1_xboole_0)|v1_partfun1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_funct_2)).
% 0.17/0.36  fof(t155_funct_2, conjecture, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_partfun1(X3,X4)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|r2_hidden(X4,k5_partfun1(X1,X2,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_2)).
% 0.17/0.36  fof(d7_partfun1, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(X4=k5_partfun1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>?[X6]:((((v1_funct_1(X6)&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&X6=X5)&v1_partfun1(X6,X1))&r1_partfun1(X3,X6))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_partfun1)).
% 0.17/0.36  fof(c_0_3, plain, ![X19, X20, X21]:((X20=k1_xboole_0|v1_partfun1(X21,X19)|(~v1_funct_1(X21)|~v1_funct_2(X21,X19,X20)|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))))|(~v1_funct_1(X21)|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))))&(X19!=k1_xboole_0|v1_partfun1(X21,X19)|(~v1_funct_1(X21)|~v1_funct_2(X21,X19,X20)|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))))|(~v1_funct_1(X21)|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t132_funct_2])])])).
% 0.17/0.36  fof(c_0_4, negated_conjecture, ~(![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_partfun1(X3,X4)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|r2_hidden(X4,k5_partfun1(X1,X2,X3))))))), inference(assume_negation,[status(cth)],[t155_funct_2])).
% 0.17/0.36  fof(c_0_5, plain, ![X7, X8, X9, X10, X11, X13, X14, X15, X17]:(((((((v1_funct_1(esk1_5(X7,X8,X9,X10,X11))|~r2_hidden(X11,X10)|X10!=k5_partfun1(X7,X8,X9)|(~v1_funct_1(X9)|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))))&(m1_subset_1(esk1_5(X7,X8,X9,X10,X11),k1_zfmisc_1(k2_zfmisc_1(X7,X8)))|~r2_hidden(X11,X10)|X10!=k5_partfun1(X7,X8,X9)|(~v1_funct_1(X9)|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))))))&(esk1_5(X7,X8,X9,X10,X11)=X11|~r2_hidden(X11,X10)|X10!=k5_partfun1(X7,X8,X9)|(~v1_funct_1(X9)|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))))))&(v1_partfun1(esk1_5(X7,X8,X9,X10,X11),X7)|~r2_hidden(X11,X10)|X10!=k5_partfun1(X7,X8,X9)|(~v1_funct_1(X9)|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))))))&(r1_partfun1(X9,esk1_5(X7,X8,X9,X10,X11))|~r2_hidden(X11,X10)|X10!=k5_partfun1(X7,X8,X9)|(~v1_funct_1(X9)|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))))))&(~v1_funct_1(X14)|~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))|X14!=X13|~v1_partfun1(X14,X7)|~r1_partfun1(X9,X14)|r2_hidden(X13,X10)|X10!=k5_partfun1(X7,X8,X9)|(~v1_funct_1(X9)|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))))))&((~r2_hidden(esk2_4(X7,X8,X9,X15),X15)|(~v1_funct_1(X17)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))|X17!=esk2_4(X7,X8,X9,X15)|~v1_partfun1(X17,X7)|~r1_partfun1(X9,X17))|X15=k5_partfun1(X7,X8,X9)|(~v1_funct_1(X9)|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))))&(((((v1_funct_1(esk3_4(X7,X8,X9,X15))|r2_hidden(esk2_4(X7,X8,X9,X15),X15)|X15=k5_partfun1(X7,X8,X9)|(~v1_funct_1(X9)|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))))&(m1_subset_1(esk3_4(X7,X8,X9,X15),k1_zfmisc_1(k2_zfmisc_1(X7,X8)))|r2_hidden(esk2_4(X7,X8,X9,X15),X15)|X15=k5_partfun1(X7,X8,X9)|(~v1_funct_1(X9)|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))))))&(esk3_4(X7,X8,X9,X15)=esk2_4(X7,X8,X9,X15)|r2_hidden(esk2_4(X7,X8,X9,X15),X15)|X15=k5_partfun1(X7,X8,X9)|(~v1_funct_1(X9)|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))))))&(v1_partfun1(esk3_4(X7,X8,X9,X15),X7)|r2_hidden(esk2_4(X7,X8,X9,X15),X15)|X15=k5_partfun1(X7,X8,X9)|(~v1_funct_1(X9)|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))))))&(r1_partfun1(X9,esk3_4(X7,X8,X9,X15))|r2_hidden(esk2_4(X7,X8,X9,X15),X15)|X15=k5_partfun1(X7,X8,X9)|(~v1_funct_1(X9)|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_partfun1])])])])])])).
% 0.17/0.36  cnf(c_0_6, plain, (X1=k1_xboole_0|v1_partfun1(X2,X3)|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.17/0.36  fof(c_0_7, negated_conjecture, ((v1_funct_1(esk6_0)&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))))&(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,esk4_0,esk5_0))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))))&(r1_partfun1(esk6_0,esk7_0)&((esk5_0!=k1_xboole_0|esk4_0=k1_xboole_0)&~r2_hidden(esk7_0,k5_partfun1(esk4_0,esk5_0,esk6_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.17/0.36  cnf(c_0_8, plain, (r2_hidden(X4,X6)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|X1!=X4|~v1_partfun1(X1,X2)|~r1_partfun1(X5,X1)|X6!=k5_partfun1(X2,X3,X5)|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.17/0.36  cnf(c_0_9, plain, (X1=k1_xboole_0|v1_partfun1(X2,X3)|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(cn,[status(thm)],[c_0_6])).
% 0.17/0.36  cnf(c_0_10, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.17/0.36  cnf(c_0_11, negated_conjecture, (v1_funct_2(esk7_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.17/0.36  cnf(c_0_12, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.17/0.36  cnf(c_0_13, plain, (r2_hidden(X1,k5_partfun1(X2,X3,X4))|~r1_partfun1(X4,X1)|~v1_partfun1(X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~v1_funct_1(X1)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_8])])).
% 0.17/0.36  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.17/0.36  cnf(c_0_15, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.17/0.36  cnf(c_0_16, negated_conjecture, (esk4_0=k1_xboole_0|esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.17/0.36  cnf(c_0_17, negated_conjecture, (esk5_0=k1_xboole_0|v1_partfun1(esk7_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_11]), c_0_12])])).
% 0.17/0.36  cnf(c_0_18, negated_conjecture, (r2_hidden(X1,k5_partfun1(esk4_0,esk5_0,esk6_0))|~r1_partfun1(esk6_0,X1)|~v1_partfun1(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))|~v1_funct_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15])])).
% 0.17/0.36  cnf(c_0_19, negated_conjecture, (r1_partfun1(esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.17/0.36  cnf(c_0_20, negated_conjecture, (~r2_hidden(esk7_0,k5_partfun1(esk4_0,esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.17/0.36  cnf(c_0_21, plain, (v1_partfun1(X2,X1)|X1!=k1_xboole_0|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.17/0.36  cnf(c_0_22, negated_conjecture, (esk4_0=k1_xboole_0|v1_partfun1(esk7_0,esk4_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.17/0.36  cnf(c_0_23, negated_conjecture, (~v1_partfun1(esk7_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_10]), c_0_19]), c_0_12])]), c_0_20])).
% 0.17/0.36  cnf(c_0_24, plain, (v1_partfun1(X2,X1)|X1!=k1_xboole_0|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(cn,[status(thm)],[c_0_21])).
% 0.17/0.36  cnf(c_0_25, negated_conjecture, (v1_partfun1(esk7_0,esk4_0)|m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_10, c_0_17])).
% 0.17/0.36  cnf(c_0_26, negated_conjecture, (esk4_0=k1_xboole_0), inference(sr,[status(thm)],[c_0_22, c_0_23])).
% 0.17/0.36  cnf(c_0_27, negated_conjecture, (v1_funct_2(esk7_0,esk4_0,k1_xboole_0)|v1_partfun1(esk7_0,esk4_0)), inference(spm,[status(thm)],[c_0_11, c_0_17])).
% 0.17/0.36  cnf(c_0_28, plain, (v1_partfun1(X1,k1_xboole_0)|~v1_funct_2(X1,k1_xboole_0,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))|~v1_funct_1(X1)), inference(er,[status(thm)],[c_0_24])).
% 0.17/0.36  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(rw,[status(thm)],[inference(sr,[status(thm)],[c_0_25, c_0_23]), c_0_26])).
% 0.17/0.36  cnf(c_0_30, negated_conjecture, (v1_funct_2(esk7_0,k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(sr,[status(thm)],[c_0_27, c_0_23]), c_0_26])).
% 0.17/0.36  cnf(c_0_31, negated_conjecture, (~v1_partfun1(esk7_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_23, c_0_26])).
% 0.17/0.36  cnf(c_0_32, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_12])]), c_0_31]), ['proof']).
% 0.17/0.36  # SZS output end CNFRefutation
% 0.17/0.36  # Proof object total steps             : 33
% 0.17/0.36  # Proof object clause steps            : 26
% 0.17/0.36  # Proof object formula steps           : 7
% 0.17/0.36  # Proof object conjectures             : 22
% 0.17/0.36  # Proof object clause conjectures      : 19
% 0.17/0.36  # Proof object formula conjectures     : 3
% 0.17/0.36  # Proof object initial clauses used    : 11
% 0.17/0.36  # Proof object initial formulas used   : 3
% 0.17/0.36  # Proof object generating inferences   : 7
% 0.17/0.36  # Proof object simplifying inferences  : 24
% 0.17/0.36  # Training examples: 0 positive, 0 negative
% 0.17/0.36  # Parsed axioms                        : 3
% 0.17/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.17/0.36  # Initial clauses                      : 22
% 0.17/0.36  # Removed in clause preprocessing      : 0
% 0.17/0.36  # Initial clauses in saturation        : 22
% 0.17/0.36  # Processed clauses                    : 89
% 0.17/0.36  # ...of these trivial                  : 4
% 0.17/0.36  # ...subsumed                          : 7
% 0.17/0.36  # ...remaining for further processing  : 78
% 0.17/0.36  # Other redundant clauses eliminated   : 9
% 0.17/0.36  # Clauses deleted for lack of memory   : 0
% 0.17/0.36  # Backward-subsumed                    : 0
% 0.17/0.36  # Backward-rewritten                   : 14
% 0.17/0.36  # Generated clauses                    : 83
% 0.17/0.36  # ...of the previous two non-trivial   : 89
% 0.17/0.36  # Contextual simplify-reflections      : 0
% 0.17/0.36  # Paramodulations                      : 64
% 0.17/0.36  # Factorizations                       : 0
% 0.17/0.36  # Equation resolutions                 : 9
% 0.17/0.36  # Propositional unsat checks           : 0
% 0.17/0.36  #    Propositional check models        : 0
% 0.17/0.36  #    Propositional check unsatisfiable : 0
% 0.17/0.36  #    Propositional clauses             : 0
% 0.17/0.36  #    Propositional clauses after purity: 0
% 0.17/0.36  #    Propositional unsat core size     : 0
% 0.17/0.36  #    Propositional preprocessing time  : 0.000
% 0.17/0.36  #    Propositional encoding time       : 0.000
% 0.17/0.36  #    Propositional solver time         : 0.000
% 0.17/0.36  #    Success case prop preproc time    : 0.000
% 0.17/0.36  #    Success case prop encoding time   : 0.000
% 0.17/0.36  #    Success case prop solver time     : 0.000
% 0.17/0.36  # Current number of processed clauses  : 23
% 0.17/0.36  #    Positive orientable unit clauses  : 7
% 0.17/0.36  #    Positive unorientable unit clauses: 0
% 0.17/0.36  #    Negative unit clauses             : 2
% 0.17/0.36  #    Non-unit-clauses                  : 14
% 0.17/0.36  # Current number of unprocessed clauses: 39
% 0.17/0.36  # ...number of literals in the above   : 111
% 0.17/0.36  # Current number of archived formulas  : 0
% 0.17/0.36  # Current number of archived clauses   : 47
% 0.17/0.36  # Clause-clause subsumption calls (NU) : 898
% 0.17/0.36  # Rec. Clause-clause subsumption calls : 250
% 0.17/0.36  # Non-unit clause-clause subsumptions  : 4
% 0.17/0.36  # Unit Clause-clause subsumption calls : 87
% 0.17/0.36  # Rewrite failures with RHS unbound    : 0
% 0.17/0.36  # BW rewrite match attempts            : 2
% 0.17/0.36  # BW rewrite match successes           : 2
% 0.17/0.36  # Condensation attempts                : 0
% 0.17/0.36  # Condensation successes               : 0
% 0.17/0.36  # Termbank termtop insertions          : 3592
% 0.17/0.36  
% 0.17/0.36  # -------------------------------------------------
% 0.17/0.36  # User time                : 0.032 s
% 0.17/0.36  # System time              : 0.009 s
% 0.17/0.36  # Total time               : 0.041 s
% 0.17/0.36  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
