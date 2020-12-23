%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:05:57 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   29 ( 397 expanded)
%              Number of clauses        :   22 ( 131 expanded)
%              Number of leaves         :    3 (  93 expanded)
%              Depth                    :   11
%              Number of atoms          :  166 (2423 expanded)
%              Number of equality atoms :   52 ( 651 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   66 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t85_funct_2,conjecture,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => ( v2_funct_1(X2)
       => ! [X3,X4] :
            ( ( r2_hidden(X3,X1)
              & r2_hidden(X4,X1)
              & k1_funct_1(X2,X3) = k1_funct_1(X2,X4) )
           => X3 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_2)).

fof(t32_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( v2_funct_1(X4)
          & r2_hidden(X3,X1) )
       => ( X2 = k1_xboole_0
          | k1_funct_1(k2_funct_1(X4),k1_funct_1(X4,X3)) = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).

fof(t25_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( X2 = k1_xboole_0
         => X1 = k1_xboole_0 )
       => ( v2_funct_1(X3)
        <=> ! [X4,X5] :
              ( ( r2_hidden(X4,X1)
                & r2_hidden(X5,X1)
                & k1_funct_1(X3,X4) = k1_funct_1(X3,X5) )
             => X4 = X5 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_funct_2)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_funct_2(X2,X1,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
       => ( v2_funct_1(X2)
         => ! [X3,X4] :
              ( ( r2_hidden(X3,X1)
                & r2_hidden(X4,X1)
                & k1_funct_1(X2,X3) = k1_funct_1(X2,X4) )
             => X3 = X4 ) ) ) ),
    inference(assume_negation,[status(cth)],[t85_funct_2])).

fof(c_0_4,plain,(
    ! [X13,X14,X15,X16] :
      ( ~ v1_funct_1(X16)
      | ~ v1_funct_2(X16,X13,X14)
      | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | ~ v2_funct_1(X16)
      | ~ r2_hidden(X15,X13)
      | X14 = k1_xboole_0
      | k1_funct_1(k2_funct_1(X16),k1_funct_1(X16,X15)) = X15 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_funct_2])])).

fof(c_0_5,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk3_0,esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))
    & v2_funct_1(esk4_0)
    & r2_hidden(esk5_0,esk3_0)
    & r2_hidden(esk6_0,esk3_0)
    & k1_funct_1(esk4_0,esk5_0) = k1_funct_1(esk4_0,esk6_0)
    & esk5_0 != esk6_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

cnf(c_0_6,plain,
    ( X3 = k1_xboole_0
    | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X4)) = X4
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v2_funct_1(X1)
    | ~ r2_hidden(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( v1_funct_2(esk4_0,esk3_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( v2_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,negated_conjecture,
    ( k1_funct_1(k2_funct_1(esk4_0),k1_funct_1(esk4_0,X1)) = X1
    | esk3_0 = k1_xboole_0
    | ~ r2_hidden(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_7]),c_0_8]),c_0_9]),c_0_10])])).

cnf(c_0_12,negated_conjecture,
    ( r2_hidden(esk6_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,negated_conjecture,
    ( k1_funct_1(esk4_0,esk5_0) = k1_funct_1(esk4_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,negated_conjecture,
    ( esk5_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,negated_conjecture,
    ( esk6_0 = k1_funct_1(k2_funct_1(esk4_0),k1_funct_1(esk4_0,esk5_0))
    | esk3_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])).

fof(c_0_16,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ v2_funct_1(X8)
        | ~ r2_hidden(X9,X6)
        | ~ r2_hidden(X10,X6)
        | k1_funct_1(X8,X9) != k1_funct_1(X8,X10)
        | X9 = X10
        | X7 = k1_xboole_0
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) )
      & ( r2_hidden(esk1_3(X6,X7,X8),X6)
        | v2_funct_1(X8)
        | X7 = k1_xboole_0
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) )
      & ( r2_hidden(esk2_3(X6,X7,X8),X6)
        | v2_funct_1(X8)
        | X7 = k1_xboole_0
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) )
      & ( k1_funct_1(X8,esk1_3(X6,X7,X8)) = k1_funct_1(X8,esk2_3(X6,X7,X8))
        | v2_funct_1(X8)
        | X7 = k1_xboole_0
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) )
      & ( esk1_3(X6,X7,X8) != esk2_3(X6,X7,X8)
        | v2_funct_1(X8)
        | X7 = k1_xboole_0
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) )
      & ( ~ v2_funct_1(X8)
        | ~ r2_hidden(X9,X6)
        | ~ r2_hidden(X10,X6)
        | k1_funct_1(X8,X9) != k1_funct_1(X8,X10)
        | X9 = X10
        | X6 != k1_xboole_0
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) )
      & ( r2_hidden(esk1_3(X6,X7,X8),X6)
        | v2_funct_1(X8)
        | X6 != k1_xboole_0
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) )
      & ( r2_hidden(esk2_3(X6,X7,X8),X6)
        | v2_funct_1(X8)
        | X6 != k1_xboole_0
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) )
      & ( k1_funct_1(X8,esk1_3(X6,X7,X8)) = k1_funct_1(X8,esk2_3(X6,X7,X8))
        | v2_funct_1(X8)
        | X6 != k1_xboole_0
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) )
      & ( esk1_3(X6,X7,X8) != esk2_3(X6,X7,X8)
        | v2_funct_1(X8)
        | X6 != k1_xboole_0
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_funct_2])])])])])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_18,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | k1_funct_1(k2_funct_1(esk4_0),k1_funct_1(esk4_0,esk5_0)) != esk5_0 ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,plain,
    ( X2 = X4
    | ~ v2_funct_1(X1)
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X4,X3)
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X4)
    | X3 != k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X5)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X5))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_17]),c_0_18])).

cnf(c_0_21,plain,
    ( X1 = X2
    | k1_funct_1(X3,X1) != k1_funct_1(X3,X2)
    | ~ r2_hidden(X2,k1_xboole_0)
    | ~ r2_hidden(X1,k1_xboole_0)
    | ~ v2_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4)))
    | ~ v1_funct_2(X3,k1_xboole_0,X4)
    | ~ v1_funct_1(X3) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_7,c_0_20]),c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_9,c_0_20]),c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( X1 = X2
    | k1_funct_1(esk4_0,X1) != k1_funct_1(esk4_0,X2)
    | ~ r2_hidden(X2,k1_xboole_0)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_8]),c_0_10])]),c_0_23])])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk6_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_12,c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( X1 = esk6_0
    | k1_funct_1(esk4_0,X1) != k1_funct_1(esk4_0,esk5_0)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_13])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk5_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_17,c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_14]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:19:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S5PRR_S0Y
% 0.12/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.027 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t85_funct_2, conjecture, ![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(v2_funct_1(X2)=>![X3, X4]:(((r2_hidden(X3,X1)&r2_hidden(X4,X1))&k1_funct_1(X2,X3)=k1_funct_1(X2,X4))=>X3=X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_funct_2)).
% 0.12/0.37  fof(t32_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X4)&r2_hidden(X3,X1))=>(X2=k1_xboole_0|k1_funct_1(k2_funct_1(X4),k1_funct_1(X4,X3))=X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_funct_2)).
% 0.12/0.37  fof(t25_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v2_funct_1(X3)<=>![X4, X5]:(((r2_hidden(X4,X1)&r2_hidden(X5,X1))&k1_funct_1(X3,X4)=k1_funct_1(X3,X5))=>X4=X5)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_funct_2)).
% 0.12/0.37  fof(c_0_3, negated_conjecture, ~(![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(v2_funct_1(X2)=>![X3, X4]:(((r2_hidden(X3,X1)&r2_hidden(X4,X1))&k1_funct_1(X2,X3)=k1_funct_1(X2,X4))=>X3=X4)))), inference(assume_negation,[status(cth)],[t85_funct_2])).
% 0.12/0.37  fof(c_0_4, plain, ![X13, X14, X15, X16]:(~v1_funct_1(X16)|~v1_funct_2(X16,X13,X14)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))|(~v2_funct_1(X16)|~r2_hidden(X15,X13)|(X14=k1_xboole_0|k1_funct_1(k2_funct_1(X16),k1_funct_1(X16,X15))=X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_funct_2])])).
% 0.12/0.37  fof(c_0_5, negated_conjecture, (((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk3_0,esk3_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))))&(v2_funct_1(esk4_0)&(((r2_hidden(esk5_0,esk3_0)&r2_hidden(esk6_0,esk3_0))&k1_funct_1(esk4_0,esk5_0)=k1_funct_1(esk4_0,esk6_0))&esk5_0!=esk6_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).
% 0.12/0.37  cnf(c_0_6, plain, (X3=k1_xboole_0|k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X4))=X4|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v2_funct_1(X1)|~r2_hidden(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.37  cnf(c_0_7, negated_conjecture, (v1_funct_2(esk4_0,esk3_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.37  cnf(c_0_8, negated_conjecture, (v2_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.37  cnf(c_0_9, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.37  cnf(c_0_10, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.37  cnf(c_0_11, negated_conjecture, (k1_funct_1(k2_funct_1(esk4_0),k1_funct_1(esk4_0,X1))=X1|esk3_0=k1_xboole_0|~r2_hidden(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6, c_0_7]), c_0_8]), c_0_9]), c_0_10])])).
% 0.12/0.37  cnf(c_0_12, negated_conjecture, (r2_hidden(esk6_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.37  cnf(c_0_13, negated_conjecture, (k1_funct_1(esk4_0,esk5_0)=k1_funct_1(esk4_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.37  cnf(c_0_14, negated_conjecture, (esk5_0!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.37  cnf(c_0_15, negated_conjecture, (esk6_0=k1_funct_1(k2_funct_1(esk4_0),k1_funct_1(esk4_0,esk5_0))|esk3_0=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13])).
% 0.12/0.37  fof(c_0_16, plain, ![X6, X7, X8, X9, X10]:(((~v2_funct_1(X8)|(~r2_hidden(X9,X6)|~r2_hidden(X10,X6)|k1_funct_1(X8,X9)!=k1_funct_1(X8,X10)|X9=X10)|X7=k1_xboole_0|(~v1_funct_1(X8)|~v1_funct_2(X8,X6,X7)|~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))))&((((r2_hidden(esk1_3(X6,X7,X8),X6)|v2_funct_1(X8)|X7=k1_xboole_0|(~v1_funct_1(X8)|~v1_funct_2(X8,X6,X7)|~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))))&(r2_hidden(esk2_3(X6,X7,X8),X6)|v2_funct_1(X8)|X7=k1_xboole_0|(~v1_funct_1(X8)|~v1_funct_2(X8,X6,X7)|~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))))))&(k1_funct_1(X8,esk1_3(X6,X7,X8))=k1_funct_1(X8,esk2_3(X6,X7,X8))|v2_funct_1(X8)|X7=k1_xboole_0|(~v1_funct_1(X8)|~v1_funct_2(X8,X6,X7)|~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))))))&(esk1_3(X6,X7,X8)!=esk2_3(X6,X7,X8)|v2_funct_1(X8)|X7=k1_xboole_0|(~v1_funct_1(X8)|~v1_funct_2(X8,X6,X7)|~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))))))&((~v2_funct_1(X8)|(~r2_hidden(X9,X6)|~r2_hidden(X10,X6)|k1_funct_1(X8,X9)!=k1_funct_1(X8,X10)|X9=X10)|X6!=k1_xboole_0|(~v1_funct_1(X8)|~v1_funct_2(X8,X6,X7)|~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))))&((((r2_hidden(esk1_3(X6,X7,X8),X6)|v2_funct_1(X8)|X6!=k1_xboole_0|(~v1_funct_1(X8)|~v1_funct_2(X8,X6,X7)|~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))))&(r2_hidden(esk2_3(X6,X7,X8),X6)|v2_funct_1(X8)|X6!=k1_xboole_0|(~v1_funct_1(X8)|~v1_funct_2(X8,X6,X7)|~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))))))&(k1_funct_1(X8,esk1_3(X6,X7,X8))=k1_funct_1(X8,esk2_3(X6,X7,X8))|v2_funct_1(X8)|X6!=k1_xboole_0|(~v1_funct_1(X8)|~v1_funct_2(X8,X6,X7)|~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))))))&(esk1_3(X6,X7,X8)!=esk2_3(X6,X7,X8)|v2_funct_1(X8)|X6!=k1_xboole_0|(~v1_funct_1(X8)|~v1_funct_2(X8,X6,X7)|~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_funct_2])])])])])).
% 0.12/0.37  cnf(c_0_17, negated_conjecture, (r2_hidden(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.37  cnf(c_0_18, negated_conjecture, (esk3_0=k1_xboole_0|k1_funct_1(k2_funct_1(esk4_0),k1_funct_1(esk4_0,esk5_0))!=esk5_0), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.12/0.37  cnf(c_0_19, plain, (X2=X4|~v2_funct_1(X1)|~r2_hidden(X2,X3)|~r2_hidden(X4,X3)|k1_funct_1(X1,X2)!=k1_funct_1(X1,X4)|X3!=k1_xboole_0|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X5)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X5)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_20, negated_conjecture, (esk3_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_17]), c_0_18])).
% 0.12/0.37  cnf(c_0_21, plain, (X1=X2|k1_funct_1(X3,X1)!=k1_funct_1(X3,X2)|~r2_hidden(X2,k1_xboole_0)|~r2_hidden(X1,k1_xboole_0)|~v2_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4)))|~v1_funct_2(X3,k1_xboole_0,X4)|~v1_funct_1(X3)), inference(er,[status(thm)],[c_0_19])).
% 0.12/0.37  cnf(c_0_22, negated_conjecture, (v1_funct_2(esk4_0,k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_7, c_0_20]), c_0_20])).
% 0.12/0.37  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_9, c_0_20]), c_0_20])).
% 0.12/0.37  cnf(c_0_24, negated_conjecture, (X1=X2|k1_funct_1(esk4_0,X1)!=k1_funct_1(esk4_0,X2)|~r2_hidden(X2,k1_xboole_0)|~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_8]), c_0_10])]), c_0_23])])).
% 0.12/0.37  cnf(c_0_25, negated_conjecture, (r2_hidden(esk6_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_12, c_0_20])).
% 0.12/0.37  cnf(c_0_26, negated_conjecture, (X1=esk6_0|k1_funct_1(esk4_0,X1)!=k1_funct_1(esk4_0,esk5_0)|~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_13])).
% 0.12/0.37  cnf(c_0_27, negated_conjecture, (r2_hidden(esk5_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_17, c_0_20])).
% 0.12/0.37  cnf(c_0_28, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_14]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 29
% 0.12/0.37  # Proof object clause steps            : 22
% 0.12/0.37  # Proof object formula steps           : 7
% 0.12/0.37  # Proof object conjectures             : 22
% 0.12/0.37  # Proof object clause conjectures      : 19
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 10
% 0.12/0.37  # Proof object initial formulas used   : 3
% 0.12/0.37  # Proof object generating inferences   : 7
% 0.12/0.37  # Proof object simplifying inferences  : 20
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 3
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 19
% 0.12/0.37  # Removed in clause preprocessing      : 0
% 0.12/0.37  # Initial clauses in saturation        : 19
% 0.12/0.37  # Processed clauses                    : 54
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 0
% 0.12/0.37  # ...remaining for further processing  : 54
% 0.12/0.37  # Other redundant clauses eliminated   : 5
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 8
% 0.12/0.37  # Generated clauses                    : 30
% 0.12/0.37  # ...of the previous two non-trivial   : 29
% 0.12/0.37  # Contextual simplify-reflections      : 1
% 0.12/0.37  # Paramodulations                      : 25
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 5
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
% 0.12/0.37  # Current number of processed clauses  : 22
% 0.12/0.37  #    Positive orientable unit clauses  : 8
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 1
% 0.12/0.37  #    Non-unit-clauses                  : 13
% 0.12/0.37  # Current number of unprocessed clauses: 5
% 0.12/0.37  # ...number of literals in the above   : 33
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 27
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 34
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 9
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 1
% 0.12/0.37  # Unit Clause-clause subsumption calls : 8
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 1
% 0.12/0.37  # BW rewrite match successes           : 1
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 2417
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.029 s
% 0.12/0.37  # System time              : 0.004 s
% 0.12/0.37  # Total time               : 0.034 s
% 0.12/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
