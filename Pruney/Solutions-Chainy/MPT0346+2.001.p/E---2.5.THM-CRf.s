%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:11 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 415 expanded)
%              Number of clauses        :   38 ( 181 expanded)
%              Number of leaves         :    6 ( 100 expanded)
%              Depth                    :   14
%              Number of atoms          :  178 (2425 expanded)
%              Number of equality atoms :   30 ( 338 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t16_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ! [X4] :
              ( m1_subset_1(X4,k1_zfmisc_1(X1))
             => ( ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( r2_hidden(X5,X2)
                    <=> ( r2_hidden(X5,X3)
                        & r2_hidden(X5,X4) ) ) )
               => X2 = k9_subset_1(X1,X3,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_subset_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ! [X4] :
                ( m1_subset_1(X4,k1_zfmisc_1(X1))
               => ( ! [X5] :
                      ( m1_subset_1(X5,X1)
                     => ( r2_hidden(X5,X2)
                      <=> ( r2_hidden(X5,X3)
                          & r2_hidden(X5,X4) ) ) )
                 => X2 = k9_subset_1(X1,X3,X4) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t16_subset_1])).

fof(c_0_7,plain,(
    ! [X19,X20] :
      ( ( ~ m1_subset_1(X20,X19)
        | r2_hidden(X20,X19)
        | v1_xboole_0(X19) )
      & ( ~ r2_hidden(X20,X19)
        | m1_subset_1(X20,X19)
        | v1_xboole_0(X19) )
      & ( ~ m1_subset_1(X20,X19)
        | v1_xboole_0(X20)
        | ~ v1_xboole_0(X19) )
      & ( ~ v1_xboole_0(X20)
        | m1_subset_1(X20,X19)
        | ~ v1_xboole_0(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_8,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_xboole_0(X6)
        | ~ r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_xboole_0(X8) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_9,plain,(
    ! [X21,X22,X23] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(X21))
      | ~ r2_hidden(X23,X22)
      | r2_hidden(X23,X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

fof(c_0_10,negated_conjecture,(
    ! [X31] :
      ( m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))
      & m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))
      & m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0))
      & ( r2_hidden(X31,esk5_0)
        | ~ r2_hidden(X31,esk4_0)
        | ~ m1_subset_1(X31,esk3_0) )
      & ( r2_hidden(X31,esk6_0)
        | ~ r2_hidden(X31,esk4_0)
        | ~ m1_subset_1(X31,esk3_0) )
      & ( ~ r2_hidden(X31,esk5_0)
        | ~ r2_hidden(X31,esk6_0)
        | r2_hidden(X31,esk4_0)
        | ~ m1_subset_1(X31,esk3_0) )
      & esk4_0 != k9_subset_1(esk3_0,esk5_0,esk6_0) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])])).

cnf(c_0_11,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk6_0)
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_18,plain,(
    ! [X10,X11,X12,X13,X14,X15,X16,X17] :
      ( ( r2_hidden(X13,X10)
        | ~ r2_hidden(X13,X12)
        | X12 != k3_xboole_0(X10,X11) )
      & ( r2_hidden(X13,X11)
        | ~ r2_hidden(X13,X12)
        | X12 != k3_xboole_0(X10,X11) )
      & ( ~ r2_hidden(X14,X10)
        | ~ r2_hidden(X14,X11)
        | r2_hidden(X14,X12)
        | X12 != k3_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk2_3(X15,X16,X17),X17)
        | ~ r2_hidden(esk2_3(X15,X16,X17),X15)
        | ~ r2_hidden(esk2_3(X15,X16,X17),X16)
        | X17 = k3_xboole_0(X15,X16) )
      & ( r2_hidden(esk2_3(X15,X16,X17),X15)
        | r2_hidden(esk2_3(X15,X16,X17),X17)
        | X17 = k3_xboole_0(X15,X16) )
      & ( r2_hidden(esk2_3(X15,X16,X17),X16)
        | r2_hidden(esk2_3(X15,X16,X17),X17)
        | X17 = k3_xboole_0(X15,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])).

cnf(c_0_20,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( X1 = k3_xboole_0(esk6_0,X2)
    | r2_hidden(esk2_3(esk6_0,X2,X1),esk4_0)
    | r2_hidden(esk2_3(esk6_0,X2,X1),X1)
    | ~ r2_hidden(esk2_3(esk6_0,X2,X1),esk5_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_22,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( X1 = k3_xboole_0(esk6_0,esk5_0)
    | r2_hidden(esk2_3(esk6_0,esk5_0,X1),esk4_0)
    | r2_hidden(esk2_3(esk6_0,esk5_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_24,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( k3_xboole_0(esk6_0,esk5_0) = esk4_0
    | r2_hidden(esk2_3(esk6_0,esk5_0,esk4_0),esk4_0) ),
    inference(ef,[status(thm)],[c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_28,negated_conjecture,
    ( k3_xboole_0(esk6_0,esk5_0) = esk4_0
    | ~ r2_hidden(esk2_3(esk6_0,esk5_0,esk4_0),esk5_0)
    | ~ r2_hidden(esk2_3(esk6_0,esk5_0,esk4_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_16])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_33,plain,(
    ! [X24,X25,X26] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(X24))
      | k9_subset_1(X24,X25,X26) = k3_xboole_0(X25,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_34,negated_conjecture,
    ( k3_xboole_0(esk6_0,esk5_0) = esk4_0
    | ~ r2_hidden(esk2_3(esk6_0,esk5_0,esk4_0),esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_25])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_16])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( X1 = k3_xboole_0(X2,esk6_0)
    | r2_hidden(esk2_3(X2,esk6_0,X1),esk4_0)
    | r2_hidden(esk2_3(X2,esk6_0,X1),X1)
    | ~ r2_hidden(esk2_3(X2,esk6_0,X1),esk5_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_22])).

cnf(c_0_38,negated_conjecture,
    ( esk4_0 != k9_subset_1(esk3_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_39,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_41,negated_conjecture,
    ( k3_xboole_0(esk6_0,esk5_0) = esk4_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_25])).

cnf(c_0_42,negated_conjecture,
    ( X1 = k3_xboole_0(esk5_0,esk6_0)
    | r2_hidden(esk2_3(esk5_0,esk6_0,X1),esk4_0)
    | r2_hidden(esk2_3(esk5_0,esk6_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_20])).

cnf(c_0_43,negated_conjecture,
    ( k3_xboole_0(esk5_0,esk6_0) != esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_14])])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | X2 != esk4_0
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk2_3(esk5_0,esk6_0,esk4_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(ef,[status(thm)],[c_0_42]),c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | X2 != esk4_0
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk2_3(esk5_0,esk6_0,esk4_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk2_3(esk5_0,esk6_0,esk4_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_46]),c_0_43]),c_0_48]),c_0_49])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:13:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.55  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.20/0.55  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.55  #
% 0.20/0.55  # Preprocessing time       : 0.041 s
% 0.20/0.55  # Presaturation interreduction done
% 0.20/0.55  
% 0.20/0.55  # Proof found!
% 0.20/0.55  # SZS status Theorem
% 0.20/0.55  # SZS output start CNFRefutation
% 0.20/0.55  fof(t16_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>(![X5]:(m1_subset_1(X5,X1)=>(r2_hidden(X5,X2)<=>(r2_hidden(X5,X3)&r2_hidden(X5,X4))))=>X2=k9_subset_1(X1,X3,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_subset_1)).
% 0.20/0.55  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.20/0.55  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.55  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.20/0.55  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.20/0.55  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.20/0.55  fof(c_0_6, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>(![X5]:(m1_subset_1(X5,X1)=>(r2_hidden(X5,X2)<=>(r2_hidden(X5,X3)&r2_hidden(X5,X4))))=>X2=k9_subset_1(X1,X3,X4)))))), inference(assume_negation,[status(cth)],[t16_subset_1])).
% 0.20/0.55  fof(c_0_7, plain, ![X19, X20]:(((~m1_subset_1(X20,X19)|r2_hidden(X20,X19)|v1_xboole_0(X19))&(~r2_hidden(X20,X19)|m1_subset_1(X20,X19)|v1_xboole_0(X19)))&((~m1_subset_1(X20,X19)|v1_xboole_0(X20)|~v1_xboole_0(X19))&(~v1_xboole_0(X20)|m1_subset_1(X20,X19)|~v1_xboole_0(X19)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.20/0.55  fof(c_0_8, plain, ![X6, X7, X8]:((~v1_xboole_0(X6)|~r2_hidden(X7,X6))&(r2_hidden(esk1_1(X8),X8)|v1_xboole_0(X8))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.55  fof(c_0_9, plain, ![X21, X22, X23]:(~m1_subset_1(X22,k1_zfmisc_1(X21))|(~r2_hidden(X23,X22)|r2_hidden(X23,X21))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.20/0.55  fof(c_0_10, negated_conjecture, ![X31]:(m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))&(m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))&(m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0))&((((r2_hidden(X31,esk5_0)|~r2_hidden(X31,esk4_0)|~m1_subset_1(X31,esk3_0))&(r2_hidden(X31,esk6_0)|~r2_hidden(X31,esk4_0)|~m1_subset_1(X31,esk3_0)))&(~r2_hidden(X31,esk5_0)|~r2_hidden(X31,esk6_0)|r2_hidden(X31,esk4_0)|~m1_subset_1(X31,esk3_0)))&esk4_0!=k9_subset_1(esk3_0,esk5_0,esk6_0))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])])).
% 0.20/0.55  cnf(c_0_11, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.55  cnf(c_0_12, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.55  cnf(c_0_13, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.55  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.55  cnf(c_0_15, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk6_0)|~m1_subset_1(X1,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.55  cnf(c_0_16, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_11, c_0_12])).
% 0.20/0.55  cnf(c_0_17, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.20/0.55  fof(c_0_18, plain, ![X10, X11, X12, X13, X14, X15, X16, X17]:((((r2_hidden(X13,X10)|~r2_hidden(X13,X12)|X12!=k3_xboole_0(X10,X11))&(r2_hidden(X13,X11)|~r2_hidden(X13,X12)|X12!=k3_xboole_0(X10,X11)))&(~r2_hidden(X14,X10)|~r2_hidden(X14,X11)|r2_hidden(X14,X12)|X12!=k3_xboole_0(X10,X11)))&((~r2_hidden(esk2_3(X15,X16,X17),X17)|(~r2_hidden(esk2_3(X15,X16,X17),X15)|~r2_hidden(esk2_3(X15,X16,X17),X16))|X17=k3_xboole_0(X15,X16))&((r2_hidden(esk2_3(X15,X16,X17),X15)|r2_hidden(esk2_3(X15,X16,X17),X17)|X17=k3_xboole_0(X15,X16))&(r2_hidden(esk2_3(X15,X16,X17),X16)|r2_hidden(esk2_3(X15,X16,X17),X17)|X17=k3_xboole_0(X15,X16))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.20/0.55  cnf(c_0_19, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])).
% 0.20/0.55  cnf(c_0_20, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.55  cnf(c_0_21, negated_conjecture, (X1=k3_xboole_0(esk6_0,X2)|r2_hidden(esk2_3(esk6_0,X2,X1),esk4_0)|r2_hidden(esk2_3(esk6_0,X2,X1),X1)|~r2_hidden(esk2_3(esk6_0,X2,X1),esk5_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.55  cnf(c_0_22, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.55  cnf(c_0_23, negated_conjecture, (X1=k3_xboole_0(esk6_0,esk5_0)|r2_hidden(esk2_3(esk6_0,esk5_0,X1),esk4_0)|r2_hidden(esk2_3(esk6_0,esk5_0,X1),X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.55  cnf(c_0_24, plain, (X3=k3_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X1)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.55  cnf(c_0_25, negated_conjecture, (k3_xboole_0(esk6_0,esk5_0)=esk4_0|r2_hidden(esk2_3(esk6_0,esk5_0,esk4_0),esk4_0)), inference(ef,[status(thm)],[c_0_23])).
% 0.20/0.55  cnf(c_0_26, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_hidden(X1,esk4_0)|~m1_subset_1(X1,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.55  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.55  cnf(c_0_28, negated_conjecture, (k3_xboole_0(esk6_0,esk5_0)=esk4_0|~r2_hidden(esk2_3(esk6_0,esk5_0,esk4_0),esk5_0)|~r2_hidden(esk2_3(esk6_0,esk5_0,esk4_0),esk6_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.55  cnf(c_0_29, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_26, c_0_16])).
% 0.20/0.55  cnf(c_0_30, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_13, c_0_27])).
% 0.20/0.55  cnf(c_0_31, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk4_0)|~m1_subset_1(X1,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.55  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.55  fof(c_0_33, plain, ![X24, X25, X26]:(~m1_subset_1(X26,k1_zfmisc_1(X24))|k9_subset_1(X24,X25,X26)=k3_xboole_0(X25,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.20/0.55  cnf(c_0_34, negated_conjecture, (k3_xboole_0(esk6_0,esk5_0)=esk4_0|~r2_hidden(esk2_3(esk6_0,esk5_0,esk4_0),esk5_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_25])).
% 0.20/0.55  cnf(c_0_35, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_31, c_0_16])).
% 0.20/0.55  cnf(c_0_36, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_13, c_0_32])).
% 0.20/0.55  cnf(c_0_37, negated_conjecture, (X1=k3_xboole_0(X2,esk6_0)|r2_hidden(esk2_3(X2,esk6_0,X1),esk4_0)|r2_hidden(esk2_3(X2,esk6_0,X1),X1)|~r2_hidden(esk2_3(X2,esk6_0,X1),esk5_0)), inference(spm,[status(thm)],[c_0_19, c_0_22])).
% 0.20/0.55  cnf(c_0_38, negated_conjecture, (esk4_0!=k9_subset_1(esk3_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.55  cnf(c_0_39, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.55  cnf(c_0_40, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.55  cnf(c_0_41, negated_conjecture, (k3_xboole_0(esk6_0,esk5_0)=esk4_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36]), c_0_25])).
% 0.20/0.55  cnf(c_0_42, negated_conjecture, (X1=k3_xboole_0(esk5_0,esk6_0)|r2_hidden(esk2_3(esk5_0,esk6_0,X1),esk4_0)|r2_hidden(esk2_3(esk5_0,esk6_0,X1),X1)), inference(spm,[status(thm)],[c_0_37, c_0_20])).
% 0.20/0.55  cnf(c_0_43, negated_conjecture, (k3_xboole_0(esk5_0,esk6_0)!=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_14])])).
% 0.20/0.55  cnf(c_0_44, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.55  cnf(c_0_45, negated_conjecture, (r2_hidden(X1,esk6_0)|X2!=esk4_0|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.55  cnf(c_0_46, negated_conjecture, (r2_hidden(esk2_3(esk5_0,esk6_0,esk4_0),esk4_0)), inference(sr,[status(thm)],[inference(ef,[status(thm)],[c_0_42]), c_0_43])).
% 0.20/0.55  cnf(c_0_47, negated_conjecture, (r2_hidden(X1,esk5_0)|X2!=esk4_0|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_44, c_0_41])).
% 0.20/0.55  cnf(c_0_48, negated_conjecture, (r2_hidden(esk2_3(esk5_0,esk6_0,esk4_0),esk6_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.55  cnf(c_0_49, negated_conjecture, (r2_hidden(esk2_3(esk5_0,esk6_0,esk4_0),esk5_0)), inference(spm,[status(thm)],[c_0_47, c_0_46])).
% 0.20/0.55  cnf(c_0_50, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_46]), c_0_43]), c_0_48]), c_0_49])]), ['proof']).
% 0.20/0.55  # SZS output end CNFRefutation
% 0.20/0.55  # Proof object total steps             : 51
% 0.20/0.55  # Proof object clause steps            : 38
% 0.20/0.55  # Proof object formula steps           : 13
% 0.20/0.55  # Proof object conjectures             : 31
% 0.20/0.55  # Proof object clause conjectures      : 28
% 0.20/0.55  # Proof object formula conjectures     : 3
% 0.20/0.55  # Proof object initial clauses used    : 16
% 0.20/0.55  # Proof object initial formulas used   : 6
% 0.20/0.55  # Proof object generating inferences   : 21
% 0.20/0.55  # Proof object simplifying inferences  : 13
% 0.20/0.55  # Training examples: 0 positive, 0 negative
% 0.20/0.55  # Parsed axioms                        : 6
% 0.20/0.55  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.55  # Initial clauses                      : 21
% 0.20/0.55  # Removed in clause preprocessing      : 0
% 0.20/0.55  # Initial clauses in saturation        : 21
% 0.20/0.55  # Processed clauses                    : 2065
% 0.20/0.55  # ...of these trivial                  : 76
% 0.20/0.55  # ...subsumed                          : 1586
% 0.20/0.55  # ...remaining for further processing  : 402
% 0.20/0.55  # Other redundant clauses eliminated   : 27
% 0.20/0.55  # Clauses deleted for lack of memory   : 0
% 0.20/0.55  # Backward-subsumed                    : 13
% 0.20/0.55  # Backward-rewritten                   : 5
% 0.20/0.55  # Generated clauses                    : 6862
% 0.20/0.55  # ...of the previous two non-trivial   : 6469
% 0.20/0.55  # Contextual simplify-reflections      : 30
% 0.20/0.55  # Paramodulations                      : 6728
% 0.20/0.55  # Factorizations                       : 82
% 0.20/0.55  # Equation resolutions                 : 46
% 0.20/0.55  # Propositional unsat checks           : 0
% 0.20/0.55  #    Propositional check models        : 0
% 0.20/0.55  #    Propositional check unsatisfiable : 0
% 0.20/0.55  #    Propositional clauses             : 0
% 0.20/0.55  #    Propositional clauses after purity: 0
% 0.20/0.55  #    Propositional unsat core size     : 0
% 0.20/0.55  #    Propositional preprocessing time  : 0.000
% 0.20/0.55  #    Propositional encoding time       : 0.000
% 0.20/0.55  #    Propositional solver time         : 0.000
% 0.20/0.55  #    Success case prop preproc time    : 0.000
% 0.20/0.55  #    Success case prop encoding time   : 0.000
% 0.20/0.55  #    Success case prop solver time     : 0.000
% 0.20/0.55  # Current number of processed clauses  : 357
% 0.20/0.55  #    Positive orientable unit clauses  : 32
% 0.20/0.55  #    Positive unorientable unit clauses: 0
% 0.20/0.55  #    Negative unit clauses             : 7
% 0.20/0.55  #    Non-unit-clauses                  : 318
% 0.20/0.55  # Current number of unprocessed clauses: 4433
% 0.20/0.55  # ...number of literals in the above   : 18025
% 0.20/0.55  # Current number of archived formulas  : 0
% 0.20/0.55  # Current number of archived clauses   : 45
% 0.20/0.55  # Clause-clause subsumption calls (NU) : 14533
% 0.20/0.55  # Rec. Clause-clause subsumption calls : 10967
% 0.20/0.55  # Non-unit clause-clause subsumptions  : 882
% 0.20/0.55  # Unit Clause-clause subsumption calls : 1559
% 0.20/0.55  # Rewrite failures with RHS unbound    : 0
% 0.20/0.55  # BW rewrite match attempts            : 44
% 0.20/0.55  # BW rewrite match successes           : 2
% 0.20/0.55  # Condensation attempts                : 0
% 0.20/0.55  # Condensation successes               : 0
% 0.20/0.55  # Termbank termtop insertions          : 98314
% 0.20/0.55  
% 0.20/0.55  # -------------------------------------------------
% 0.20/0.55  # User time                : 0.195 s
% 0.20/0.55  # System time              : 0.009 s
% 0.20/0.55  # Total time               : 0.204 s
% 0.20/0.55  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
