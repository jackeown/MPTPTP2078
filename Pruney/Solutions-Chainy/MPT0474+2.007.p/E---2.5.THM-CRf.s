%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:49:22 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 157 expanded)
%              Number of clauses        :   23 (  80 expanded)
%              Number of leaves         :    7 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :  112 ( 764 expanded)
%              Number of equality atoms :   30 ( 227 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(fc7_relat_1,axiom,(
    ! [X1,X2,X3,X4] : v1_relat_1(k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_relat_1)).

fof(d7_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( X2 = k4_relat_1(X1)
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> r2_hidden(k4_tarski(X4,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_relat_1)).

fof(t66_relat_1,conjecture,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_relat_1)).

fof(c_0_7,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X14,X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X17)
        | X18 = k4_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k4_xboole_0(X16,X17) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X17)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k4_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_8,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_9,plain,(
    ! [X21] : k4_xboole_0(X21,k1_xboole_0) = X21 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_10,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_11,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_13,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | r2_hidden(esk2_3(X1,X2,k1_xboole_0),X1)
    | ~ r2_hidden(esk2_3(X1,X2,k1_xboole_0),X3) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_15,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | r2_hidden(esk2_3(X1,X2,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_13])).

fof(c_0_17,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X26)
      | ~ m1_subset_1(X27,k1_zfmisc_1(X26))
      | v1_relat_1(X27) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_18,plain,(
    ! [X22] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X22)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0
    | r2_hidden(esk2_3(X1,X1,k1_xboole_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,plain,(
    ! [X36,X37,X38,X39] : v1_relat_1(k2_tarski(k4_tarski(X36,X37),k4_tarski(X38,X39))) ),
    inference(variable_rename,[status(thm)],[fc7_relat_1])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0
    | ~ r2_hidden(esk2_3(X1,X1,k1_xboole_0),X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_19])).

fof(c_0_25,plain,(
    ! [X28,X29,X30,X31,X32,X33] :
      ( ( ~ r2_hidden(k4_tarski(X30,X31),X29)
        | r2_hidden(k4_tarski(X31,X30),X28)
        | X29 != k4_relat_1(X28)
        | ~ v1_relat_1(X29)
        | ~ v1_relat_1(X28) )
      & ( ~ r2_hidden(k4_tarski(X33,X32),X28)
        | r2_hidden(k4_tarski(X32,X33),X29)
        | X29 != k4_relat_1(X28)
        | ~ v1_relat_1(X29)
        | ~ v1_relat_1(X28) )
      & ( ~ r2_hidden(k4_tarski(esk3_2(X28,X29),esk4_2(X28,X29)),X29)
        | ~ r2_hidden(k4_tarski(esk4_2(X28,X29),esk3_2(X28,X29)),X28)
        | X29 = k4_relat_1(X28)
        | ~ v1_relat_1(X29)
        | ~ v1_relat_1(X28) )
      & ( r2_hidden(k4_tarski(esk3_2(X28,X29),esk4_2(X28,X29)),X29)
        | r2_hidden(k4_tarski(esk4_2(X28,X29),esk3_2(X28,X29)),X28)
        | X29 = k4_relat_1(X28)
        | ~ v1_relat_1(X29)
        | ~ v1_relat_1(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_relat_1])])])])])])).

cnf(c_0_26,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,plain,
    ( v1_relat_1(k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_19])).

fof(c_0_30,negated_conjecture,(
    k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t66_relat_1])).

cnf(c_0_31,plain,
    ( r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X2)
    | r2_hidden(k4_tarski(esk4_2(X1,X2),esk3_2(X1,X2)),X1)
    | X2 = k4_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_12])).

fof(c_0_34,negated_conjecture,(
    k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(fof_simplification,[status(thm)],[c_0_30])).

cnf(c_0_35,plain,
    ( k4_relat_1(X1) = k1_xboole_0
    | r2_hidden(k4_tarski(esk4_2(X1,k1_xboole_0),esk3_2(X1,k1_xboole_0)),X1)
    | ~ v1_relat_1(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_37,plain,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_32]),c_0_36]),c_0_33]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:52:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.13/0.39  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.028 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.13/0.39  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.13/0.39  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.13/0.39  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.13/0.39  fof(fc7_relat_1, axiom, ![X1, X2, X3, X4]:v1_relat_1(k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_relat_1)).
% 0.13/0.39  fof(d7_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(X2=k4_relat_1(X1)<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X2)<=>r2_hidden(k4_tarski(X4,X3),X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_relat_1)).
% 0.13/0.39  fof(t66_relat_1, conjecture, k4_relat_1(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_relat_1)).
% 0.13/0.39  fof(c_0_7, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X14,X11)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12))&(~r2_hidden(X14,X12)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12)))&(~r2_hidden(X15,X11)|r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k4_xboole_0(X11,X12)))&((~r2_hidden(esk2_3(X16,X17,X18),X18)|(~r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k4_xboole_0(X16,X17))&((r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))&(~r2_hidden(esk2_3(X16,X17,X18),X17)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.13/0.39  cnf(c_0_8, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.39  fof(c_0_9, plain, ![X21]:k4_xboole_0(X21,k1_xboole_0)=X21, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.13/0.39  cnf(c_0_10, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_8])).
% 0.13/0.39  cnf(c_0_11, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.39  cnf(c_0_12, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.13/0.39  cnf(c_0_13, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.39  cnf(c_0_14, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|r2_hidden(esk2_3(X1,X2,k1_xboole_0),X1)|~r2_hidden(esk2_3(X1,X2,k1_xboole_0),X3)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.13/0.39  cnf(c_0_15, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.39  cnf(c_0_16, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|r2_hidden(esk2_3(X1,X2,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_14, c_0_13])).
% 0.13/0.39  fof(c_0_17, plain, ![X26, X27]:(~v1_relat_1(X26)|(~m1_subset_1(X27,k1_zfmisc_1(X26))|v1_relat_1(X27))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.13/0.39  fof(c_0_18, plain, ![X22]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X22)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.13/0.39  cnf(c_0_19, plain, (k4_xboole_0(X1,X1)=k1_xboole_0|r2_hidden(esk2_3(X1,X1,k1_xboole_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.13/0.39  cnf(c_0_20, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.39  cnf(c_0_21, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.39  fof(c_0_22, plain, ![X36, X37, X38, X39]:v1_relat_1(k2_tarski(k4_tarski(X36,X37),k4_tarski(X38,X39))), inference(variable_rename,[status(thm)],[fc7_relat_1])).
% 0.13/0.39  cnf(c_0_23, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.39  cnf(c_0_24, plain, (k4_xboole_0(X1,X1)=k1_xboole_0|~r2_hidden(esk2_3(X1,X1,k1_xboole_0),X2)), inference(spm,[status(thm)],[c_0_12, c_0_19])).
% 0.13/0.39  fof(c_0_25, plain, ![X28, X29, X30, X31, X32, X33]:(((~r2_hidden(k4_tarski(X30,X31),X29)|r2_hidden(k4_tarski(X31,X30),X28)|X29!=k4_relat_1(X28)|~v1_relat_1(X29)|~v1_relat_1(X28))&(~r2_hidden(k4_tarski(X33,X32),X28)|r2_hidden(k4_tarski(X32,X33),X29)|X29!=k4_relat_1(X28)|~v1_relat_1(X29)|~v1_relat_1(X28)))&((~r2_hidden(k4_tarski(esk3_2(X28,X29),esk4_2(X28,X29)),X29)|~r2_hidden(k4_tarski(esk4_2(X28,X29),esk3_2(X28,X29)),X28)|X29=k4_relat_1(X28)|~v1_relat_1(X29)|~v1_relat_1(X28))&(r2_hidden(k4_tarski(esk3_2(X28,X29),esk4_2(X28,X29)),X29)|r2_hidden(k4_tarski(esk4_2(X28,X29),esk3_2(X28,X29)),X28)|X29=k4_relat_1(X28)|~v1_relat_1(X29)|~v1_relat_1(X28)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_relat_1])])])])])])).
% 0.13/0.39  cnf(c_0_26, plain, (v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.13/0.39  cnf(c_0_27, plain, (v1_relat_1(k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.39  cnf(c_0_28, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_23])).
% 0.13/0.39  cnf(c_0_29, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_24, c_0_19])).
% 0.13/0.39  fof(c_0_30, negated_conjecture, ~(k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(assume_negation,[status(cth)],[t66_relat_1])).
% 0.13/0.39  cnf(c_0_31, plain, (r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X2)|r2_hidden(k4_tarski(esk4_2(X1,X2),esk3_2(X1,X2)),X1)|X2=k4_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.39  cnf(c_0_32, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.13/0.39  cnf(c_0_33, plain, (~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_12])).
% 0.13/0.39  fof(c_0_34, negated_conjecture, k4_relat_1(k1_xboole_0)!=k1_xboole_0, inference(fof_simplification,[status(thm)],[c_0_30])).
% 0.13/0.39  cnf(c_0_35, plain, (k4_relat_1(X1)=k1_xboole_0|r2_hidden(k4_tarski(esk4_2(X1,k1_xboole_0),esk3_2(X1,k1_xboole_0)),X1)|~v1_relat_1(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])).
% 0.13/0.39  cnf(c_0_36, negated_conjecture, (k4_relat_1(k1_xboole_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.39  cnf(c_0_37, plain, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_32]), c_0_36]), c_0_33]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 38
% 0.13/0.39  # Proof object clause steps            : 23
% 0.13/0.39  # Proof object formula steps           : 15
% 0.13/0.39  # Proof object conjectures             : 4
% 0.13/0.39  # Proof object clause conjectures      : 1
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 10
% 0.13/0.39  # Proof object initial formulas used   : 7
% 0.13/0.39  # Proof object generating inferences   : 11
% 0.13/0.39  # Proof object simplifying inferences  : 6
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 10
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 20
% 0.13/0.39  # Removed in clause preprocessing      : 0
% 0.13/0.39  # Initial clauses in saturation        : 20
% 0.13/0.39  # Processed clauses                    : 124
% 0.13/0.39  # ...of these trivial                  : 3
% 0.13/0.39  # ...subsumed                          : 33
% 0.13/0.39  # ...remaining for further processing  : 88
% 0.13/0.39  # Other redundant clauses eliminated   : 5
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 5
% 0.13/0.39  # Backward-rewritten                   : 5
% 0.13/0.39  # Generated clauses                    : 206
% 0.13/0.39  # ...of the previous two non-trivial   : 143
% 0.13/0.39  # Contextual simplify-reflections      : 1
% 0.13/0.39  # Paramodulations                      : 199
% 0.13/0.39  # Factorizations                       : 2
% 0.13/0.39  # Equation resolutions                 : 5
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
% 0.13/0.39  # Current number of processed clauses  : 53
% 0.13/0.39  #    Positive orientable unit clauses  : 9
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 2
% 0.13/0.39  #    Non-unit-clauses                  : 42
% 0.13/0.39  # Current number of unprocessed clauses: 52
% 0.13/0.39  # ...number of literals in the above   : 162
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 30
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 541
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 246
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 27
% 0.13/0.39  # Unit Clause-clause subsumption calls : 15
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 15
% 0.13/0.39  # BW rewrite match successes           : 3
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 4204
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.032 s
% 0.13/0.39  # System time              : 0.005 s
% 0.13/0.39  # Total time               : 0.038 s
% 0.13/0.39  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
